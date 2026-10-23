#ifndef GC_H
#define GC_H

	/*
		GC parameters that can be tuned
		TODO: make max_roots manually settable
	*/

#define MAX_ROOTS 256
#define TIME_ALLOC_MS 850
#define PING_OBJ_TOTAL 50

	// gc constants

const int8_t GC_WHITE = 0;
const int8_t GC_GRAY = 1;
const int8_t GC_BLACK = 2;

const int8_t PHASE_NEW = 0;
const int8_t PHASE_MARK = 1;
const int8_t PHASE_SWEEP = 2;

const int8_t ARR_NO = 0;
const int8_t ARR_FLAT = 1;
const int8_t ARR_NEST = 2;

#define MAX_ALIGN_UP(size) (size + sizeof(max_align_t) - 1) & ~(sizeof(max_align_t) - 1)

	/*
		gc_type:
			defines the layout of the memory for the mark phase's pointer lookup.
	*/

typedef struct gc_type {
	int8_t total;
	int32_t* offsets; 
} gc_type_t;

	/*
		gc_obj:
			defined struct is followed by the actual allocated memory.
			program is given references to this. 
		- next: used to link all gc objects in a single list
		- type: type layout information used to traverse through sub-pointers
		- color: "color" used to mark the accessibility of a pointer
		- arrFlag: whether or not the object is an array/vector + whether it contains nested pointers
		~ followed by either raw data OR array/vector header
	*/

typedef struct gc_obj {
	struct gc_obj* next;
	gc_type_t* type;
	unsigned int color : 2;
	unsigned int arrFlag : 2;
} gc_obj_t;

const size_t GC_OBJ_SIZE = MAX_ALIGN_UP(sizeof(gc_obj_t));

	/*
		gc_array:
			defines a dynamically sized array
		- elemSize: the size of an individual element in the array
		- capacity: the current allocation for the array
		- size: the RAW number of elements in the array
		- data: a pointer to the raw data
		~ for tensors, followed by the array dimensions
	*/

typedef struct gc_array {
	int32_t elemSize;
	int32_t capacity;
	int32_t size;
	void* data;
} gc_array_t;

	/*
		garbage collector globals
	*/

static int32_t gc_phase = PHASE_NEW;

static gc_obj_t* gc_head = NULL;
static gc_obj_t* gc_prev_sweep = NULL;
static gc_obj_t* gc_sweep = NULL;

static gc_obj_t* gc_roots[MAX_ROOTS];
static int32_t gc_root_total = 0; 

	// debug variables
static int32_t gc_obj_total = 0;

	/*
		gray set definition / API
	*/

static gc_obj_t** gray_set = NULL;
static int32_t gray_cap = 1024;
static int32_t gray_total = 0;

void _gray_push(gc_obj_t* obj) {
	if (gray_total >= gray_cap) {
		gray_cap = (gray_cap * 3) / 2;
		gray_set = (gc_obj_t**) realloc(gray_set, sizeof(gc_obj_t*) * gray_cap);
	}
	gray_set[gray_total] = obj;
	gray_total = gray_total + 1;
}

gc_obj_t* _gray_pop() {
	if (gray_total == 0) return NULL;
	gray_total = gray_total - 1;
	return gray_set[gray_total];
}

	/*
		garbage collector API
	*/

extern void gc_init() {
	gray_set = (gc_obj_t**) malloc(sizeof(gc_obj_t*) * 1024);
}

inline static void* _gc_alloc(int32_t size, gc_type_t* type, int8_t arrFlag) {
	// initialize object
	gc_obj_t* obj = (gc_obj_t*) calloc(1, GC_OBJ_SIZE + size);
	obj->type = type;
	obj->color = GC_WHITE;
	obj->next = gc_head;
	obj->arrFlag = arrFlag;
	// update gc state
	gc_head = obj;
	gc_obj_total = gc_obj_total + 1;
	return (void*) (obj + 1);
}

extern void* gc_alloc(int32_t size, gc_type_t* type) {
	_gc_alloc(size, type, ARR_NO);
}

extern void* gc_alloc_array(int32_t elemSize, int32_t arrSize, int32_t exSize, int8_t nestFlag, gc_type_t* type) {
	// initialize gc object
	gc_array_t* array = (gc_array_t*) _gc_alloc(sizeof(gc_array_t) + exSize, type, nestFlag ? ARR_NEST : ARR_FLAT);
	// allocate raw data
	int32_t arrCap = 16;
	if (arrSize > arrCap) arrCap = arrSize;
	array->data = calloc(arrCap, elemSize);
	// initialize size information
	array->elemSize = elemSize;
	array->capacity = arrCap;
	array->size = arrSize;
	return (void*) array;
}

void* gc_free(gc_obj_t* obj) {
	// for array, free the dimension information
	if (obj->arrFlag) {
		gc_array_t* array = (gc_array_t*) (obj + 1);
		free(array->data);
	}
	// free the object
	free(obj);
	gc_obj_total = gc_obj_total - 1;
}

void* raw_alloc_1d_array(int32_t elemSize, int32_t arrSize) {
	gc_array_t* array = (gc_array_t*) malloc(sizeof(gc_array_t));
	array->data = malloc(elemSize * arrSize);
	array->elemSize = elemSize;
	array->capacity = arrSize;
	array->size = arrSize;
	return (void*) array;
}

void raw_free_array(gc_array_t* arr) {
	free(arr->data);
	free(arr);
}

extern void gc_new_root(void* ptr) {
	if (gc_root_total >= MAX_ROOTS) {
		exit_log("Root stack overflow.", "");
	}
	gc_roots[gc_root_total] = ((gc_obj_t*) ptr) - 1;
	gc_root_total = gc_root_total + 1;
}

void _gc_mark_elem(int8_t* data, gc_type_t* type) {
	for (int i = 0; i < type->total; i++) {
		// read sub-pointer, if not already gray, add to gray set
		int8_t* subPtr = data + type->offsets[i];
		gc_obj_t* subObj = *((gc_obj_t**) subPtr) - 1;
		if (subObj != NULL && subObj->color == GC_WHITE) {
			subObj->color = GC_GRAY;
			_gray_push(subObj);
		}
	}
}

	// assumes every pointer is directly to a gc obj
void _gc_mark_array_direct(gc_array_t* array) {
	gc_obj_t** data = (gc_obj_t**) array->data;
	for (int i = 0; i < array->size; i++) {
		gc_obj_t* subObj = data[i] - 1;
		if (subObj != NULL && subObj->color == GC_WHITE) {
			subObj->color = GC_GRAY;
			_gray_push(subObj);
		}
	}
}

	// goes through the list of offsets provided by the type
void _gc_mark_array_layout(gc_array_t* array, gc_type_t* type) {
	int8_t* data = (int8_t*) array->data;
	for (int i = 0; i < array->size; i++) {
		data = data + array->elemSize;
		_gc_mark_elem(data, type);
	}
}

void _gc_mark_obj(gc_obj_t* obj) {
	// mark as safe
	obj->color = GC_BLACK;
	// array (with nested pointers) case
	if (obj->arrFlag == ARR_NEST) {
		if (obj->type == NULL) _gc_mark_array_direct((gc_array_t*) (obj + 1));
		else _gc_mark_array_layout((gc_array_t*) (obj + 1), obj->type);
		return;
	} else if (obj->arrFlag == ARR_FLAT) return;
	// find raw ptr, use gc_type info to find each sub-pointer
	if (obj->type == NULL) return;
	_gc_mark_elem((int8_t*) (obj + 1), obj->type);
	/*gc_type_t* type = obj->type;
	if (type == NULL) return;
	int8_t* data = (int8_t*) (obj + 1);*/
}

void _gc_mark() {
	int mTotal = 0;
	// iterate through gray set objects
	gc_obj_t* nextObj = _gray_pop();
	while (nextObj != NULL) {
		_gc_mark_obj(nextObj);
		// every so often, check how much time has passed
		mTotal = mTotal + 1;
		if (mTotal == PING_OBJ_TOTAL) {
			mTotal = 0;
		}
		// move onto next object
		nextObj = _gray_pop();
	}
	// if completed gray set, prep for sweep phase
	gc_phase = PHASE_SWEEP;
	gc_sweep = gc_head;
	gc_prev_sweep = NULL;
}

void _gc_sweep() {
	// iterate through all objects
	while (gc_sweep != NULL) {
		// if white, free
		if (gc_sweep->color == GC_WHITE) {
			// connect previous obj (or stack head) to next object
			if (gc_prev_sweep == NULL) {
				gc_head = gc_sweep->next;
			} else {
				gc_prev_sweep->next = gc_sweep->next;
			}
			// move to next object, delete old object
			gc_obj_t* del_obj = gc_sweep;
			gc_sweep = gc_sweep->next;
			gc_free(del_obj);
		// otherwise, mark white and move on
		} else {
			gc_sweep->color = GC_WHITE;
			gc_prev_sweep = gc_sweep;
			gc_sweep = gc_sweep->next;
		}
	}
	// if completed sweep, prep for next iteration
	gc_phase = PHASE_NEW;
}

extern void gc_collect() {
	// add roots to gray set
	if (gc_phase == PHASE_NEW) {
		for (int i = 0; i < gc_root_total; i++) {
			_gray_push(gc_roots[i]);
		}
		gc_phase = PHASE_MARK;
	}
	// mark and sweep
	if (gc_phase == PHASE_MARK) _gc_mark();
	if (gc_phase == PHASE_SWEEP) _gc_sweep();
}

#endif