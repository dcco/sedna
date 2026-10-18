#ifndef OS_H
#define OS_H
	
	/*
		basic functions
	*/


extern float _Float_builtin_expo(float f, float z) {
	return powf(f, z);
}

extern float _Float_builtin_sqrt(float f) {
	return sqrtf(f);
}

extern float _Float_builtin_ln(float f) {
	return logf(f);
}

extern uint32_t _Int_builtin_abs(uint32_t f) {
	return abs(f);
}

extern float _Float_builtin_abs(float f) {
	return fabsf(f);
}

extern int32_t _Float_builtin_floor(float f) {
	return (int32_t) floorf(f);
}

extern int32_t _Float_builtin_ceil(float f) {
	return (int32_t) ceilf(f);
}

extern float _Float_builtin_sin(float f) {
	return sin(f);
}

extern float _Float_builtin_cos(float f) {
	return cos(f);
}

extern float _Int_builtin_toRadians(int32_t i) {
	return ((float) i) * M_PI / 180.0f;
}

extern uint32_t _U8_builtin_color(uint8_t r, uint8_t g, uint8_t b) {
	return ((uint32_t) r) << 16 | ((uint32_t) g) << 8 | ((uint32_t) b);
}

extern uint32_t _U32_builtin_rgb(uint32_t c) {
	return c >> 8;
}

extern void array_grow(gc_array_t* arr) {
	arr->size = arr->size + 1;
	if (arr->size >= arr->capacity) {
		int32_t newCap = arr->capacity * 3 / 2;
		arr->capacity = newCap;
		arr->data = realloc(arr->data, arr->elemSize * newCap);
	}
}

extern void array_grow_n(gc_array_t* arr, int32_t n) {
	arr->size = arr->size + n;
	if (arr->size >= arr->capacity) {
		int32_t newCap = arr->capacity * 3 / 2;
		arr->capacity = newCap;
		arr->data = realloc(arr->data, arr->elemSize * newCap);
	}
}

extern void _a1_builtin_remove(gc_array_t* arr, int32_t i) {
	if (i < 0 || i >= arr->size) exit_log("Out of bounds exception on array removal.", "");
	if (i != arr->size - 1) {
		int8_t* rawData = (int8_t*) arr->data;
		memcpy(rawData + (i * arr->elemSize), rawData + ((arr->size - 1) * arr->elemSize), arr->elemSize);  
	}
	// downsize if necessary
	arr->size = arr->size - 1;
	if (arr->capacity > 32 && arr->size <= arr->capacity / 2) {
		int32_t newCap = arr->capacity * 3 / 4;
		arr->capacity = newCap;
		arr->data = realloc(arr->data, arr->elemSize * newCap);
	}
}

extern void _a1_builtin_flush(gc_array_t* arr) {
	arr->size = 0;
}

extern void _a1_builtin_clear(gc_array_t* arr) {
	int32_t arrCap = 16;
	arr->capacity = arrCap;
	free(arr->data);
	arr->data = malloc(arr->elemSize * arrCap);
	arr->size = 0;
}

extern void* _a1_builtin_toCPtr(gc_array_t* arr) {
	return arr->data;
}

extern void* _a1_builtin_toRawPtr(gc_array_t* arr) {
	return arr->data;
}

extern void _a1_builtin_addFloat(gc_array_t* arr, float f) {
	int32_t i = arr->size;
	array_grow_n(arr, 4);
	float* fPtr = (float*) (((int8_t*) arr->data) + i);
	*fPtr = f;
}

extern void _a1_builtin_addU32(gc_array_t* arr, uint32_t n) {
	int32_t i = arr->size;
	array_grow_n(arr, 4);
	uint32_t* nPtr = (uint32_t*) (((int8_t*) arr->data) + i);
	*nPtr = n;
}

extern void _a1_builtin_addI32(gc_array_t* arr, int32_t n) {
	int32_t i = arr->size;
	array_grow_n(arr, 4);
	int32_t* nPtr = (int32_t*) (((int8_t*) arr->data) + i);
	*nPtr = n;
}

extern void* _any_builtin_cAlloc(int64_t size, int32_t i) {
	return malloc(size * i);
}

	/*
		os - console / printing functions
	*/

extern void _String_Sys_Os_print(void* _s) {
	dusk_string_t* s = (dusk_string_t*) _s;
	printf("%s\n", &s->start);
}

extern void _ptr_Sys_Os_print(uint8_t* s) {
	printf("%s\n", s);
}

extern void _String_builtin_panic(void* _s) {
	dusk_string_t* s = (dusk_string_t*) _s;
	exit_log(&s->start, "");
}

	/*
		os - randomization
	*/

extern int32_t _Int_Sys_Os_randomInt(int32_t i) {
	return rand() % i;
}

extern float _none_Sys_Os_randomFloat() {
	return ((float) rand()) / ((float) RAND_MAX);
}

	/*
		os - prng object
	*/

extern xoshiro_state_t* _Int_Sys_Os_newPRNG(int32_t seed) {
	xoshiro_state_t* prng = (xoshiro_state_t*) gc_alloc(sizeof(xoshiro_state_t), NULL);
	xoshiro_seed(prng, (uint64_t) seed);
	return prng;
}

extern int32_t _PRNG_Sys_Os_randomInt(xoshiro_state_t* prng, int32_t i) {
	return (int32_t) (xoshiro_next(prng) % (uint64_t) i);
}
extern float _PRNG_Sys_Os_randomFloat(xoshiro_state_t* prng) {
	uint32_t bits = (uint32_t) (xoshiro_next(prng) >> 41) | 0x3F800000u; // exponent = 127
	float f = *((float*) &bits);
	return f - 1.0f; 
}

	/*
		os - time
	*/

extern uint64_t _none_Sys_Os_time() {
	return time_ns() / 1000000;
	//return 0;
	
}

extern uint64_t _none_Sys_Os_timeNS() {
	return time_ns();
}

#endif