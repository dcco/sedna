#ifndef JAS_STRING_H
#define JAS_STRING_H

	/*
		dusk_string:
		- len: number of characters in the string
		- start: a single character representing the "start" of the string
			(this field exists so that we have a predictable offset for creating string constants in LLVM)
		~ followed by remainder of character data
	*/

typedef struct dusk_string {
	int32_t len;
	char start;
} dusk_string_t;

	/*
		basic string functions
	*/

static dusk_string_t* _newString(int32_t len) {
	dusk_string_t* s = (dusk_string_t*) gc_alloc(sizeof(dusk_string_t) + sizeof(char) * (len + 1), NULL);
	s->len = len;
	return s;
}

extern void* _String_builtin_add(void* _s1, void* _s2) {
	dusk_string_t* s1 = (dusk_string_t*) _s1;
	dusk_string_t* s2 = (dusk_string_t*) _s2;
	int len = s1->len + s2->len;
	dusk_string_t* sx = _newString(len);
	char* data = &sx->start;
	memcpy(data, &s1->start, sizeof(char) * s1->len);
	memcpy(data + s1->len, &s2->start, sizeof(char) * s2->len);
	data[len] = 0;
	return sx;
}

extern int32_t _String_builtin_measure(void* s) {
	return ((dusk_string_t*) s)->len;
}

	/*
		string conversion functions
	*/

extern void* _Int_builtin_toString(int32_t i) {
	int length = snprintf(NULL, 0, "%d", i);
	dusk_string_t* s = _newString(length);
	snprintf(&s->start, length + 1, "%d", i);
	return (void*) s;
}

extern void* _Float_builtin_toString(float f) {
	int length = snprintf(NULL, 0, "%f", f);
	dusk_string_t* s = _newString(length);
	snprintf(&s->start, length + 1, "%f", f);
	return (void*) s;
}

extern char* _String_builtin_cString(void* s) {
	return &((dusk_string_t*) s)->start;
}

extern void* _ptr_builtin_toString(uint8_t* src) {
	int32_t length = strlen(src);
	dusk_string_t* dst = _newString(length);
	memcpy(&dst->start, src, length + 1);
	return (void*) dst;
}

#endif