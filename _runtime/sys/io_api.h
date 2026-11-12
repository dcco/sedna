#ifndef IO_API_H
#define IO_API_H

	/*
		simple file API - "complete" for file manipulation, but for more detailed
			handling probably want an FFI implementation
	*/

	// - path-based file manipulations

int8_t _String_Sys_Os_fileExists(void* _path) {
	dusk_string_t* path = (dusk_string_t*) _path;
	struct stat st;
	return stat(&path->start, &st) == 0;
}

int8_t _String_Sys_Os_fileDelete(void* _path) {
	dusk_string_t* path = (dusk_string_t*) _path;
	return remove(&path->start);
}

int8_t _String_Sys_Os_fileRename(void* _oldPath, void* _newPath) {
	dusk_string_t* oldPath = (dusk_string_t*) _oldPath;
	dusk_string_t* newPath = (dusk_string_t*) _newPath;

	return rename(&oldPath->start, &newPath->start) == 0;
}

	// - file opening

void* _String_Sys_Os_newFileReader(void* _path) {
	dusk_string_t* path = (dusk_string_t*) _path;
	return fopen(&path->start, "r");
}

void* _String_Sys_Os_newFileWriter(void* _path, int8_t appendFlag) {
	dusk_string_t* path = (dusk_string_t*) _path;
	return fopen(&path->start, appendFlag ? "a" : "w");
}

void _FileReader_Sys_Os_close(void* fc) {
	fflush((FILE*) fc);
	fclose((FILE*) fc);
}

void _FileWriter_Sys_Os_close(void* fc) {
	fflush((FILE*) fc);
	fclose((FILE*) fc);
}

	// - file read

void* _FileReader_Sys_Os_read(void* _fc, int64_t elemSize, int32_t size) {
	FILE* fc = (FILE*) _fc;
	gc_array_t* buffer = gc_alloc_array(elemSize, size, 0, ARR_FLAT, NULL);
	fread(buffer->data, 1, elemSize * size, fc);
	if (ferror(fc)) exit_log("Unhandled file reader error.", "");
	return buffer;
}

int8_t _FileReader_Sys_Os_readByte(void* _fc) {
	FILE* fc = (FILE*) _fc;
	int8_t b;
	fread(&b, 1, 1, fc);
	if (ferror(fc)) exit_log("Unhandled file reader error.", "");
	return b;
}

int32_t _FileReader_Sys_Os_readInt(void* _fc) {
	FILE* fc = (FILE*) _fc;
	int32_t i;
	fread(&i, 1, 4, fc);
	if (ferror(fc)) exit_log("Unhandled file reader error.", "");
	return i;
}

	// - file write

void _FileWriter_Sys_Os_write(void* _fc, void* _buffer) {
	FILE* fc = (FILE*) _fc;
	gc_array_t* buffer = (gc_array_t*) _buffer;
	int64_t size = buffer->elemSize * buffer->size;
	fwrite(buffer->data, 1, size, fc);
}

void _FileWriter_Sys_Os_writeByte(void* _fc, int8_t b) {
	FILE* fc = (FILE*) _fc;
	fwrite(&b, 1, 1, fc);
}

void _FileWriter_Sys_Os_writeInt(void* _fc, int32_t i) {
	FILE* fc = (FILE*) _fc;
	fwrite(&i, 1, 4, fc);
}

void _FileWriter_Sys_Os_writeString(void* _fc, void* _s) {
	FILE* fc = (FILE*) _fc;
	dusk_string_t* s = (dusk_string_t*) _s;
	fwrite(&s->start, 1, s->len, fc);
}

	// - file position ops

int8_t _FileReader_Sys_Os_seek(void* _fc, int32_t i) {
	return fseek((FILE*) _fc, i, SEEK_CUR) != 0;
}

int8_t _FileReader_Sys_Os_eof(void* _fc) {
	return feof((FILE*) _fc);
}

/*
int32_t _FileChannel_Sys_Os_writeRaw(void* _fc, int8_t* buffer, int32_t size) {
	FILE* fc = (FILE*) _fc;

	if (size < 0) size = 0;
	return (int32_t) fwrite(buffer, 1, size, fc);
}*/

#endif