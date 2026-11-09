#ifndef IO_API_H
#define IO_API_H

void* _String_Sys_Os_fileOpen(void* _path, void* _mode) {
	dusk_string_t* path = (dusk_string_t*) _path;
	dusk_string_t* mode = (dusk_string_t*) _mode;
	
	return fopen(&path->start, &mode->start);
}

void _FileChannel_Sys_Os_close(void* fc) {
	fclose((FILE*) fc);
}

int32_t _FileChannel_Sys_Os_read(void* _fc, void* _buffer, int32_t size) {
	FILE* fc = (FILE*) _fc;
	gc_array_t* buffer = (gc_array_t*) _buffer;

	if (size < 0) size = 0;
	return (int32_t) fread(buffer->data, 1, size, fc);
}

int32_t _FileChannel_Sys_Os_write(void* _fc, void* _buffer, int32_t size) {
	FILE* fc = (FILE*) _fc;
	gc_array_t* buffer = (gc_array_t*) _buffer;

	if (size < 0) size = 0;
	return (int32_t) fwrite(buffer->data, 1, size, fc);
}

int32_t _FileChannel_Sys_Os_writeRaw(void* _fc, int8_t* buffer, int32_t size) {
	FILE* fc = (FILE*) _fc;

	if (size < 0) size = 0;
	return (int32_t) fwrite(buffer, 1, size, fc);
}

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

#endif