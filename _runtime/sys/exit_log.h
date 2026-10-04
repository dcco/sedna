#ifndef EXIT_LOG_H
#define EXIT_LOG_H

#include <time.h>

void exit_log(const char *s, const char *z) {
	FILE* file;
	file = fopen("err.log", "a");
	if (file == NULL) exit(1);

	time_t tm = time(NULL);
	fprintf(file, "%s: ", ctime(&tm));
	fprintf(file, s, z);
	fprintf(file, "\n");
	fclose(file);
	exit(1);
}

#endif /* EXIT_LOG_H */