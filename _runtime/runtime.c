#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#include <malloc.h>
#include <pthread.h>
#include <time.h>
#include <sys/stat.h>

#include "rc_constants.h"
#include "time_api.h"
#include "exit_log.h"
#include "gc.h"
#include "dusk_string.h"

#include "xoshiro.h"
#include "os.h"
#include "io_api.h"

	/* runtime hooks */

extern void _none_main();

	/* bootstrap main function */

int main(void) {
	gc_init();
	srand(time(NULL) ^ getpid());
	_none_main();
	return 0;
}