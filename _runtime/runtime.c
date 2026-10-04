#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#include <malloc.h>
#include <pthread.h>

#include "rc_constants.h"
#include "time_api.h"
#include "exit_log.h"
#include "gc.h"
#include "dusk_string.h"

#include "xoshiro.h"
#include "os.h"

	/* runtime hooks */

extern void _none_main();

	/* bootstrap main function */

int main(void) {
	gc_init();
	srand(time(NULL) ^ getpid());
	_none_main();
	return 0;
}