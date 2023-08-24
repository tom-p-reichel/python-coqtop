#define _GNU_SOURCE
#include <stdio.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <stdint.h>

#ifdef MAKE_PUBLIC
#define MAYBE_STATIC
#else
#define MAYBE_STATIC static
#endif

typedef struct {
	struct random_data rd;
	char buf[128];
} prng;

MAYBE_STATIC void prng_init(prng* a) {
	initstate_r(42424,&a->buf,128,&a->rd);
}

MAYBE_STATIC int32_t prng_pull(prng* a) {
	int32_t out;
	random_r(&a->rd,&out);
	return out;
}

MAYBE_STATIC int prng_struct_size(){ 
	return sizeof(prng);
}

