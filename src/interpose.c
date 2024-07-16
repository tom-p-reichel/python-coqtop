#define _GNU_SOURCE
#include <stdio.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <stdint.h>

// this is extremely silly!
// but i do not want to create more
// non-static symbols in the interpose
// binary, so we opt to "copy paste"
// the static definitions, rather
// than link against them,
// which would invariably produce non-
// static symbols.
#include "random.c"

static prng random_gen;

static ssize_t (*real_read)(int fd, void *buf, size_t count) = NULL;

static size_t chunk = 0;

ssize_t read(int fd, void *buf, size_t count) {
	if (real_read==NULL) {
		real_read = dlsym(RTLD_NEXT,"read");
		prng_init(&random_gen);
	}
	if (fd!=STDIN_FILENO)
		return real_read(fd,buf,count);

	if (chunk==0) {
		int32_t syncno = prng_pull(&random_gen);
		dprintf(STDOUT_FILENO,"<%d>",syncno);
		dprintf(STDERR_FILENO,"<%d>",syncno);

		ssize_t out = real_read(fd,&chunk,sizeof(size_t));
		if (out<=0) {
			// nonblock or read error.
			// just propagate upwards.
			return out;
		}
		if (out!=sizeof(size_t)) {
			// this is possible but
			// EXTREMELY improbable.
			// someone sent us a signal
			// PARTWAY through reading about 4 bytes.
			// TODO: handle this if it ever occurs.
			dprintf(STDERR_FILENO,"Something incredibly improbable has occurred: see repltap interpose.c.  Dying.");
			exit(123);
		}
	}
	
	size_t new_count = (count > chunk) ? chunk : count;

	ssize_t out = real_read(fd,buf,new_count);

	if (out <= 0) {
		return out;
	}

	chunk -= out;

	return out;
}
