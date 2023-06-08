#define _GNU_SOURCE
#include <stdio.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <stdint.h>

static ssize_t (*real_read)(int fd, void *buf, size_t count) = NULL;

static struct random_data random_state = {.state=NULL};

static char random_buf[128] = {0};

ssize_t read(int fd, void *buf, size_t count) {
	if (real_read==NULL) {
		real_read = dlsym(RTLD_NEXT,"read");
		initstate_r(42424,random_buf,128,&random_state);
	}
	int32_t syncno;
	if (fd==STDIN_FILENO) {
		random_r(&random_state,&syncno);
		dprintf(STDOUT_FILENO,"<%d|",syncno);
		dprintf(STDERR_FILENO,"<%d>\n",syncno);
	}
	ssize_t out = real_read(fd,buf,count);
	if (fd==STDIN_FILENO) {
		dprintf(STDOUT_FILENO,"%zd>\n",out);
	}
	return out;
}
