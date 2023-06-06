#define _GNU_SOURCE
#include <stdio.h>
#include <unistd.h>
#include <dlfcn.h>

static ssize_t (*real_read)(int fd, void *buf, size_t count) = NULL;

static size_t number_reads = 0;

ssize_t read(int fd, void *buf, size_t count) {
	if (real_read==NULL) {
		real_read = dlsym(RTLD_NEXT,"read");
	}
	if (fd==STDIN_FILENO) {
		dprintf(STDOUT_FILENO,"<read sync %zu>\n",number_reads);
		dprintf(STDERR_FILENO,"<read sync %zu>\n",number_reads);
		number_reads++;
	}
	return real_read(fd,buf,count);
}
