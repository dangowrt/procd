/*
 * Install a pre-compiled seccomp BPF filter passed in from ujail via a
 * sealed memfd identified by the SECCOMP_BPF_FD environment variable.
 *
 * Copyright (C) 2026 Daniel Golle <daniel@makrotopia.org>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License version 2.1
 * as published by the Free Software Foundation
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <linux/filter.h>
#include <linux/seccomp.h>

static void preload_die(const char *msg)
{
	int e = errno;

	fprintf(stderr, "preload-seccomp: %s: %s\n", msg,
		e ? strerror(e) : "");
	_exit(127);
}

__attribute__((constructor))
static void preload_seccomp_install(void)
{
	const char *fd_env = getenv("SECCOMP_BPF_FD");
	struct sock_fprog prog;
	struct sock_filter *filter;
	struct stat st;
	char *end;
	long fd;

	if (!fd_env || !fd_env[0])
		return;

	errno = 0;
	fd = strtol(fd_env, &end, 10);
	if (errno || *end || fd < 0 || fd > 0x7fffffff)
		preload_die("malformed SECCOMP_BPF_FD");

	unsetenv("SECCOMP_BPF_FD");
	unsetenv("LD_PRELOAD");

	if (fstat((int)fd, &st) < 0)
		preload_die("fstat");

	if (st.st_size == 0 || (size_t)st.st_size % sizeof(*filter))
		preload_die("bad memfd size");

	filter = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, (int)fd, 0);
	if (filter == MAP_FAILED)
		preload_die("mmap");

	close((int)fd);

	prog.len = st.st_size / sizeof(*filter);
	prog.filter = filter;

	if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0))
		preload_die("PR_SET_NO_NEW_PRIVS");

	if (syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog))
		preload_die("seccomp(SET_MODE_FILTER)");
}
