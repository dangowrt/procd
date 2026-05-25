/*
 * libpreload-seccomp.so
 *
 * Receive a pre-compiled cBPF seccomp filter from ujail (or from
 * seccomp-trace) via a sealed memfd whose descriptor number is passed in
 * the SECCOMP_BPF_FD environment variable, install
 * PR_SET_NO_NEW_PRIVS, then load the filter via the seccomp() syscall.
 * The helper is wired in via LD_PRELOAD so that the filter is armed
 * AFTER ld.so has finished its work and AFTER libc has set up its
 * private state, but BEFORE the workload's own main(). That ordering is
 * the whole reason this helper exists: it lets the cBPF program forbid
 * execve, dynamic-linker bootstrap syscalls and libc init syscalls
 * without those calls tripping the filter before the workload's first
 * instruction runs.
 *
 * Why a constructor and not __libc_start_main interception:
 *
 *   The hook used to be a replacement __libc_start_main (with a
 *   __uClibc_main fallback) that called the real entry point via
 *   dlsym(RTLD_NEXT, ...). That trick is libc-specific: glibc, musl and
 *   uClibc all expose __libc_start_main / __uClibc_main with a stable
 *   prototype, but bionic does not. A constructor attached via
 *   __attribute__((constructor)) runs in the same window (after the
 *   dynamic linker has called libc's init code, before the executable's
 *   own constructors and main()) on every libc that supports DT_INIT /
 *   DT_INIT_ARRAY, which is to say every libc the kernel can boot a
 *   userspace on.
 *
 * Why a sealed memfd and not a path:
 *
 *   The earlier design passed SECCOMP_FILE=/path/to/seccomp.json and
 *   compiled the BPF inside the workload's address space. That dragged
 *   libubox and libblobmsg_json into the jail rootfs and exposed a JSON
 *   parser to the workload's attackers. ujail now compiles the JSON to
 *   cBPF on the host side, writes the struct sock_filter[] array into a
 *   memfd created with MFD_ALLOW_SEALING, seals it with
 *   F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK, and hands the
 *   descriptor number to us via SECCOMP_BPF_FD. The workload sees a
 *   tamper-evident copy of the filter; libubox and libblobmsg_json no
 *   longer have to live in the jail rootfs.
 *
 * Build modes:
 *
 *   The CMake build picks one of two modes for this file. The default
 *   is to link against the system libc, just like any other helper
 *   library. When CMake is invoked with -DNOLIBC_INCLUDE_DIR set to the
 *   kernel tree's tools/include/nolibc directory, the helper is built
 *   freestanding (-nostdlib -ffreestanding -fno-builtin -include
 *   nolibc.h). In that mode the helper has no DT_NEEDED entries at all;
 *   getenv(), strtol(), fstat(), mmap(), close(), prctl(),
 *   fprintf() etc. come from nolibc as static-inline syscall wrappers,
 *   and the workload's bind-mount of libc/libdl is no longer needed to
 *   load the helper. The freestanding mode exists to defend against the
 *   theoretical two-libcs-in-one-process trap when a binary built
 *   against a different libc than ujail itself is run under classic
 *   procd-jail with -S; on a stock musl OpenWrt the two modes are
 *   functionally identical.
 *
 *   The two modes share a single source. Including nolibc.h via -include
 *   defines the NOLIBC macro, and the conditional system-header block
 *   below skips the system <stdio.h>, <stdlib.h> etc. in that case so
 *   nolibc's static-inline definitions do not clash with the system
 *   declarations.
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

#ifndef NOLIBC
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
#endif

#include <linux/filter.h>
#include <linux/seccomp.h>

#ifdef NOLIBC
/* nolibc's sys/syscall.h only provides the syscall() macro; the kernel
 * uapi header below is what defines __NR_seccomp. We mirror it to
 * SYS_seccomp so the syscall() call site below works in both modes. */
#include <asm/unistd.h>
#ifndef SYS_seccomp
#define SYS_seccomp __NR_seccomp
#endif
#endif

static void preload_die(const char *msg)
{
	int e = errno;

	fprintf(stderr, "preload-seccomp: %s: %s\n", msg,
		e ? strerror(e) : "");
	_exit(127);
}

#ifdef NOLIBC
/*
 * nolibc's getenv() reads from the weak environ symbol that the dynamic
 * loader never populates for shared objects; in freestanding LD_PRELOAD
 * context environ is always NULL. Fetch the value from /proc/self/environ
 * instead so the constructor can locate SECCOMP_BPF_FD regardless of
 * libc's bootstrap state.
 */
static const char *preload_getenv_proc(char *buf, size_t buflen, const char *key)
{
	int fd;
	ssize_t n, total = 0;
	size_t klen = 0;
	const char *p;

	while (key[klen])
		klen++;

	fd = open("/proc/self/environ", O_RDONLY);
	if (fd < 0)
		return NULL;

	while (total < (ssize_t)buflen - 1) {
		n = read(fd, buf + total, buflen - 1 - total);
		if (n < 0) {
			if (errno == EINTR)
				continue;
			close(fd);
			return NULL;
		}
		if (n == 0)
			break;
		total += n;
	}
	close(fd);
	buf[total] = '\0';

	for (p = buf; p < buf + total; ) {
		size_t plen = 0;
		while (p + plen < buf + total && p[plen])
			plen++;
		if (plen > klen && p[klen] == '=' &&
		    !memcmp(p, key, klen))
			return p + klen + 1;
		p += plen + 1;
	}
	return NULL;
}
#endif

__attribute__((constructor))
static void preload_seccomp_install(void)
{
#ifdef NOLIBC
	char envbuf[4096];
	const char *fd_env = preload_getenv_proc(envbuf, sizeof(envbuf),
						 "SECCOMP_BPF_FD");
#else
	const char *fd_env = getenv("SECCOMP_BPF_FD");
#endif
	struct sock_fprog prog;
	struct sock_filter *filter;
	struct stat st;
	char *end;
	long fd;

	/* SECCOMP_BPF_FD is only set when ujail wanted a seccomp filter
	 * installed; running the preload in any other process is a no-op. */
	if (!fd_env || !fd_env[0])
		return;

	errno = 0;
	fd = strtol(fd_env, &end, 10);
	if (errno || *end || fd < 0 || fd > 0x7fffffff)
		preload_die("malformed SECCOMP_BPF_FD");

#ifndef NOLIBC
	unsetenv("SECCOMP_BPF_FD");
	unsetenv("LD_PRELOAD");
#endif

	if (fstat((int)fd, &st) < 0)
		preload_die("fstat");

	/* The memfd contains the raw struct sock_filter[] array, nothing
	 * else; the length is implied by the file size. ujail sealed the
	 * memfd against grow/shrink/write, so the size we read here matches
	 * what ujail wrote. */
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

	/* The kernel copied the BPF program at SET_MODE_FILTER time, so the
	 * mmap is dead weight from here on. We deliberately leave it mapped
	 * rather than munmap; one tiny read-only mapping is cheap, and a
	 * stale environ entry pointing at the now-closed fd is harmless
	 * because nothing else in the workload knows the SECCOMP_BPF_FD
	 * contract. */
}
