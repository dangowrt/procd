/*
 * Copyright (C) 2020 Daniel Golle <daniel@makrotopia.org>
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

#ifndef _JAIL_CGROUPS_H
#define _JAIL_CGROUPS_H

#include <stdbool.h>

void cgroups_init(const char *p);
int parseOCIlinuxcgroups(struct blob_attr *msg, bool is_update);
void cgroups_apply(pid_t pid);
int cgroups_attach_pid(pid_t pid);
int cgroups_kill_all(void);
void cgroups_free(void);
void cgroups_prepare(void);

#endif
