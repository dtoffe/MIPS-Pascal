/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: clock.c,v 1030.6 88/03/02 13:45:29 bettina Exp $ */

/* Return user cpu time, not including child processes, in milliseconds */

#include "pascalio.h"

#ifdef SYSV
#include <limits.h>
#include <sys/types.h>
#include <sys/times.h>

#define CLK_TCK 60

unsigned long
clock()
{
    struct tms buffer;
    if (times(&buffer) == -1) exit(123);
    return (buffer.tms_utime * 1000) / CLK_TCK;
}
#endif

#ifdef BSD
#include <sys/time.h>
#include <sys/resource.h>

unsigned long
clock()
{
    struct rusage ru;
    getrusage(0, &ru);
    return (ru.ru_utime.tv_sec * 1000 + ru.ru_utime.tv_usec / 1000);
}
#endif
