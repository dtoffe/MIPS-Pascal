/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: pascalio.h,v 1030.6 88/03/02 13:45:23 bettina Exp $ */
#include <stdio.h>

#define private static
#define boolean unsigned
#define true 1
#define false 0
#define abs(x) ((x) < 0 ? -(x) : (x))
#define min(a,b) ((a) < (b) ? (a) : (b))
#define max(a,b) ((a) > (b) ? (a) : (b))

unsigned _libp_pascal_file_counter;
unsigned _libp_ansi_pascal;

#define TMP_FILE "/tmp/pas%d.%d"
#define TMP_LENGTH 24

struct pascal_file {
    FILE *stdiofile;
    char *name;
};

#ifdef BSD
#define _IOFBF 0
#define setvbuf(stream, buf, type, size) \
  (setbuffer(stream, (((type) == _IONBF) ? (unsigned char *)0 : (buf)), size), \
  (((type) == _IOLBF) ? setlinebuf(stream) : 0))
#endif

unsigned long
calc_size(/* FILE *f; unsigned long size */);

unsigned char *malloc(), *xmalloc();

#include <errno.h>
extern int errno;
