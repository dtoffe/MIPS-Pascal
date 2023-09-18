/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: new.c,v 1030.6 88/03/02 13:45:25 bettina Exp $ */

#include "pascalio.h"

unsigned char *
new (size, zero)
     unsigned size;
     unsigned zero;
{
    register unsigned char *p = xmalloc(size);
    if (zero && p != NULL) memset(p, 0, size);
    return (p);
}

void
dispose (p, size)
     unsigned char * p;
     unsigned size;
{
    xfree (p);
}
