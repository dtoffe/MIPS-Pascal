/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: getbuf.c,v 1030.6 88/03/02 13:45:37 bettina Exp $ */

#include <sys/param.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "pascalio.h"

/* Create a new buffer of size rsize for use with file iop */
void
_getbuf (iop, rsize)
     register FILE *iop;
     register unsigned rsize;
{
    int size, type;

    size = calc_size(iop, rsize);
    type = (iop==stdout && isatty(fileno(stdout))) ? _IOLBF : _IOFBF;
    setvbuf(iop, (unsigned char *) malloc((unsigned) size), type, size);
    iop->_cnt = size;
}
