/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: put.c,v 1030.6 88/03/02 13:45:33 bettina Exp $ */

#include <stdio.h>

void
put (f, size)
     register FILE *f;
     register int size;		/* unsigned causes unsigned test below */
{
    if (!(f->_flag & _IOWRT)) {
	fprintf(stderr, "put called on file not open for writing.\n");
	return;
    }
    f->_ptr += size;
    f->_cnt -= size;
    if (f->_cnt < size) {
	if (f->_base == NULL) {	/* stdout or stderr 1st output */
	    f->_cnt = 0;
	    _flsbuf(*(f->_ptr-1), f);
	} else {
	    fflush(f);
	}
    }
}
