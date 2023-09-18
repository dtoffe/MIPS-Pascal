/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: exit.c,v 1030.6 88/03/02 13:45:30 bettina Exp $ */

#include "pascalio.h"

void
exit (code)
     int code;
{
    /* Delete /tmp files. */
    register unsigned i;
    for (i = _libp_pascal_file_counter; i != 0; i-= 1) {
	unsigned char namebuf[TMP_LENGTH];
	unsigned char *name = namebuf;
	sprintf (name, TMP_FILE, i, getpid());
	unlink (name);
    }
    _cleanup();
    _exit(code);
}
