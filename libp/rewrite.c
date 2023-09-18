/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: rewrite.c,v 1030.6 88/03/02 13:45:36 bettina Exp $ */

#include "pascalio.h"
#define L_SET 0

void
rewrite (fref, name, namelength, size)
     register struct pascal_file *fref;
     register unsigned char *name;
     register unsigned namelength;
     register unsigned size;	/* Zero for text file, else record size */
{
    register FILE *f;

    f = fref->stdiofile;
    while (namelength != 0 && name[namelength-1] == ' ') namelength -= 1;
    if (namelength != 0) {
	/* Remember supplied name for reset/rewrite with no name. */
	register unsigned char *n = name;
	name = malloc(namelength+1);
	memcpy (name, n, namelength);
	name[namelength] = '\0';
	fref->name = name;
    }
    else {
	name = fref->name;
	if (name == NULL) {
	    /* No name, and no previous name.  Use a file in /tmp. */
	    if (f != NULL) {
		fseek (f, 0, L_SET);
		return;
	    }
	    name = malloc(TMP_LENGTH);
	    _libp_pascal_file_counter += 1;
	    sprintf(name, TMP_FILE, _libp_pascal_file_counter, getpid());
	    fref->name = name;
	}
    }
    if (f != NULL) {
	f = freopen(name, "w", f);
    } else {
	f = fopen(name, "w");
    }
    if (f != NULL) {
	if (f->_base == NULL) {
	    _getbuf (f, size != 0 ? size : 1);
	}
    }
    fref->stdiofile = f;
}
