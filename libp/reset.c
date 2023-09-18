/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: reset.c,v 1030.6 88/03/02 13:45:34 bettina Exp $ */

#include <sys/param.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "pascalio.h"
#define L_SET 0

/* Given a file descriptor and desired size, compute size of buffer that
  we should use */
unsigned long
calc_size (f, size)
    FILE *f;
    register unsigned size;
{
    struct stat stbuf;
    extern unsigned char _sibuf[];
    register unsigned bsize;

#ifdef BSD
    if (fstat(fileno(f), &stbuf) < 0 || stbuf.st_blksize <= 0) {
	bsize = BUFSIZ;
    }
    else {
	bsize = stbuf.st_blksize;
    }
#endif
#ifdef SYSV
    bsize = BUFSIZ;
#endif
    return max(bsize / size * size, size);
}

void
reset (fref, name, namelength, size)
     register struct pascal_file *fref;
     register unsigned char *name;
     register unsigned namelength;
     register unsigned size;	/* Zero for text file, else record size */
{
    register FILE *f;

    f = fref->stdiofile;

    while (namelength != 0 && name[namelength-1] == ' ') namelength -= 1;

    if (namelength != 0) {
	register unsigned char *n = name;
	name = malloc(namelength+1);
	memcpy (name, n, namelength);
	name[namelength] = '\0';
	fref->name = name;
    }
    else {
	name = fref->name;
	if (name == NULL) {
	    if (f != NULL) {
		fseek (f, 0, L_SET);
		return;
	    }
	    /* The open below will fail, because this is a new filename. */
	    name = malloc(TMP_LENGTH);
	    _libp_pascal_file_counter += 1;
	    sprintf(name, TMP_FILE, _libp_pascal_file_counter, getpid());
	    fref->name = name;
	}
    }
    /** Need to assure that buffer size is multiple of record size **/
    if (f != NULL) {
	f = freopen(name, "r", f);
    } else {
	f = fopen(name, "r");
    }
    if (f != NULL) {
       	if (size != 0) {	/* Non text file */
	    register unsigned bsize = calc_size(f, size);
	    register int ctemp;

#ifdef SYSV
	    /* ugly ugly -- they steal some bytes!#?$* */
	    bsize += 8;
#endif
	    if (f == stdin) {
		f->_base = _sibuf;
	    }
	    else {
		unsigned char *our_size = (unsigned char *) malloc(bsize);
		setvbuf(f, our_size, ((our_size) ? _IOFBF : _IONBF), bsize);
	    }
	    ctemp = _filbuf(f);
	    if (ctemp != EOF) ungetc(ctemp, f);
	}
    }
    fref->stdiofile = f;
}
