/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: data.c,v 1030.6 88/03/02 13:45:56 bettina Exp $ */

/* Pascal provides its own definition of _iob with the _ptr field for
   stdout and stderr already initialized (we rely on flsbuf to take care
   of the _base field), so that Pascal "output^ := c" will work. In SYSV,
   this definition is already in its own file data.c, so it's easy for us
   to override it; in 4.3BSD, it lies in findiop.c and we can't separate
   it lest we mess up the precarious method of selecting between short
   and long versions of _cleanup, so we grab all of findiop.c.
*/

#include "pascalio.h"

#ifdef BSD

extern	char	*calloc();

#define active(iop)	((iop)->_flag & (_IOREAD|_IOWRT|_IORW))

#define NSTATIC	20	/* stdin + stdout + stderr + the usual */

static	char sbuf[NSTATIC];
char	*_smallbuf = sbuf;

FILE _iob[NSTATIC] = {
	{ 0, NULL, NULL, 0, _IOREAD,		0 },	/* stdin  */
	{ 0, &sbuf[1], NULL, 0, _IOWRT,		1 },	/* stdout */
	{ 0, &sbuf[2], NULL, 0, _IOWRT|_IONBF,	2 },	/* stderr */
};

static	FILE	**iobglue;
static	FILE	**endglue;

/*
 * Find a free FILE for fopen et al.
 * We have a fixed static array of entries, and in addition
 * may allocate additional entries dynamically, up to the kernel
 * limit on the number of open files.
 * At first just check for a free slot in the fixed static array.
 * If none are available, then we allocate a structure to glue together
 * the old and new FILE entries, which are then no longer contiguous.
 */
FILE *
_findiop()
{
	register FILE **iov, *iop;
	register FILE *fp;

	if (iobglue == 0) {
		for (iop = _iob; iop < _iob + NSTATIC; iop++)
			if (!active(iop))
				return (iop);

		if (_f_morefiles() == 0) {
			errno = ENOMEM;
			return (NULL);
		}
	}

	iov = iobglue;
	while (*iov != NULL && active(*iov))
		if (++iov >= endglue) {
			errno = EMFILE;
			return (NULL);
		}

	if (*iov == NULL)
		*iov = (FILE *)calloc(1, sizeof **iov);

	return (*iov);
}

_f_morefiles()
{
	register FILE **iov;
	register FILE *fp;
	register char *cp;
	int nfiles;

	nfiles = getdtablesize();

	iobglue = (FILE **)calloc(nfiles, sizeof *iobglue);
	if (iobglue == NULL)
		return (0);

	endglue = iobglue + nfiles;

	for (fp = _iob, iov = iobglue; fp < &_iob[NSTATIC]; /* void */)
		*iov++ = fp++;

	_smallbuf = calloc(nfiles, sizeof(*_smallbuf));
	return (1);
}

f_prealloc()
{
	register FILE **iov;
	register FILE *fp;

	if (iobglue == NULL && _f_morefiles() == 0)
		return;

	for (iov = iobglue; iov < endglue; iov++)
		if (*iov == NULL)
			*iov = (FILE *)calloc(1, sizeof **iov);
}

_fwalk(function)
	register int (*function)();
{
	register FILE **iov;
	register FILE *fp;

	if (iobglue == NULL) {
		for (fp = _iob; fp < &_iob[NSTATIC]; fp++)
			if (active(fp))
				(*function)(fp);
	} else {
		for (iov = iobglue; iov < endglue; iov++)
			if (*iov && active(*iov))
				(*function)(*iov);
	}
}

_cleanup()
{
	extern int fclose();

	_fwalk(fclose);
}

#endif

#ifdef SYSV

/* some slop is allowed at the end of the buffers in case an upset in
 * the synchronization of _cnt and _ptr (caused by an interrupt or other
 * signal) is not immediately detected.
 */
unsigned char _sibuf[BUFSIZ+8] = {0};
unsigned char _sobuf[BUFSIZ+8] = {0};
/*
 * Ptrs to start of preallocated buffers for stdin, stdout.
 */
unsigned char *_stdbuf[] = { _sibuf, _sobuf };

unsigned char _smbuf[_NFILE+1][_SBFSIZ];

FILE _iob[_NFILE] = {
	{ 0, NULL, NULL, _IOREAD, 0},
	{ 0, _sobuf, NULL, _IOWRT, 1},
	{ 0, _smbuf[2], NULL, _IOWRT+_IONBF, 2},
};

/*
 * Ptr to end of io control blocks
 */
FILE *_lastbuf = { &_iob[_NFILE] };

/*
 * Ptrs to end of read/write buffers for each device
 * There is an extra bufend pointer which corresponds to the dummy
 * file number _NFILE, which is used by sscanf and sprintf.
 */
unsigned char *_bufendtab[_NFILE+1] = { NULL, NULL, _smbuf[2]+_SBFSIZ, };

#endif
