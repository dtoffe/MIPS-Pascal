/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: get_arg.c,v 1030.6 88/03/02 13:45:27 bettina Exp $ */

extern unsigned __Argc;
extern unsigned char **__Argv;

get_arg(i, s, l)
     register unsigned i;
     register unsigned char *s;
     register unsigned l;
{
    register unsigned char *e = s + l;
    if (i < __Argc) {
	register unsigned char *p = __Argv[i];
	register unsigned c;
	while (s != e && (c = *p++) != '\0') {
	    *s++ = c;
	}
    }
    while (s != e) {
	*s++ = ' ';
    }
}
