/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: caseerror.c,v 1030.6 88/03/02 13:45:26 bettina Exp $ */

#include "pascalio.h"

caseerror (page, line, name, namelength)
     register unsigned char *name;
     register unsigned namelength;
{
    register unsigned char *n = malloc(namelength+1);
    memcpy (n, name, namelength);
    n[namelength] = '\0';
    fprintf (stderr,
      "No case matches value in case statement on page %d line %d file %s.\n",
      page, line, n);
}
