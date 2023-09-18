/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: time.c,v 1030.6 88/03/02 13:46:00 bettina Exp $ */

#include <sys/param.h>
#ifdef BSD
#	include <sys/time.h>
#else
#	include <sys/types.h>
#	include <time.h>
#endif

__time (s, l)
	register char *s;
	register int l;
{
#ifdef BSD
	struct timeval tv;
#else
	time_t sec;
#endif
	register struct tm *tp;
	register unsigned y;

	if (l <= 0) return;
#ifdef BSD
	gettimeofday (&tv, 0);
	tp = localtime (&tv.tv_sec);
#else
	sec = time (0);
	tp = localtime (&sec);
#endif
	s[0] = (tp->tm_hour / 10) + '0';
	if (l == 1) return;
	s[1] = (tp->tm_hour % 10) + '0';
	if (l == 2) return;
	s[2] = ':';
	if (l == 3) return;
	s[3] = (tp->tm_min / 10) + '0';
	if (l == 4) return;
	s[4] = (tp->tm_min % 10) + '0';
	if (l == 5) return;
	s[5] = ':';
	if (l == 6) return;
	s[6] = (tp->tm_sec / 10) + '0';
	if (l == 7) return;
	s[7] = (tp->tm_sec % 10) + '0';
	if (l == 8) return;
	memset (s+8, ' ', l-8);
}
