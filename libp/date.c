/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: date.c,v 1030.6 88/03/02 13:45:58 bettina Exp $ */

#include <sys/param.h>
#ifdef BSD
#	include <sys/time.h>
#else
#	include <sys/types.h>
#	include <time.h>
#endif

__date (s, l)
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
	y = tp->tm_year % 100;
	s[0] = (y / 10) + '0';
	if (l == 1) return;
	s[1] = (y % 10) + '0';
	if (l == 2) return;
	s[2] = '/';
	if (l == 3) return;
	s[3] = ((tp->tm_mon + 1) / 10) + '0';
	if (l == 4) return;
	s[4] = ((tp->tm_mon + 1) % 10) + '0';
	if (l == 5) return;
	s[5] = '/';
	if (l == 6) return;
	s[6] = (tp->tm_mday / 10) + '0';
	if (l == 7) return;
	s[7] = (tp->tm_mday % 10) + '0';
	if (l == 8) return;
	memset (s+8, ' ', l-8);
}
