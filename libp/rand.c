/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: rand.c,v 1030.6 88/03/02 13:46:01 bettina Exp $ */

#ifdef MIPSEL
#	define LSW 0
#	define MSW 1
#else
#	define LSW 1
#	define MSW 0
#endif

double __random_float ()
{
	union {
		double d;
		unsigned w[2];
	} o;
	o.w[LSW] = random();
	o.w[MSW] = random();
	o.w[LSW] = o.w[LSW] ^ (o.w[1] << 31);
	o.w[MSW] = (o.w[MSW] >> 11) | (1023<<20);
	return o.d - 1.0;
}
