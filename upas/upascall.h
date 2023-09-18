/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upascall.h,v 1030.7 88/02/18 14:55:38 bettina Exp $ */

      procedure Callspecial(
		  Fsys : Setofsys;
		  Fidp : Idp); external;
      procedure Callinline(
		  Fsys : Setofsys;
		  Fidp : Idp); external;
      procedure Callregular(
		  Fsys : Setofsys;
		  Fidp: Idp); external;
