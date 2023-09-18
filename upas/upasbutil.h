/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasbutil.h,v 1030.7 88/02/18 14:55:36 bettina Exp $ */

  function Comptypes(
	     Fstrp1,
	     Fstrp2 : Strp)
     : boolean; external;
  function Stringpadpossible(
	     Fstrp1: Strp;
	var  Fattr: Attr)
     : boolean; external;
  procedure Getbounds(
	      Fstrp : Strp;
	  var Fmin,
	      Fmax : integer); external;
  function Strng(
	     Fstrp : Strp)
     : boolean; external;
  procedure Constant(
	      Fsys : Setofsys;
	  var Fstrp : Strp;
	  var Fvalu : Valu); external;
