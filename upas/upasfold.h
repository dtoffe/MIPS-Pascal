/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasfold.h,v 1030.7 88/02/18 14:55:41 bettina Exp $ */

function is_constant (
	   t : pttreerec)
   : boolean;
  external;

function is_float_constant (
	   t : pttreerec)
   : boolean;
  external;

function float_fold (
	var u : bcrec;
	    fleft : pttreerec;
	    fright : pttreerec)
    : boolean;
  external;

function fold (
	var u : bcrec;
	    fleft : pttreerec;
	    fright : pttreerec)
    : boolean;
  external;

procedure ConstantExpression (
	    Fsys : Setofsys;
	var Fstrp : Strp;
	var Fvalu : Valu);
  external;
