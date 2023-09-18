/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasexpr.h,v 1030.7 88/02/18 14:55:39 bettina Exp $ */
    procedure Load(
	    var Fattr : Attr); external;
    procedure Loadaddress(
	    var Fattr : Attr); external;
    procedure Store(
	    var Fattr : Attr); external;
      procedure Getatemp(
	      var Fattr : Attr;
		  Fstrp : Strp;
	      var Stamp : integer;
		  Regok : boolean); external;
      procedure Freetemps(
		  FStamp : integer); external;

      procedure Selector(
		  Fsys : Setofsys;
		  Fidp : Idp;
		  var baseindir: Indirtype); external;
      procedure Loadboth(
	      var Fattr : Attr); external;
      procedure Matchtypes(
	      var Fattr : Attr); external;
      procedure Matchtoassign(
	      var Fattr : Attr;
		  Ftypep : Strp); external;
      procedure Shiftset (
	var Setval : Valu;
	    Shift,
	    Finallength : integer); external;
      procedure Setmatchtoassign(
	      var Fattr : Attr;
		  Ftypep : Strp;
		  Spacked : boolean); external;
      procedure Loadandcheckbounds(
	      var Fattr : Attr;
		  Fboundtypep : Strp); external;
    procedure Expression(
		Fsys : Setofsys); external;
