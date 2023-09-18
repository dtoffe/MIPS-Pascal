/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upaslex.h,v 1030.7 88/02/18 14:55:35 bettina Exp $ */

procedure Error(
	    Ferrnr : integer); external;
procedure Errorwithid(
	    Ferrnr : integer;
	    Varnam : Identname); external;
procedure Warning(
	    Ferrnr : integer); external;
procedure Warningwithid(
	    Ferrnr : integer;
	    Varnam : Identname); external;
procedure Skipiferr(
	    Fsyinsys : Setofsys;
	    Ferrnr : integer;
	    Fskipsys : Setofsys); external;
procedure Iferrskip(
	    Ferrnr : integer;
	    Fsys : Setofsys); external;
procedure Errandskip(
	    Ferrnr : integer;
	    Fsys : Setofsys); external;
procedure Newfile(
	var Infile : text); external;
procedure Finishline; external;
procedure Setswitch(
	    Switchname : Identname;
	    Switchval : integer); external;
procedure Insymbol; external;
