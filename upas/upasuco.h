/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasuco.h,v 1030.7 88/02/18 14:55:34 bettina Exp $ */

procedure Uco0(
	    Fop : Uopcode); external;
procedure Uco1type(
	    Fop : Uopcode;
	    Fdty : Datatype); external;
procedure Uco1int(
	    Fop : Uopcode;
	    Fint : integer); external;
procedure UcoProcpointer(Fidp: Idp); external;
procedure Uco1idp(
	    Fop : Uopcode;
	    Fidp : Idp); external;
procedure Ucoinit(
	    Fdty : Datatype;
	    Fblock : integer;
	    Foffset,
	    Foffset2 : Addrrange;
	    Flength : Sizerange;
	    Fval : Valu); external;
procedure Uco2typtyp(
	    Fop : Uopcode;
	    Fdty1,
	    Fdty2 : Datatype); external;
procedure Uco1attr(
	    Fop : Uopcode;
	    Fattr : Attr); external;
procedure Uco2typint(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fint : integer); external;
procedure Uco2intint(
	    Fop : Uopcode;
	    Fint1,
	    Fint2 : integer); external;
procedure Ucosym(
	    Fop : Uopcode;
	    Fint1,
	    Fint2,
	    Fint3: integer); external;
procedure Ucolab(
	    Fname,
	    flag1,
	    flag2 : integer); external;
procedure Ucooptn(
	    Fname : integer;
	    Fint : integer); external;
procedure Uco3int(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fint1,
	    Fint2 : integer); external;
procedure Uco3intval(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fint1,
	    Fint2 : integer); external;
procedure Uco3val(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fint : integer;
	    Fval : Valu); external;
procedure Uco4int(
	    Fop : Uopcode;
	    Llev,
	    Int,
	    Off,
	    Len : integer); external;
procedure Uco5typaddr(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fmty : Memtype;
	    Fblock : integer;
	    Foffset,
	    Flen : Addrrange); external;
procedure Uco6(
	    Fop : Uopcode;
	    Fdty : Datatype;
	    Fmty : Memtype;
	    Fblock : integer;
	    Foffset,
	    Flen,
	    Foffset2 : Addrrange); external;
procedure Ucolda(
	    Fmty : Memtype;
	    Fblock : integer;
	    Foffset,
	    Flen,
	    Foffset2: Addrrange); external;
procedure Ucomem(
	    Fop: Uopcode;
	    Fdty : Datatype;
	    Fmty : Memtype;
	    Fblock : integer;
	    Foffset,
	    Flen : Addrrange); external;
procedure Ucodef(
	    Fmty : Memtype;
	    Fint : integer); external;
procedure Ucoloc(
	    Fline,
	    Ffile: integer); external;
procedure Ucoxjp(
	    Fdty : Datatype;
	    Ffirstlabel,
	    Fotherslabel : integer;
	    Flowbound,
	    Fhighbound : integer); external;
procedure Support(
	    Fsupport : Supports); external;
procedure Stdcallinit(
	var Parcount : integer); external;
procedure Par(
	    Dtype : Datatype;
	var Parcount : integer); external;
procedure Partype (Typep : Strp; var Parcount : integer); external;
function Genstaticchain(blk: integer): boolean; external;
function Getstaticlink(lv: integer): boolean; external;
procedure Passstaticlink(lv : integer; genpar: boolean); external;
