/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasutil.h,v 1030.7 88/02/18 14:55:33 bettina Exp $ */
function Log2(Fval: integer): Bitrange; external;
function Roundup(
	I: integer;
	J: integer) : integer; external;
function Rounddown(
	   I : integer;
	   J : integer)
   : integer; external;
function Alignobject(
	   Memctr : integer;
	   Fsize,
	   Align : integer)
   : integer; external;
function Aligndown(
	   Memctr : integer;
	   Fsize,
	   Align : integer)
   : integer; external;
function Findmemorytype(
	   Dty : Datatype;
	   Fsize : Sizerange;
	   Isparam,
	   Istemp : boolean)
   : Memtype; external;
function Assignnextmemoryloc(
	   Mty : Memtype;
	   Fsize : Sizerange;
	   Align : cardinal)
   : integer; external;
function Getlabel
   : integer; external;
function Stringsize(
	   Charcount : integer)
   : integer; external;
function Stringchars(
	   Strsize : integer)
   : integer; external;
function Intlen(
	   I : integer)
   : integer; external;
function Fnln (Fn : Filename) : integer; external;
function Idln(
	   Id : Identname)
   : integer; external;
procedure Makeexternalname(
	var Fid : Identname); external;
procedure Enterid(
	    Fidp : Idp); external;
procedure Searchsection(
	    Fidp : Idp;
	var Fidp1 : Idp); external;
procedure Searchid(
	    Fidcls : Setofids;
	var Fidp : Idp); external;
procedure Filenameassign(var f: filename; str: identname); external;
