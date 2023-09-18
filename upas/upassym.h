/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upassym.h,v 1030.7 88/02/18 14:55:40 bettina Exp $ */
#define iauxNil -1

procedure st_feinit; external;
procedure Popbtmap; external;
procedure Syminit; external;
procedure Addnullfilename(var s: Filename); external;
function Symaddstr (
	   idname : Identname): integer; external;
function Symaddextstr (
	   idname : Identname): integer; external;
function Typetoaux (
     typeptr: Strp; replicate, auxneeded, needpack, noneedsamefile: boolean): 
   integer; external;
procedure Resolveptrauxes; external;
