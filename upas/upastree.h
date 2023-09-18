/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upastree.h,v 1030.7 88/02/18 14:55:40 bettina Exp $ */
    procedure Pushstak (
		i : pttreerec); external;
/*   procedure Popstak; external;	*/
#define Popstak  if errorcount = 0 then stak := stak^.next
    procedure Swapstak; external;
    function Gettreenode: pttreerec; external;
    procedure Leafnode; external;
    procedure Unarynode; external;
    procedure Binarynode; external;
    function Duplicatetree(root: pttreerec): pttreerec; external;
    function Isboolexpr(root: pttreerec): boolean; external;
    function Startwithor(root: pttreerec): boolean; external;
    procedure Exprprepass(root: pttreerec); external;
    procedure Genexpr(root: pttreerec); external;
    procedure Jumpboolexpr(root: pttreerec; 
			   isfjp: boolean; 
			   exitlab, altlab: integer); external;
    procedure Strboolexpr(root: pttreerec;
			  notted: boolean;
			  lhstree: pttreerec; 
		     var  Fattr: Attr;
			  exitlab: integer;
			  exitwhentrue: boolean;
			  altlab: integer); external;
