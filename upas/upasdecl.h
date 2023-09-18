/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasdecl.h,v 1030.7 88/02/18 14:55:37 bettina Exp $ */

  procedure Labeldeclaration(Fsys: Setofsys); external; 
  procedure Constantdeclaration(Fsys: Setofsys); external;
  procedure Typedeclaration(Fsys: Setofsys); external;
  procedure Variabledeclaration(Fprocp: Idp;
				Fsys: Setofsys); external;
  procedure Proceduredeclaration(Fsys: Setofsys; 
	var Forwardprocedures: Idp ;Procflag : boolean); external;
