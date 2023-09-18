/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: allocator.h,v 1030.7 88/02/18 14:55:42 bettina Exp $ */
function alloc_mark (
       var fheap : pointer)
   : pointer;
  external;

procedure alloc_release (
	var fheap : pointer;
	    fmark : pointer);
  external;

function alloc_new (
	   fsize : integer;
       var fheap : pointer)
   : pointer;
  external;

procedure alloc_dispose (
	    fptr : pointer;
	var fheap : pointer);
  external;

