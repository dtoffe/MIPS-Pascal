{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: allocator.p,v 1030.6 88/03/02 13:45:50 bettina Exp $ }
/*------------------------------------------------------------------*/
/*| Copyright Unpublished, MIPS Computer Systems, Inc.  All Rights |*/
/*| Reserved.  This software contains proprietary and confidential |*/
/*| information of MIPS and its suppliers.  Use, disclosure or     |*/
/*| reproduction is prohibited without the prior express written   |*/
/*| consent of MIPS.                                               |*/
/*------------------------------------------------------------------*/
/*$Header: allocator.p,v 1030.6 88/03/02 13:45:50 bettina Exp $*/


#ifndef PASTEL
type
  pointer = cardinal;
#endif

#ifdef PASTEL
#  define ptradd(_type, _ptr, _offset) _type(addrel(_ptr, _offset))
#else
#  define ptradd(_type, _ptr, _offset) _type(ord(_ptr) + (_offset))
#endif

#include "cmplrs/mipspascal.h"
#include "allocator.h"

const
  default_scb_size = 64*1024;
  bcb_mask = 16#fffffffc;
  curr_allocated = 16#1;
  prev_allocated = 16#2;
  min_fragment = 256;

type
  scbp = ^scb;

  bcbp = ^bcb;

  scb =
    record
      last_scb : scbp;
      next_scb : scbp;
      free_list : bcbp;
      scb_size : integer;
    end {record};

  {---------------------------------------------------------------------------}
  { curr_size is the size of the current bcb, it is always a factor of 8. The }
  { lowest two bits encode whether the entry is allocated and whether the     }
  { previous entry is allocated. The two masks curr_allocated and	      }
  { prev_allocated are used to determine the two conditions.		      }
  {---------------------------------------------------------------------------}
  bcb =
    record
      prev_size : integer;
      curr_size : integer;
      case boolean of
	true : ();
	false : (
	  last_bcb : bcbp;
	  next_bcb : bcbp);
    end {record};

var
  alloc_anchor : scbp := nil;

function sbrk (
	   fsize : integer)
   : scbp;
  external;

procedure memcpy (
	    toptr,
	    fromptr : pointer;
	    fsize : cardinal);
  external;

function alloc_page (
	   fsize : integer)
   : scbp;
  var
    p : scbp;
    q : scbp;
    i : integer;
  begin
    if (alloc_anchor = nil) or (alloc_anchor^.scb_size < fsize) then begin
      p := sbrk(fsize);
      if ord(p) = -1 then p := nil
      else if bitand(ord(p), -4096) <> ord(p) then begin
	i := bitand(ord(p)+4095, -4096)-ord(p);
	q := sbrk(i);
	p := ptradd(scbp, p, i);
      end;
    end else begin
      p := alloc_anchor;
      alloc_anchor := alloc_anchor^.next_scb;
    end;
    alloc_page := p;
  end {function alloc_page};

procedure alloc_free (
	    fptr : scbp);

  begin
    fptr^.next_scb := alloc_anchor;
    alloc_anchor := fptr;
    fptr^.scb_size := abs(fptr^.scb_size);
  end {procedure alloc_free};

procedure alloc_dump (
	    fheap : pointer);
  var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;
    ca : boolean;
    pa : boolean;
    i : integer;

  begin
    p := scbp(fheap);
    while p <> nil do begin
      writeln;
      write('scb     ', ord(p) : 8 : 16, ' ', p^.scb_size : 8, ' ',
	  ord(p^.last_scb) : 8 : 16, ' ', ord(p^.next_scb) : 8 : 16, ' ');
      if p^.scb_size > 0 then write(ord(p^.free_list) : 8 : 16);
      writeln;
      r := ptradd(bcbp, p, sizeof(scb)+16);
      i := bitand(r^.curr_size, bcb_mask);
      repeat
	write('bcb     ', ord(r) : 8 : 16, ' ', i : 8, ' ');
	ca := bitand(r^.curr_size, curr_allocated) = curr_allocated;
	pa := bitand(r^.curr_size, prev_allocated) = prev_allocated;
	if not ca then begin
	  write(ord(r^.last_bcb) : 8 : 16, ' ', ord(r^.next_bcb) : 8 : 16);
	  if pa then write('prev alloc ')
	  else write('prev free  ');
	  s := ptradd(bcbp, r, i);
	  if s^.prev_size <> i then write('<= block not consistent');
	end;
	writeln;
	r := ptradd(bcbp, r, i);
	i := bitand(r^.curr_size, bcb_mask);
      until i = 0;
      p := p^.next_scb;
    end {while};
    writeln;
  end {procedure alloc_dump};

procedure alloc_scb (
	var fmark : scbp;
	    fsize : integer);
  var
    q : scbp;
    r : bcbp;
    s : bcbp;

  begin
    q := alloc_page(fsize);
    fmark := q;
    if q = nil then return;
    q^.scb_size := -fsize;
    q^.last_scb := nil;
    q^.next_scb := nil;

    {-------------------------------------------------------------------------}
    { construct a bcb out of free space 				      }
    {-------------------------------------------------------------------------}
    r := ptradd(bcbp, q, sizeof(scb));
    s := ptradd(bcbp, q, fsize-8);
    r^.prev_size := 0;
    r^.curr_size := ord(s)-ord(r)+prev_allocated;
    s^.prev_size := ord(s)-ord(r);
    s^.curr_size := 0+curr_allocated;
    r^.last_bcb := r;
    r^.next_bcb := r;
    q^.free_list := r;
  end {procedure alloc_scb};

function alloc_mark;
{ (
       var fheap : integer)
   : integer;
  external;
  }
  var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;
    t : bcbp;
    rsize : integer;

  begin
    alloc_scb(q, default_scb_size);
    if q = nil then return(0);
    alloc_mark := ord(q);
    p := scbp(fheap);

    {-------------------------------------------------------------------------}
    { chain scb onto list						      }
    {-------------------------------------------------------------------------}
    if p <> nil then begin
      while p^.next_scb <> nil do p := p^.next_scb;
      p^.next_scb := q;
      q^.last_scb := p;
    end;
#ifdef PASTEL
    fheap := q;
#else
    fheap := ord(q);
#endif
    q^.scb_size := abs(q^.scb_size);

    r := q^.free_list;
    rsize := bitand(r^.curr_size, bcb_mask);
    s := ptradd(bcbp, r, sizeof(bcb));
    t := ptradd(bcbp, r, rsize);
    r^.next_bcb := s;
    r^.last_bcb := s;
    s^.next_bcb := r;
    s^.last_bcb := r;
    t^.prev_size := ord(t)-ord(s);
    s^.curr_size := ord(t)-ord(s)+prev_allocated;
    r^.curr_size := 0+prev_allocated;
    q^.free_list := s;

  end {function alloc_mark};

procedure alloc_release;
{ (
	var fheap : integer;
	    fmark : integer);
  external;
  }
  var
    p : scbp;
    q : scbp;
    r : scbp;

  begin
    p := scbp(fheap);
    q := scbp(fmark);

    {-------------------------------------------------------------------------}
    { be sure mark is in the heap					      }
    {-------------------------------------------------------------------------}
    while (p <> q) and (p <> nil) do p := p^.last_scb;
    if p = nil then return;		{ could post an error		      }

    {-------------------------------------------------------------------------}
    { set the heap to the first mark before fmark or nil		      }
    {-------------------------------------------------------------------------}
    r := q^.last_scb;
    if r <> nil then r^.next_scb := nil;
    while (r <> nil) and (r^.scb_size < 0) do r := r^.last_scb;
#ifdef PASTEL
    fheap := r;
#else
    fheap := ord(r);
#endif

    {-------------------------------------------------------------------------}
    { free all the scb's from the mark until the end of the list              }
    {-------------------------------------------------------------------------}
    repeat
      r := q^.next_scb;
      alloc_free(q);
      q := r;
    until q = nil;

  end {procedure alloc_release};

function alloc_next_scb (
	   fsize : integer;
       var fheap : pointer)
   : integer;
  var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;

  begin
    /* alloc_dump(fheap);						     */
    alloc_scb(q, max(default_scb_size, bitand(fsize+8+sizeof(scb)+4095,
	16#7ffff000)));
    if q = nil then return(0);
    p := scbp(fheap);

    {-------------------------------------------------------------------------}
    { chain scb onto list						      }
    {-------------------------------------------------------------------------}
    while p^.next_scb <> nil do p := p^.next_scb;
    p^.next_scb := q;
    q^.last_scb := p;
    p := scbp(fheap);
    r := q^.free_list;
    s := p^.free_list;

    {-------------------------------------------------------------------------}
    { place bcb on free chain						      }
    {-------------------------------------------------------------------------}
    if s <> nil then begin
      r^.last_bcb := s^.last_bcb;
      r^.next_bcb := s;
      s^.last_bcb^.next_bcb := r;
      s^.last_bcb := r;
    end;
    p^.free_list := r;
    return(1);
  end {function alloc_next_scb};

function alloc_resize
/* (
	    fptr : pointer;
	    fsize : cardinal;
	var fheap : pointer)
   : pointer */
  ;
  var
    nptr : bcbp;
    csize : integer;

  begin
    nptr := ptradd(bcbp, fptr, -8);
    if bitand(nptr^.curr_size, curr_allocated) = 0 then return(pointer(nil));
    csize := bitand(nptr^.curr_size, bcb_mask);
    if csize >= fsize then return(fptr);

    nptr := bcbp(alloc_new(fsize, fheap));
    if nptr = nil then return(pointer(nil));
    memcpy(pointer(nptr), fptr, csize);
    alloc_dispose(fptr, fheap);
    alloc_resize := pointer(nptr);

  end {function alloc_resize};

#ifndef host_mips
function alloc_new;
{ (
	   fsize : integer;
       var fheap : integer)
   : pointer;
  external;
  }
  var
    i : integer;
    lsize : integer;
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;
    t : bcbp;

  begin
    /* alloc_dump(fheap);						     */
    p := scbp(fheap);

    {-------------------------------------------------------------------------}
    { implicit mark for new that wasn't preceeded by a mark                   }
    {-------------------------------------------------------------------------}
    if p = nil then begin
      i := alloc_mark(fheap);
      if i = 0 then return(nil);
      p := scbp(fheap);
    end;

    {-------------------------------------------------------------------------}
    { search free list until a block larger than the request is found	      }
    {-------------------------------------------------------------------------}
    r := p^.free_list;
    s := r;
    lsize := max(16, bitand(fsize+11, 16#fffffff8));

    repeat
      i := bitand(r^.curr_size, bcb_mask);
      r := r^.next_bcb;
    until (i >= lsize) or (r = s);
    r := r^.last_bcb;

    {-------------------------------------------------------------------------}
    { if no more room in free list, therefore we must allocate a new scb      }
    {-------------------------------------------------------------------------}
    if i < lsize then begin
      i := alloc_next_scb(fsize, fheap);
      if i = 0 then return(nil);
      r := p^.free_list;
      i := bitand(r^.curr_size, bcb_mask);
    end;

    {-------------------------------------------------------------------------}
    { if the block found is only slightly too big, we allocate the entire     }
    { block so as to avoid lots of useless fragments			      }
    {-------------------------------------------------------------------------}
    if (i-min_fragment) <= lsize then begin { allocate entire block	      }
      r^.last_bcb^.next_bcb := r^.next_bcb;
      r^.next_bcb^.last_bcb := r^.last_bcb;
      p^.free_list := r^.next_bcb;
      r^.curr_size := bitor(r^.curr_size, curr_allocated);
      s := ptradd(bcbp, r, i);
      s^.curr_size := bitor(s^.curr_size, prev_allocated);
#ifdef PASTEL
      alloc_new := addrel(r, 8);
#else
      alloc_new := ord(r)+8;
#endif
      return;
    end;

    {-------------------------------------------------------------------------}
    { allocate the new element at the bottom of the block and fix all the     }
    { allocation bits and sizes 					      }
    {-------------------------------------------------------------------------}
    s := ptradd(bcbp, r, i);
    s^.curr_size := bitor(s^.curr_size, prev_allocated);
    s^.prev_size := lsize;
    s := ptradd(bcbp, s, -lsize);
    s^.curr_size := bitor(lsize, curr_allocated);
#ifdef PASTEL
    alloc_new := addrel(s, 8);
#else
    alloc_new := ord(s)+8;
#endif
    s^.prev_size := i-lsize;
    r^.curr_size := bitor(i-lsize, prev_allocated);
    p^.free_list := r;
    return;

  end {function alloc_new};

procedure alloc_dispose;
{ (
	    fptr : pointer;
	var fheap : integer);
  external;

  }
  var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;
    t : bcbp;
    u : bcbp;
    x : bcbp;
    y : bcbp;
    z : bcbp;
    lsize : integer;
    msize : integer;
    rsize : integer;
    ssize : integer;
    tsize : integer;

  begin
    /* alloc_dump(fheap);						     */
    r := ptradd(bcbp, fptr, -8);
    p := scbp(fheap);
    if p^.last_scb <> nil then begin

      {-----------------------------------------------------------------------}
      { find scb that contains block, either forward from heap or backward    }
      {-----------------------------------------------------------------------}
      while (p <> nil) and ((ord(p) > ord(r))
       or ((ord(p)+abs(p^.scb_size)) < ord(r))) do p := p^.next_scb;
      if p = nil then begin
	p := scbp(fheap);
	while (p <> nil) and ((ord(p) > ord(r))
	 or ((ord(p)+abs(p^.scb_size)) < ord(r))) do p := p^.last_scb;
	if p = nil then return; 	{ could report an error 	      }
      end;

      {-----------------------------------------------------------------------}
      { find mark that controls storage for that scb			      }
      {-----------------------------------------------------------------------}
      while p^.scb_size < 0 do p := p^.last_scb;
    end;

    lsize := r^.curr_size;
    rsize := bitand(lsize, bcb_mask);
    s := ptradd(bcbp, r, rsize);
    msize := s^.curr_size;
    ssize := bitand(msize, bcb_mask);

    {-------------------------------------------------------------------------}
    { special case each of the four possiblities : merge the blocks above and }
    { below; merge just the block above; merge just the block below and merge }
    { no blocks 							      }
    {-------------------------------------------------------------------------}
    if bitand(lsize, prev_allocated) = 0 then begin
      tsize := r^.prev_size;
      t := ptradd(bcbp, r, -tsize);
      if not odd(msize) then begin	{ merge all three blocks	      }
	u := p^.free_list;
	tsize := tsize+rsize+ssize;
	if (tsize >= min_fragment) and (r^.prev_size < min_fragment) then
	  begin
/**/
	  x := u^.last_bcb;
	  t^.next_bcb := u;
	  t^.last_bcb := x;
	  x^.next_bcb := t;
	  u^.last_bcb := t;
	end;
	t^.curr_size := tsize+prev_allocated;
	z := ptradd(bcbp, t, tsize);
	z^.prev_size := tsize;
	if ssize < min_fragment then return;
	x := s^.next_bcb;
	y := s^.last_bcb;
	y^.next_bcb := x;
	x^.last_bcb := y;
	if u = s then p^.free_list := x;
	return;
      end else begin			{ merge upper and middle blocks       }
	tsize := tsize+rsize;
	if (tsize >= min_fragment) and (r^.prev_size < min_fragment) then
	  begin
	  u := p^.free_list;
/**/
	  x := u^.last_bcb;
	  t^.next_bcb := u;
	  t^.last_bcb := x;
	  x^.next_bcb := t;
	  u^.last_bcb := t;
	end;
	t^.curr_size := tsize+prev_allocated;
	s^.curr_size := ssize+curr_allocated;
	s := ptradd(bcbp, t, tsize);
	s^.prev_size := tsize;
	return;
      end;
    end else begin
      if not odd(msize) then begin	{ merge middle and lower blocks       }
	rsize := rsize+ssize;
	u := p^.free_list;
	if (rsize >= min_fragment) then begin
/**/
	  x := u^.last_bcb;
	  r^.next_bcb := u;
	  r^.last_bcb := x;
	  x^.next_bcb := r;
	  u^.last_bcb := r;
	end;
	t := ptradd(bcbp, r, rsize);
	t^.prev_size := rsize;
	r^.curr_size := rsize+prev_allocated;
	if ssize < min_fragment then return;
	x := s^.next_bcb;
	y := s^.last_bcb;
	y^.next_bcb := x;
	x^.last_bcb := y;
	if u = s then p^.free_list := x;
	return;
      end else begin			{ just put block onto chain	      }
	if (rsize >= min_fragment) then begin
	  u := p^.free_list;
/**/
	  x := u^.last_bcb;
	  r^.next_bcb := u;
	  r^.last_bcb := x;
	  x^.next_bcb := r;
	  u^.last_bcb := r;
	end;
	t := ptradd(bcbp, r, rsize);
	t^.prev_size := rsize;
	r^.curr_size := rsize+prev_allocated;
	s^.curr_size := ssize+curr_allocated;
	return;
      end;
    end;
  end {procedure alloc_dispose};

var
  malloc_scb : pointer;

function malloc;
{(
	   fsize : integer);
   : pointer;
  external;
}
  begin
    malloc := alloc_new(fsize, malloc_scb);
  end {function malloc};

procedure free;
{(
	    fptr : pointer);
  external;
}
  begin
    alloc_dispose(fptr, malloc_scb);
  end {procedure free};

function realloc;
{(
	   fptr : pointer;
	   fsize : integer);
   : pointer;
  external;
}
  begin
    realloc := alloc_resize(fptr, fsize, malloc_scb);
  end {function realloc};
#endif host_mips

