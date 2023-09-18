{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasexpr.p,v 1030.7 88/02/18 14:55:21 bettina Exp $ }

#include "upasglob.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upasbutil.h"
#include "upascall.h"
#include "upastree.h"
#include "upasfold.h"
#include "upasexpr.h"
#include "allocator.h"



(*Load,Store,Loadaddress*)
(************************************************************************)
(*									*)
(* LOADADDRESS -- loads address of an Attr onto the stack		*)
(* If the address of FATTR has already been loaded, then does nothing	*)
(* UNLESS there is a constant non-zero displacement, in which case it	*)
(* emits an IXA to combine the displacement with the base address;	*)
(* if it has NOT been loaded, then loads it, and updates ATTR to	*)
(* reflect that fact.							*)
(*									*)
(************************************************************************)

procedure Loadaddress (* var Fattr : Attr *);
  var
    lop : Uopcode;
    ldty : Datatype;
  begin 				(* loadaddress			     *)
    with Fattr do begin
      if Atypep <> nil then begin
	case Kind of
	Cnst : begin
	    if Strng(Atypep) then begin
	      Uco1attr(Ulca, Fattr);
	    end else begin
	      Error(171);
	    end;
	  end {case Cnst};
	Varbl : begin
	    if Indirect <> Notind then begin
	      lop := Ulod;
	      if (Indexmt in [Mmt, Pmt]) and Genstaticchain(Ablock) then begin
		lop := Uisld;
	      end;
	      ldty := Adt;
	      if Indirect = Hind then ldty := Hdt;
	      Uco5typaddr(lop, ldty, Indexmt, Ablock, Indexr, Pointersize);
	      Indirect := Notind;
	      Indexed := true;
	    end;
	    if Indexed then begin
	      if Dplmt mod Addrunit <> 0 then Error(171);
	      if Dplmt < 0 then begin
		Uco2typint(Udec, Adt, (-Dplmt) div Addrunit);
	      end else if Dplmt > 0 then begin
		Uco2typint(Uinc, Adt, Dplmt div Addrunit);
	      end;
	    end else begin		(* not indexed			     *)
	      lop := Ulda;
	      if (Amty in [Mmt, Pmt]) and Genstaticchain(Ablock) then begin
		lop := Uilda;
	      end;
	      Uco1attr(lop, Fattr);
	    end;
	  end {case Varbl};
	Expr :
	    ;
	end {case};
	Kind := Varbl;
	Dplmt := 0;
	Aclass := Vars;
	Indexed := true;
	Asize := Pointersize;
      end;
    end {with};
  end {procedure Loadaddress};

function ivalue (
    Fdty: Datatype;
    i: integer): pttreerec;
  var
    t: pttreerec;
  begin
    t := Gettreenode;
    t^.U.Opc := Uldc;
    t^.U.Dtype := Fdty;
    t^.U.length := Wordsize;
    t^.U.Constval.ival := i;
    t^.l := nil;
    t^.r := nil;
    return t;
  end {ivalue};

function bop (
    Fop: Uopcode;
    Fdty: Datatype;
    l, r: pttreerec
    ): pttreerec;
  var
    t: pttreerec;
  begin
    t := Gettreenode();
    t^.U.Opc := Fop;
    t^.U.Dtype := Fdty;
    t^.U.Lexlev := 0;		{ overflow check }
    t^.l := l;
    t^.r := r;
    return t;
  end {bop};

function get_bit_index (
    t: pttreerec;
    var cindex: integer;
    var vindex: pttreerec
    ): pttreerec;
  var
    t2, t3: pttreerec;
  begin
    case t^.U.opc of
      Uinc, Udec:
	begin
	  t2 := t;
	  t := get_bit_index(t2^.l, cindex, vindex);
	  cindex := cindex + t2^.U.I1 * Addrunit;
	end;
      Uixa:
	begin
	  if t^.U.I1 < Wordsize then begin
	    t2 := t;
	    t := get_bit_index (t2^.l, cindex, vindex);
	    if t2^.U.I1 = 1 then begin
	      t3 := t2^.r;
	    end else begin
	      t3 := bop(Umpy, t2^.r^.U.Dtype, t2^.r,
				ivalue(t2^.r^.U.Dtype, t2^.U.I1));
	    end;
	    if vindex = nil then begin
	      vindex := t3;
	    end else begin
	      vindex := bop(Uadd, vindex^.U.Dtype, vindex, t3);
	    end;
	  end;
	end;
      otherwise: ;
    end {case};
    return t;
  end {get_bit_index};

(************************************************************************)
(*									*)
(*  LOAD - loads an Attr onto the stack 				*)
(*									*)
(*  If fattr is a constant or variable, generates code to load it on	*)
(*  the stack, if it has not already been loaded (this is always the	*)
(*  case when fattr is an expression).	if it is too big to be loaded	*)
(*  on the stack, loads its address, if it has not already been loaded	*)
(*									*)
(************************************************************************)

#ifndef PASTEL	/* PASTEL's mod is not floormod, whereas UPAS's is. */
#define floormod(a,b) ((a) mod (b))
#endif
const
  Halfsize = 2*Bytesize;

procedure Load (* var fattr: attr *);
  var
    lop : Uopcode;
    ldty : Datatype;
    shiftl, shiftr: 0..Wordsize-1;
    l: Bytesize..Wordsize;
    Lattr, Tattr : Attr;
    Lstamp : integer;
    vindex : pttreerec;
    boff : integer;
  begin
    shiftl := 0;			{ bit-field shift left amount }
    shiftr := 0;			{ bit-field shift right amount }
    vindex := nil;			{ variable shift amount }
    with Fattr do begin
      if Atypep <> nil then begin
	case Kind of
	Expr :
	    ;
	Cnst : begin
	    lop := Uldc;
	    if Atypep^.Stdtype = Mdt then 
	      lop := Ulca;
	    Uco1attr(lop, Fattr);
	  end {case Cnst};
	Varbl : begin
	    if Atypep^.Stdtype = Mdt then begin
	      Loadaddress(Fattr);
	    end else begin
	      vindex := nil;
	      if Indexed and (Asize < Bytesize) then begin
		stak^.tree := get_bit_index(stak^.tree, Dplmt, vindex);
	        if vindex <> nil then begin
		  boff := Dplmt mod Wordsize;
		  if boff <> 0 then begin
		    Dplmt := Dplmt - boff;
		    vindex := bop(Uadd, vindex^.U.Dtype, vindex,
					ivalue(vindex^.U.Dtype, boff));
		  end;
		  Pushstak(vindex);
		  Lstamp := 0;
		  Getatemp(Tattr, Intptr, Lstamp, false);
		  Store(Tattr);
		  Lattr := Tattr;
		  Load(Lattr);
		  assert((Bytesize = 8) and (Wordsize = 32));
		  Uco3intval(Uldc, Ldt, Wordsize, 5);
		  Uco1type(Ushr, vindex^.U.Dtype);
		  Uco2typint(Uixa, stak^.tree^.U.Dtype, Wordsize);
		end;
	      end;
	      if Indirect <> Notind then begin
		lop := Ulod;
		if (Amty in [Mmt, Pmt]) and Genstaticchain(Ablock) then begin
		  lop := Uisld;
		end;
		ldty := Adt;
		if Indirect = Hind then ldty := Hdt;
		Uco5typaddr(lop, ldty, Indexmt, Ablock, Indexr, Pointersize);
		Indirect := Notind;
		Indexed := true;
	      end;
	      { Check for bit-field references.  For bit-fields, turn into
		byte, halfword, or word reference, and set shift amounts
		to cause extraction after reference is complete. }
	      if (Asize < Wordsize)
	      and not (   ((Asize = Halfsize) and (floormod(Dplmt, Halfsize) = 0))
		       or ((Asize = Bytesize) and (floormod(Dplmt, Bytesize) = 0)))
	      then begin
		{ Find smallest unit (byte, word, halfword) that contains field.
		  Test is for first and last bits of field in same unit. }
		l := Wordsize;
		if vindex = nil then begin
		  if (abs(Dplmt) div Halfsize)
		      = (abs(Dplmt + Asize - 1) div Halfsize) then begin
		    l := Halfsize;
		    if (abs(Dplmt) div Bytesize)
			= (abs(Dplmt + Asize - 1) div Bytesize) then begin
		      l := Bytesize;
		    end;
		  end;
		end;
		{ Compute shift right and left amounts.  Left shift brings
		  most significant bit of field to left end of register and
		  right shift then sign or zero extends. }
		{ Perhaps should bump l to Wordsize in some cases to aid
		  cse of loads. }
		if lsb_first then begin
		  shiftr := floormod(Dplmt, l);
		  shiftl := l - (shiftr + Asize);
		  if shiftl <> 0 then shiftl := shiftl + (Wordsize - l);
		  Dplmt := Dplmt - shiftr;
		  shiftr := shiftr + shiftl;
		end else if Atypep^.Stdtype = Sdt then begin
		  { On msb first machines, sets get extracted to msb
		    part of word rather than lsb part.  Aren't msb first
		    machines ugly? }
		  l := Wordsize;
		  shiftl := floormod(Dplmt, Wordsize);
		  Dplmt := Dplmt - shiftl;
		  shiftr := Wordsize - (shiftl + Asize);
		  shiftl := shiftl + shiftr;
		end else begin
		  shiftl := floormod(Dplmt, l);
		  Dplmt := Dplmt - shiftl;
		  if shiftl <> 0 then begin
		    shiftl := shiftl + (Wordsize - l);
		    shiftr := Wordsize - Asize;
		  end else begin
		    shiftr := l - Asize;
		  end;
		end;
		Asize := l;
	      end;
	      if Indexed then begin
		Uco1attr(Uilod, Fattr);
		Indexed := false;
	      end else begin
		lop := Ulod;
		if (Amty in [Mmt, Pmt]) and Genstaticchain(Ablock) then begin
		  lop := Uisld;
		end;
		Uco1attr(lop, Fattr);
	      end;
	    end;
	  end {case Varbl};
	end {case};
	if Atypep^.Stdtype <> Mdt then begin
	  Kind := Expr;
	end;
	if vindex <> nil then begin
	  Load(Tattr);
	  lop := Ushr;
	  if not lsb_first then begin
	    lop := Ushl;
	  end;
	  Uco1type(lop, Adtype);
	  Freetemps (Lstamp);
	end;
	if not lsb_first and (Atypep^.Stdtype = Sdt) then begin
	  if shiftr <> 0 then begin
	    Uco3intval (Uldc, Ldt, Intsize, shiftr);
	    Uco1type (Ushr, Adtype);
	  end;
	  if shiftl <> 0 then begin
	    Uco3intval (Uldc, Ldt, Intsize, shiftl);
	    Uco1type (Ushl, Adtype);
	  end;
	end else if (shiftl = shiftr) and (shiftr >= Halfsize)
	    and (Adtype = Ldt) then begin
	  Uco3intval (Uldc, Adtype, Intsize, lshift(1, Wordsize-shiftr)-1);
	  Uco1type (Uand, Adtype);
	end else begin
	  if shiftl <> 0 then begin
	    Uco3intval (Uldc, Ldt, Intsize, shiftl);
	    Uco1type (Ushl, Adtype);
	  end;
	  if shiftr <> 0 then begin
	    Uco3intval (Uldc, Ldt, Intsize, shiftr);
	    Uco1type (Ushr, Adtype);
	  end;
	end;
      end;
    end {with};
  end {procedure Load};


(************************************************************************)
(*									*)
(* STORE								*)
(*									*)
(* Generates code to store the value on top of the stack in the memory	*)
(* location described by FATTR.  If the value is too large to fit on	*)
(* the stack, a MOV is used to do the store.  If the address of FATTR	*)
(* already been loaded (e.g. FATTR describes a location in an array),	*)
(* then an ISTR is used.						*)
(*									*)
(************************************************************************)


procedure Store (* var Fattr : Attr *);
  var
    schainused : boolean;
    lop : Uopcode;
    exitlab : integer;
    shiftl, shiftr: 0..Wordsize-1;
    l: Bytesize..Wordsize;
    k1, k2: cardinal;
    Lattr, Tattr, Tattr2 : Attr;
    Lstamp : integer;
    ldty : Datatype;
    vindex : pttreerec;
    boff : integer;
  begin
    with Fattr do begin
      if Atypep <> nil then begin
	Lstamp := 0;
	vindex := nil;
	if Indexed and (Asize < Bytesize) then begin
	  stak^.next^.tree := get_bit_index(stak^.next^.tree, Dplmt, vindex);
	  if vindex <> nil then begin
	    boff := Dplmt mod Wordsize;
	    if boff <> 0 then begin
	      Dplmt := Dplmt - boff;
	      vindex := bop(Uadd, vindex^.U.Dtype, vindex,
				  ivalue(vindex^.U.Dtype, boff));
	    end;
	    Pushstak(vindex);
	    Getatemp(Tattr2, Intptr, Lstamp, false);
	    Store(Tattr2);
	    Swapstak;
	    Lattr := Tattr2;
	    Load(Lattr);
	    assert((Bytesize = 8) and (Wordsize = 32));
	    Uco3intval(Uldc, Ldt, Wordsize, 5);
	    Uco1type(Ushr, vindex^.U.Dtype);
	    Uco2typint(Uixa, stak^.next^.tree^.U.Dtype, Wordsize);
	    Swapstak;
	  end;
	end;
	if Indirect <> Notind then begin
	  lop := Ulod;
	  if (Indexmt in [Mmt, Pmt]) and Genstaticchain(Ablock) then lop := Uisld;
	  ldty := Adt;
	  if Indirect = Hind then ldty := Hdt;
	  Uco5typaddr(lop, ldty, Indexmt, Ablock, Indexr, Pointersize);
	  Swapstak;
	  Indirect := Notind;
	  Indexed := true;
	end;
	if not Indexed then begin
	  if Atypep^.Stdtype = Mdt then begin
	    Error(171);
	  end;
	end;
	{ Check for bit-field references.  For bit-fields, turn into
	  byte, halfword, or word load/store. }
	if (Asize < Wordsize)
	and not (   ((Asize = Halfsize) and (floormod(Dplmt, Halfsize) = 0))
		 or ((Asize = Bytesize) and (floormod(Dplmt, Bytesize) = 0)))
	then begin
	  { Find smallest unit (byte, word, halfword) that contains field.
	    Test is for first and last bits of field in same unit. }
	  if Indexed then begin
	    Getatemp(Tattr, Addressptr, Lstamp, false);
	    Swapstak;
	    Store(Tattr);
	    Lattr := Tattr;
	    Load(Lattr);
	    Swapstak;
	  end;
	  l := Wordsize;
#if 0
	  if vindex = nil then begin
	    if (abs(Dplmt) div Halfsize)
		= (abs(Dplmt + Asize - 1) div Halfsize) then begin
	      l := Halfsize;
	      if (abs(Dplmt) div Bytesize)
		  = (abs(Dplmt + Asize - 1) div Bytesize) then begin
		l := Bytesize;
	      end;
	    end;
	  end;
#endif
	  { Compute shift right and left amounts.  }
	  if lsb_first then begin
	    shiftr := floormod(Dplmt, l);
	    shiftl := Wordsize - (shiftr + Asize);
	    Dplmt := Dplmt - shiftr;
	  end else begin
	    shiftl := floormod(Dplmt, l);
	    shiftr := Wordsize - (shiftl + Asize);
	    Dplmt := Dplmt - shiftl;
	  end;
	  Asize := l;
	  if (vindex = nil) and is_constant(stak^.tree) then begin
	    k1 := lshift(1,Wordsize-shiftl-shiftr)-1;
	    k2 := bitand(stak^.tree^.u.constval.ival, k1);
	    k1 := lshift(k1, shiftr);
	    k2 := lshift(k2, shiftr);
	    Popstak;
	    if Indexed then begin
	      Lattr := Tattr;
	      Load (Lattr);
	    end;
	    Lattr := Fattr;
	    Load (Lattr);
	    if k1 <> k2 then begin
	      Uco3intval (Uldc, Ldt, Intsize, bitnot(k1));
	      Uco1type (Uand, Ldt);
	    end;
	    if k2 <> 0 then begin
	      Uco3intval (Uldc, Ldt, Intsize, k2);
	      Uco1type (Uior, Ldt);
	    end;

	  end else if not lsb_first and (Atypep^.Stdtype = Sdt) then begin

	    { aren't msb first machines disgusting? }

	    if Indexed then begin
	      Lattr := Tattr;
	      Load (Lattr);
	    end;
	    Lattr := Fattr;
	    Load (Lattr);
	    if shiftl <> 0 then begin
	      Uco3intval (Uldc, Ldt, Intsize, shiftl);
	      Uco1type (Ushl, Ldt);
	    end;
	    if vindex <> nil then begin
	      Lattr := Tattr2;
	      Load(Lattr);
	      Uco1type (Ushl, Ldt);
	    end;
	    Uco1type (Uxor, Ldt);
	    Uco3intval (Uldc, Ldt, Intsize, shiftl+shiftr);
	    Uco1type (Ushr, Ldt);
	    if shiftr <> 0 then begin
	      Uco3intval (Uldc, Ldt, Intsize, shiftr);
	      Uco1type (Ushl, Ldt);
	    end;
	    if vindex <> nil then begin
	      Lattr := Tattr2;
	      Load(Lattr);
	      Uco1type (Ushr, Ldt);
	    end;
	    if Indexed then begin
	      Lattr := Tattr;
	      Load (Lattr);
	    end;
	    Lattr := Fattr;
	    Load (Lattr);
	    Uco1type (Uxor, Ldt);

	  end else begin

	    { not storing constant }

	    if Indexed then begin
	      Lattr := Tattr;
	      Load (Lattr);
	    end;
	    Lattr := Fattr;
	    Load (Lattr);
	    if vindex <> nil then begin
	      Lattr := Tattr2;
	      Load(Lattr);
	      lop := Ushr;
	      if not lsb_first then lop := Ushl;
	      Uco1type (lop, Ldt);
	    end;
	    if shiftr <> 0 then begin
	      Uco3intval (Uldc, Ldt, Intsize, shiftr);
	      Uco1type (Ushr, Ldt);
	    end;
	    Uco1type (Uxor, Ldt);
	    if (shiftr = 0) and (shiftl >= Halfsize) then begin
	      Uco3intval (Uldc, Ldt, Intsize, lshift(1,Wordsize-shiftl)-1);
	      Uco1type (Uand, Ldt);
	    end else begin
	      Uco3intval (Uldc, Ldt, Intsize, shiftl+shiftr);
	      Uco1type (Ushl, Ldt);
	      if shiftl <> 0 then begin
		Uco3intval (Uldc, Ldt, Intsize, shiftl);
		Uco1type (Ushr, Ldt);
	      end;
	    end;
	    if vindex <> nil then begin
	      Lattr := Tattr2;
	      Load(Lattr);
	      lop := Ushl;
	      if not lsb_first then lop := Ushr;
	      Uco1type (lop, Ldt);
	    end;
	    if Indexed then begin
	      Lattr := Tattr;
	      Load (Lattr);
	    end;
	    Lattr := Fattr;
	    Load (Lattr);
	    Uco1type (Uxor, Ldt);
	  end;
	  if Indexed then begin
	    Freetemps (Lstamp);
	  end;
	end;
	{ generate the code						      }
	if Indexed then begin
	  Exprprepass(stak^.next^.tree);
	  Exprprepass(stak^.tree);
	  Genexpr(stak^.next^.tree);
	  Genexpr(stak^.tree);
	  if Atypep^.Stdtype = Mdt then begin (* two addresses on the stack  *)
	    Uco2intint(Umov, Atypep^.Align, Atypep^.Stsize);
	  end else begin		(* a value into an address, both on  *)
					(* the stack			     *)
	    Uco1attr(Uistr, Fattr);
	  end;
	  Popstak;
	  Popstak;
	end else begin			(* not indexed			     *)
#if 0 /* Aug19,85 */
	  if Isboolexpr(stak^.tree) then begin
	    if not (Amty in [Mmt, Pmt]) then begin
	      schainused := false;
	    end else begin
	      schainused := Genstaticchain(Ablock);
	    end;
	    lastuclabel := lastuclabel+1;
	    exitlab := lastuclabel;
	    if schainused then begin
	      Strboolexpr(stak^.next^.tree, false, stak^.tree, Fattr,
		  exitlab, Startwithor(stak^.next^.tree), exitlab);
	    end else begin
	      Strboolexpr(stak^.tree, false, nil, Fattr, exitlab,
		  Startwithor(stak^.tree), exitlab);
	    end;
	    Ucolab(exitlab, 0, 0);
	    if schainused then begin
	      Popstak;
	    end;
	  end else
#endif
	    begin
	    if not (Amty in [Mmt, Pmt]) then begin
	      schainused := false;
	    end else begin
	      schainused := Genstaticchain(Ablock);
	    end;
	    if schainused then begin
	      Exprprepass(stak^.next^.tree);
	      Genexpr(stak^.tree);
	      Popstak;
	      (* if rhs is a function call, do not pre-generate the top call *)
	    end else if stak^.tree^.U.opc in [Ucup, Uicuf] then begin
	      Exprprepass(stak^.tree^.l);
	    end else begin
	      Exprprepass(stak^.tree);
	    end;
	    Genexpr(stak^.tree);
	    if schainused then begin
	      Uco1attr(Uisst, Fattr);
	    end else begin
	      Uco1attr(Ustr, Fattr);
	    end;
	  end;
	  Popstak;
	end;
      end;
    end {with};
  end {procedure Store};


(*Getatemp,Freetemps*)
procedure Getatemp (* var Fattr : Attr; Fstrp : Strp; var Stamp : integer; Regok : boolean *);
  (* reserves a temporary location for an intermediate result corresponding  *)
  (* to the type pointed to by FSTR and puts a description of it in FATTR    *)

  label
    11;

  var
    I, Tempnum : integer;
  begin 				(* getatemp			     *)
    if Stamp = 0 then begin
      Stampctr := Stampctr+1;
      Stamp := Stampctr;
    end;
    if Fstrp <> nil then begin
      (* try to re-use old temporary					     *)
      for I := 1 to Tempcount do begin
	with Temps[I] do begin
	  if Free
	      and (Fstrp^.Stsize = Tsize)
	      and (Fstrp^.Stdtype = Stdtype)
	      and (Regok = Vreg) then begin
	    Tempnum := I;
	    goto 11;
	  end;
	end {with};
      end {for};
      (* no free temps; create a new one				     *)
      if Tempcount = Maxtemps then begin
	Error(171);			(* Compiler error		     *)
      end else begin
	Tempcount := Tempcount+1;
      end;
      with Temps[Tempcount] do begin
	Tsize := Fstrp^.Stsize;
	Stdtype := Fstrp^.Stdtype;
	Vreg := Regok;
	Mty := Findmemorytype(Fstrp^.Stdtype, Tsize, false, true);
	Offset := Assignnextmemoryloc(Mty, Tsize, Fstrp^.Align);
	if Regok then begin
	  Ucomem(Uvreg, Stdtype, Mty, Memblock, Offset, Tsize);
	end;
      end {with};
      Tempnum := Tempcount;
11 :
      Temps[Tempnum].Free := false;
      Temps[Tempnum].Stamp := Stamp;
      with Fattr do begin
	Amty := Temps[Tempnum].Mty;
	Dplmt := Temps[Tempnum].Offset;
(*	      Tsize := Temps[Tempnum].Tsize; ??? Per Bothner *)
	Asize := Fstrp^.Stsize;
	Baseaddress := Dplmt;
	Atypep := Fstrp;
	Adtype := Fstrp^.Stdtype;
	Kind := Varbl;
	Ablock := Memblock;
	Indirect := Notind;
	Indexed := false;
	Apacked := false;
	Subkind := nil;
	Aclass := Vars;
      end {with};
    end;
  end {procedure Getatemp};

procedure Freetemps (* FStamp : integer *);
  (* Free all temps that have stamp FSTAMP				     *)
  var
    I : integer;
  begin
    for I := 1 to Tempcount do begin
      with Temps[I] do begin
	if Stamp = FStamp then begin
	  if Free then begin
	    Error(171); 		(* compiler error		     *)
	  end else begin
	    Free := true;
	  end;
	end;
      end {with};
    end {for};
  end {procedure Freetemps};

(*Selector*)
(************************************************************************)
(*									*)
(*	SELECTOR -- given a variable pointed to by FIDP, parses any	*)
(*	  subscripts, fields references, or uparrows, collapsing	*)
(*	  constants where possible and generating code as necessary.	*)
(*	  A description of the address of the object is returned in	*)
(*	  Gattr.							*)
(*									*)
(*	In most cases, the final result will be a single simple 	*)
(*	object (e.g. REC.ARRAY1[I]^.J), but occasionally it will	*)
(*	be a whole complex object, as in the assignment statement	*)
(*		  ARRAY1 := ARRAY2;					*)
(*									*)
(************************************************************************)
procedure Selector (* Fsys : Setofsys; Fidp : Idp; var baseindir: Indirtype *);
	 				(* this tells whether the result of  *)
					(* the selector is in heap or not -  *)
					(* Fred Chow			     *)

  var
    I : integer;
    Found : boolean;
    Lattr, L2attr : Attr;
    Lidp : Idp;
    Parcount : integer;
    Parsingleft, Parsingright : boolean;
    Lstamp : integer;
    typep : Strp;

  procedure Addindex;

    var
      Lmin, Lmax, Indexvalue, Elementsize : integer;
      Elementsperword : Bitrange;
      Lowboundfolded : boolean;

    procedure Foldlowbound;
      (* Attempts to fold lowerbound of subscript into base address. Only    *)
      (* does this in easy cases					     *)
      begin
	Lowboundfolded := (Lattr.Kind = Varbl) and not (Lattr.Indexed)
	 and (Lattr.Indirect = Notind) and ((Elementsize >= Salign)
	 or (Salign mod Elementsize = 0)) and (Elementsize mod Addrunit = 0);
	if Lowboundfolded then begin
	  Lattr.Dplmt := Lattr.Dplmt-(Lmin*Elementsize);
	end;
      end {procedure Foldlowbound};

    procedure Sublowbound;
      (* Adjusts a subindex by the low bound of its type, checking the	     *)
      (* bounds if necessary. Tries to emit a zero lower bounds check, for   *)
      (* machines that have a check instruction of that format		     *)
      var
	Llmin, Llmax : integer;
      begin
	with Gattr do begin
	  if not Lowboundfolded then begin
	    if Lmin > 0 then begin
	      Uco2typint(Udec, Adtype, Lmin);
	    end else if Lmin < 0 then begin
	      Uco2typint(Uinc, Adtype, -Lmin);
	    end;
	  end;
	  if Runtimecheck then begin
	    Getbounds(Atypep, Llmin, Llmax);
	    if Llmin < Lmin then begin
	      if Lowboundfolded then begin
		Uco2typint(Uchkl, Adtype, Lmin);
	      end else begin
		Uco2typint(Uchkl, Adtype, 0);
	      end;
	    end;
	    if Llmax > Lmax then begin
	      if Lowboundfolded then begin
		Uco2typint(Uchkh, Adtype, Lmax);
	      end else begin
		Uco2typint(Uchkh, Adtype, Lmax-Lmin);
	      end;
	    end;
	  end;
	end {with};
      end {procedure Sublowbound};

    begin				(* addindex			     *)
      (* get next index 						     *)
      Lattr := Gattr;
      Indexvalue := 0;
      with Lattr do begin
	if (Atypep <> nil) and (Atypep^.Form <> Arrays) then begin
	  Error(307);
	  Atypep := nil;
	end;
      end {with};
      Insymbol;
      Expression(Fsys+[Commasy, Rbracksy]);
      if (Gattr.Atypep <> nil) and (Gattr.Atypep^.Form <> Scalar) then begin
	Error(403);
      end;
      Lmin := 0;
      Lmax := 0;
      Elementsize := Salign;
      if Lattr.Atypep <> nil then begin
	with Lattr.Atypep^ do begin
	  (* make sure index is right type and check value if possible	     *)
	  if Comptypes(Inxtype, Gattr.Atypep) then begin
	    Getbounds(Inxtype, Lmin, Lmax);
	    if Gattr.Kind = Cnst then begin
	      if (Gattr.Cval.Ival < Lmin) or (Gattr.Cval.Ival > Lmax) then
		begin
		Error(263);
	      end;
	    end;
	  end else begin
	    Error(457);
	  end;
	  Elementsize := Aelsize;
	end {with};
      end;
      (* if the subscript is a constant, try to calculate the address now    *)
      if Gattr.Kind = Cnst then begin
	Indexvalue := Gattr.Cval.Ival;
      end else if Gattr.Kind = Varbl then begin
	(* put it on stack, making sure the base address is loaded	     *)
	if Gattr.Indexed then begin
	  Load(Gattr);			(* resolve Gattr fully		     *)
	  if Lattr.Kind <> Expr then begin (* and then load Lattr	     *)
	    if Lattr.Indexed then begin
	      Swapstak;
	    end;
	    Foldlowbound;
	    Loadaddress(Lattr);
	    Swapstak;
	  end;
	end else begin
	  Foldlowbound;
	  Loadaddress(Lattr);
	  Load(Gattr);
	end;
	(* gattr = expr, already loaded 				     *)
      end else if not Lattr.Indexed then begin
	Foldlowbound;
	Loadaddress(Lattr);
	Swapstak;
      end else begin
	Lowboundfolded := false;
      end;
      if Lattr.Atypep <> nil then begin
	with Lattr.Atypep^ do begin
	  Lattr.Apacked := Arraypf;
	  Lattr.Asize := Aelsize;
	  (* change Lattr to be the type of the array element		     *)
	  Lattr.Atypep := Aeltype;
	  if Aeltype <> nil then begin
	    Lattr.Adtype := Aeltype^.Stdtype;
	  end else begin
	    Lattr.Adtype := Zdt;
	  end;
	end {with};
      end;
      (* combine this index with the current address on top of the stack or  *)
      (* generate code to do so 					     *)
      if Lattr.Atypep <> nil then begin
	if Gattr.Kind = Cnst then begin
	  if Elementsize > 0 then begin
	    Indexvalue := Indexvalue-Lmin;
	    if (Elementsize < Salign) and (Salign mod Elementsize > 0) then
	      begin			(* uneven packing		     *)
	      Elementsperword := Salign div Elementsize;
	      Lattr.Dplmt := Lattr.Dplmt
				+ (Indexvalue div Elementsperword)*Salign
				+ (Indexvalue mod Elementsperword)*Elementsize;
	    end else begin
	      Lattr.Dplmt := Lattr.Dplmt+Indexvalue*Elementsize;
	    end;
	  end;
	end else begin
	  Sublowbound;
	  Uco2typint(Uixa, Gattr.Adtype, Elementsize);
	end;
      end;
      Gattr := Lattr;
    end {procedure Addindex};

  begin 				(* Selector			     *)
    with Fidp^, Gattr do begin
      Atypep := Idtype;
      Kind := Varbl;
      Aclass := Klass;
      Indexed := false;
      Apacked := false;
      Subkind := nil;
      if Atypep <> nil then begin
	Adtype := Atypep^.Stdtype;
      end else begin
	Adtype := Zdt;
      end;
      (* first, put in GATTR a description of the variable parsed so far     *)
      case Klass of
      Vars : begin			(* variable			     *)
	  if Parseright then begin
	    Referenced := true;
	  end;
	  if Parseleft then begin
	    Assignedto := true;
	  end;
	  Ablock := Vblock;
	  if Vexternal then
	    st_fixextsc(Vblock, scUndefined);
	  Dplmt := Vaddr;
	  Amty := Vmty;
	  Baseaddress := Dplmt;
	  if Idtype = nil then begin
	    Asize := Intsize;
	  end else begin
	    if not Loopvar then
	      Asize := Idtype^.Stsize
	    else Asize := Loopvar_idtype^.Stsize;
	  end;
	  if Vkind = Formal then begin
	    Indirect := Aind;
	    Indexmt := Amty;
	    Indexr := Dplmt;
	    Dplmt := 0;
	  end else begin
	    Indirect := Notind;
	  end;
	end {case Vars};
      Field : begin			(* field of a record		     *)
	  (* get the address of the record from the display		     *)
	  with Display[Disx] do begin
	    if Occur = Crec then begin
	      Amty := Cmty;
	      Ablock := Mblock;
	      Ablock := Cblock;
	      Apacked := Inpacked;
	      Asize := Fieldsize;
	      Indexr := Cindexr;
	      Indirect := Cindirect;
	      Indexed := Cindexed;
	      Indexmt := Cindexmt;
	      Dplmt := Cdspl+Fldaddr;
	      Baseaddress := Dplmt;
	    end else begin
	      Error(171);
	    end;
	  end {with};
	end {case Field};
      Func : begin			(* function result		     *)
	  (* assignment to a function is only legal if the function is	     *)
	  (* currently active, which means it should be on the display	     *)
	  I := Top;
	  Found := false;
	  if Prockind = Regular then begin
	    while not Found and ((I > 2) or (I > 0) and (Progidp = nil))do begin
	      with Display[I] do begin
		Found := (Occur = Blck) and (Mblock = Pfmemblock);
	      end {with};
	      I := I-1;
	    end {while};
	  end;
	  if not Found then begin
	    Error(453);
	  end else begin
	    Indexr := 0;
	    Amty := Resmemtype;
	    Ablock := Pfmemblock;
	    Dplmt := Resaddr;
	    Baseaddress := Resaddr;
	    Fassigned := true;
	    Indirect := Notind;
	    if Atypep = nil then begin
	      Asize := Intsize;
	    end else begin
	      Asize := Atypep^.Stsize;
	    end;
	  end;
	end {case Func}
      end {case};
    end {with};
    Iferrskip(166, Selectsys+Fsys);

    (*************************************************************************)
    (* next, process any subscripts, uparrows, or field references	     *)
    (*************************************************************************)
    baseindir := Aind;
    while Sy in Selectsys do begin
      Gattr.Apacked := false;
      if Sy = Lbracksy then begin	(* [ : array subscripts 	     *)
	Parsingleft := Parseleft;
	Parsingright := Parseright;
	Parseleft := false;
	Parseright := true;
	(* load base address						     *)
	if Gattr.Indirect <> Notind then begin
	  Loadaddress(Gattr);
	end;
	repeat
	  Addindex;
	until Sy <> Commasy; (* for each subscript  *)
	if Sy = Rbracksy then begin	(* parse the right bracket	     *)
	  Insymbol;
	end else begin
	  Error(155);
	end;
	Parseleft := Parsingleft;
	Parseright := Parsingright;
      end else if Sy = Periodsy then begin (* . : fields of a record	     *)
	with Gattr do begin
	  Asize := Intsize;		(* in case of error		     *)
	  if Atypep <> nil then begin
	    if Atypep^.Form <> Records then begin
	      Error(308);
	      Atypep := nil;
	    end;
	  end;
	  Insymbol;
	  if Sy = Identsy then begin
	    if Atypep <> nil then begin
	      (* find the field in the symbol table			     *)
	      Searchsection(Atypep^.Recfirstfield, Lidp);
	      if Lidp = nil then begin
		Error(309);
		Atypep := nil;
	      end else begin
		with Lidp^ do begin
		  (* combine the field offset with whatever we have so far   *)
		  (* in Dplmt						     *)
		  Dplmt := Dplmt+Fldaddr;
		  Baseaddress := Dplmt;
		  Asize := Fieldsize;
		  Atypep := Idtype;
		  Apacked := Inpacked;
		  if Idtype <> nil then begin
		    Adtype := Idtype^.Stdtype;
		  end else begin
		    Adtype := Zdt;
		  end;
		end {with};
	      end;
	    end;
	    Insymbol;
	  end else begin
	    Error(209);
	  end;
	end {with};
      end else begin		(* sy = arrowsy ^ : pointers and files *)
	baseindir := Hind;		(* treat files as in heap	     *)
	if Gattr.Atypep <> nil then begin
	  with Gattr do begin
	    if not (Atypep^.Form in [SPointer, Files]) then begin
	      Error(407);
	    end else if Atypep^.Form = SPointer then begin
	      Load(Gattr);
	      Atypep := Atypep^.Eltype;
	      if Atypep <> nil then begin
		Adtype := Atypep^.Stdtype;
		Asize := Atypep^.Stsize;
	      end;
	      Indexed := true;
	      Dplmt := 0;
	      Kind := Varbl;
	      Aclass := Vars;
	      Apacked := false;
#if 0
	      (* check for nil pointer					     *)
	      if Runtimecheck or (Indirect in [Aind, Hind]) or Indexed then
		begin 
		Loadaddress(Gattr);
#if 0
		if Runtimecheck then begin
		  Uco0(Uchkn);
		end;
#endif
		Indexed := true;
	      end;
#endif
	      Fidp^.Referenced := true;
	    end else if not Atypep^.Textfile or Parseleft then begin
	      (* Atypep^.Form = files					     *)
	      (* Load the address of the buffer 			     *)
	      typep := Atypep;
	      Dplmt := Dplmt + File_stdio_offset;
	      Asize := Pointersize;
	      Atypep := Addressptr;
	      Adtype := Adt;
	      Load(Gattr);
	      Atypep := Addressptr;
	      Adtype := Adt;
	      Asize := Pointersize;
	      Indexed := true;
	      Dplmt := 1*Wordsize;		(* see stdio.h *)
	      Kind := Varbl;
	      Aclass := Vars;
	      Apacked := false;
	      Atypep := Addressptr;
	      Load(Gattr);
	      Apacked := {typep^.Filepf}false;
	      Asize := typep^.Componentsize;
	      Atypep := typep^.Filetype;
	      if Atypep <> nil then begin
		Adtype := Atypep^.Stdtype;
	      end;
	      Indexed := true;
	      Dplmt := 0;
	      Kind := Varbl;
	      Aclass := Vars;
	    end else begin
	      (* Call standard procedure peek_char to get the value of the   *)
	      (* buffer 						     *)
	      Dplmt := Dplmt + File_stdio_offset;
	      Asize := Pointersize;
	      Atypep := Addressptr;
	      Adtype := Adt;
	      Lstamp := 0;
	      if Kind = Expr then begin
		Getatemp(Lattr, Addressptr, Lstamp, false);
		L2attr := Lattr;
		Store(Lattr);
		Gattr := L2attr;
	      end;
	      Stdcallinit(Parcount);
	      Load(Gattr);
	      Par(Adt, Parcount);
	      Support(Peekchar);
	      if Lstamp > 0 then begin
		Freetemps(Lstamp);
	      end;
	      Kind := Expr;
	      Atypep := Charptr;
	    end;
	  end {with};
	end;

	Insymbol;
      end;
      Iferrskip(166, Fsys+Selectsys);
    end {while};
    with Gattr do begin
      if Atypep <> nil then begin
	Adtype := Atypep^.Stdtype;
      end;
    end {with};
  end {procedure Selector};

(*Loadboth,Matchtypes,Matchtoassign,Makereal,Loadandcheckbounds*)
(************************************************************************)
(*									*)
(*	LOADBOTH -- generates code to load two items on the stack	*)
(*									*)
(*	Neither or one or both items may be already loaded on the	*)
(*	   stack, or already partially loaded on the stack (e.g.,	*)
(*	   its address may be on the stack but not the item itself.	*)
(*	   This procedure generates code to get them both fully 	*)
(*	   loaded, and in the right order.				*)
(*									*)
(************************************************************************)
procedure Loadboth /* ( var Fattr : Attr)  */;

#if 0
  function Realtype (
	     Lattr : Attr)
     : Datatype;
    begin

      with Lattr.Atypep^ do begin
	if (Stdtype = Mdt) then begin
	  Realtype := Adt;
	end else begin
	  Realtype := Lattr.Adtype;
	end;
      end {with};
    end {function Realtype};
#endif

  begin
    with Gattr do begin
      if Fattr.Kind = Expr then begin	(* first one on the stack. push      *)
					(* second			     *)
	if Kind <> Expr then begin
	  Load(Gattr);
	end;
      end else if Kind = Expr then begin (* second one on the stack. push    *)
					(* first and swap		     *)
	if (Fattr.Kind = Varbl) and Fattr.Indexed then begin
	  Swapstak;
	end;
	Load(Fattr);
	Swapstak;
      end else if (Kind = Varbl) and Indexed then begin (* second one	     *)
					(* indexed by the stack. load, push, *)
					(* swap 			     *)
	Load(Gattr);
	if (Fattr.Kind = Varbl) and Fattr.Indexed then begin
	  Swapstak;
	end;
	Load(Fattr);
	Swapstak;
      end else begin			(* neither is in any way referred to *)
					(* in the stack 		     *)
	Load(Fattr);
	Load(Gattr);
      end;
    end {with};
  end {procedure Loadboth};


(************************************************************************)
(*									*)
(*	MATCHTYPES  -- matches the types of Fattr and Gattr		*)
(*	    according to the following rules, in rigorous order:	*)
(*									*)
(*     1. if they are already matched, noop.				*)
(*     2. if any of them is not integer nor real, noop. 		*)
(*     3. if one is type Q (double), convert the other.			*)
(*     4. if one is type R (real), convert the other.			*)
(*     5. if one is type L (positive integer), convert it to the other. *)
(*									*)
(************************************************************************)


procedure Matchtypes /* ( var Fattr : Attr)  */;
  begin
    if (Fattr.Adtype <> Gattr.Adtype)
     and (Gattr.Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt])
     and (Fattr.Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) then begin
      Loadboth(Fattr);
      if Gattr.Adtype = Xdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Xdt, Fattr.Adtype);
	Swapstak;
	Fattr.Atypep := Extendedptr;
      end else if Fattr.Adtype = Xdt then begin
	Uco2typtyp(Ucvt, Xdt, Gattr.Adtype);
	Gattr.Atypep := Extendedptr;
      end else if Gattr.Adtype = Qdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Qdt, Fattr.Adtype);
	Swapstak;
	Fattr.Atypep := Doubleptr;
      end else if Fattr.Adtype = Qdt then begin
	Uco2typtyp(Ucvt, Qdt, Gattr.Adtype);
	Gattr.Atypep := Doubleptr;
      end else if Gattr.Adtype = Rdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Rdt, Fattr.Adtype);
	Swapstak;
	Fattr.Atypep := Realptr;
      end else if Fattr.Adtype = Rdt then begin
	Uco2typtyp(Ucvt, Rdt, Gattr.Adtype);
	Gattr.Atypep := Realptr;
      end else if (Gattr.Adtype = Ldt) and (Fattr.Adtype = Jdt) then begin
	Uco2typtyp(Ucvt, Fattr.Adtype, Gattr.Adtype);
	if Fattr.Atypep <> nil then {this check is for in case of error only}
	  Gattr.Atypep := Fattr.Atypep;
      end else if (Fattr.Adtype = Ldt) and (Gattr.Adtype = Jdt) then begin
	Swapstak;
	Uco2typtyp(Ucvt, Gattr.Adtype, Fattr.Adtype);
	Swapstak;
	Fattr.Atypep := Gattr.Atypep;
      end;

      Fattr.Adtype := Gattr.Atypep^.Stdtype;
      Gattr.Adtype := Gattr.Atypep^.Stdtype;
    end;
  end {procedure Matchtypes};


procedure Matchtoassign /* ( var Fattr : Attr; Ftypep : Strp)  */;

  (***************************************************************************)
  (* Matches the type of Fattr to Ftypep. Fattr.Kind should be Expr	     *)
  (***************************************************************************)

  var
    Ldtype : Datatype;

  begin 				(* matchtoassign		     *)
    if Ftypep <> nil then begin
      with Ftypep^, Fattr do begin
	if Stdtype <> Adtype then begin
#if 0
	  if Stdtype in [Rdt, Qdt, Xdt] then begin
	    Uco2typtyp(Ucvt, Stdtype, Adtype);
	  end else if (Adtype in [/*Bdt, Cdt,*/ Jdt, Ldt])
		and (Stdtype in [/*Bdt, Cdt,*/ Jdt, Ldt]) then begin
	      Uco2typtyp(Ucvt, Stdtype, Adtype);
	  end else begin		(* convert required		     *)
	    if Stdtype in [Jdt, Ldt] then begin
	      Ldtype := Stdtype;
	    end else begin
	      Ldtype := Jdt;
	    end;
	    Uco2typtyp(Ucvt, Ldtype, Adtype);
	    if Ldtype <> Stdtype then begin
	      Uco2typtyp(Ucvt, Stdtype, Jdt);
	    end;
	  end;
#else
	  Uco2typtyp(Ucvt, Stdtype, Adtype);
#endif
	  Atypep := Ftypep;
	  Adtype := Stdtype;
	end;
      end {with};
    end;
  end {procedure Matchtoassign};

procedure Makereal (
	var Fattr : Attr);
  (* same as Matchtypes, but the result MUST be real, even if both Fattr and *)
  (* Gattr are of type integer (used for real divide)			     *)

  begin 				(* makereal			     *)
#if 0
    with Gattr do begin
      if ((Fattr.Adtype <> Rdt) or (Adtype <> Rdt))
       and (Fattr.Adtype in [Jdt, Ldt, Rdt])
       and (Adtype in [Jdt, Ldt, Rdt]) then begin
	Loadboth(Fattr);
	(* will make it type r						     *)
	if Adtype <> Rdt then begin
	  Uco2typtyp(Ucvt, Rdt, Adtype);
	  Adtype := Rdt;
	  Atypep := Realptr;
	end;
	if Fattr.Adtype <> Rdt then begin
	  Swapstak;
	  Uco2typtyp(Ucvt, Rdt, Fattr.Adtype);
	  Swapstak;
	  Fattr.Adtype := Rdt;
	  Fattr.Atypep := Realptr;
	end;
      end;
    end {with};
#else
    if not ((Gattr.Adtype in [Rdt, Qdt, Xdt])
	    or (Fattr.Adtype in [Rdt, Qdt, Xdt])) then begin
      Loadboth(Fattr);
      Uco2typtyp(Ucvt, Qdt, Gattr.Adtype);
      Gattr.Adtype := Qdt;
      Gattr.Atypep := Doubleptr;
      Swapstak;
      Uco2typtyp(Ucvt, Qdt, Fattr.Adtype);
      Swapstak;
      Fattr.Adtype := Qdt;
      Fattr.Atypep := Doubleptr;
    end else if Gattr.Adtype <> Fattr.Adtype then begin
      Loadboth(Fattr);
      if Gattr.Adtype = Xdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Xdt, Fattr.Adtype);
	Swapstak;
	Fattr.Adtype := Xdt;
	Fattr.Atypep := Extendedptr;
      end else if Fattr.Adtype = Xdt then begin
	Uco2typtyp(Ucvt, Xdt, Gattr.Adtype);
	Gattr.Adtype := Xdt;
	Gattr.Atypep := Extendedptr;
      end else if Gattr.Adtype = Qdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Qdt, Fattr.Adtype);
	Swapstak;
	Fattr.Adtype := Qdt;
	Fattr.Atypep := Doubleptr;
      end else if Fattr.Adtype = Qdt then begin
	Uco2typtyp(Ucvt, Qdt, Gattr.Adtype);
	Gattr.Adtype := Qdt;
	Gattr.Atypep := Doubleptr;
      end else if Gattr.Adtype = Rdt then begin
	Swapstak;
	Uco2typtyp(Ucvt, Rdt, Fattr.Adtype);
	Swapstak;
	Fattr.Adtype := Rdt;
	Fattr.Atypep := Realptr;
      end else if Fattr.Adtype = Rdt then begin
	Uco2typtyp(Ucvt, Rdt, Gattr.Adtype);
	Gattr.Adtype := Rdt;
	Gattr.Atypep := Realptr;
      end;
    end;
#endif
  end {procedure Makereal};

procedure Loadandcheckbounds /* ( var Fattr : Attr; Fboundtypep : Strp)  */;

  (***************************************************************************)
  (* Loads Fattr and makes sure it is within the bounds of Fboundtypep^      *)
  (***************************************************************************)

  var
    Bmin, Bmax, Cmin, Cmax : integer;

  begin 				(* loadandcheckbounds		     *)
    if Fboundtypep <> nil then begin
      Getbounds(Fboundtypep, Cmin, Cmax);
      with Fattr do begin
	if Kind = Cnst then begin
	  with Cval do begin
	    if Adtype in [ /* Bdt, Cdt,  */Jdt, Ldt] then begin
	      if (Ival < Cmin) or (Ival > Cmax) then begin
		Error(367);
	      end;
	    end;
	  end {with};
	  Load(Fattr);
	  Matchtoassign(Fattr, Fboundtypep);
	  (* this could be improved by matching before loading		     *)
	end else begin			(* kind in [varbl,expr] 	     *)
	  Load(Fattr);
	  Matchtoassign(Fattr, Fboundtypep);
	  if Runtimecheck and ((Kind <> Varbl)
	   or (Subkind <> Fboundtypep)) then begin
	    Getbounds(Atypep, Bmin, Bmax);
	    if Bmin < Cmin then begin
	      Uco2typint(Uchkl, Adtype, Cmin);
	    end;
	    if Bmax > Cmax then begin
	      Uco2typint(Uchkh, Adtype, Cmax);
	    end;
	  end;
	end;
      end {with};
    end;
  end {procedure Loadandcheckbounds};

(*Shiftset,Matchsets,Adjtosetoffset,Setmatchtoassign*)
(************************************************************************)
(*									*)
(*	SET ADJUSTING PROCEDURES					*)
(*									*)
(*	For any set operations, the size and lower offset of the	*)
(*	set or sets involved must be taken into account.  These 	*)
(*	procedures are involved with that.				*)
(*									*)
(*	SHIFTSET -- does the equivalent of an ADJ on a constant set	*)
(*	MATCHSETS -- matches two sets before doing a binary operation	*)
(*	  on them							*)
(*	SETMATCHTOASSIGN -- adjusts the set on top of the stack to	*)
(*	  correspond to the set variable it will be assigned to 	*)
(*	ADJTOSETOFFSET -- adjusts a scalar to conform to a lower offset *)
(*	  of a set before an INN opeation				*)
(*									*)
(************************************************************************)
procedure Shiftset (*
	var Setval : Valu;
	    Shift,
	    Finallength : integer *);

  (***************************************************************************)
  (* shifts a set constant						     *)
  (***************************************************************************)

  var
    I : integer;
  begin
    with Setval do begin
      Shift := Shift div 4;
      Finallength := Finallength div 4;
      if lsb_first then begin
	Shift := -Shift + Finallength - Ival;
      end;
      if Shift > 0 then begin
	(* shift up							     *)
	for I := Ival downto 1 do begin
	  Chars^.ss[I+Shift] := Chars^.ss[I];
	end {for};
	for I := 1 to Shift do begin
	  Chars^.ss[I] := '0';
	end {for};
      end else if Shift < 0 then begin
	(* shift down							     *)
	Shift := -Shift;
	for I := 1 to Ival-Shift do begin
	  Chars^.ss[I] := Chars^.ss[I+Shift];
	end {for};
	for I := max(Ival-Shift+1, 1) to Ival do begin
	  Chars^.ss[I] := '0';
	end {for};
      end;
      Ival := Finallength;
    end {with};
  end {procedure Shiftset};

procedure Matchsets (
	var Fattr : Attr);

  (***************************************************************************)
  (* adjusts the sets represented by FATTR and GATTR to have the same offset *)
  (* and length 							     *)
  (***************************************************************************)

  var
    Hmin, Hmax, Smin, Smax, Setsize : integer; (* characteristics of new set *)
    Gadj, Fadj : boolean;		(* Do Gattr, Fattr need to be	     *)
					(* adjusted?			     *)
    Gadjusted, Fadjusted : boolean;	(* Flags partial adjustment	     *)
    Toolarge : boolean;

  begin
    if (Gattr.Atypep <> nil) and (Fattr.Atypep <> nil)
     and (Gattr.Atypep <> Fattr.Atypep) then begin (* adjust sets	     *)
      if Fattr.Apacked then begin
	Load(Fattr);
	Fattr.Asize := Fattr.Atypep^.Stsize;
      end;
      if Gattr.Apacked then begin
	Load(Gattr);
	Gattr.Asize := Gattr.Atypep^.Stsize;
      end;
      (* find the new hard min and max					     *)
      Hmin := Min(Fattr.Atypep^.Hardmin, Gattr.Atypep^.Hardmin);
      Hmax := Max(Fattr.Atypep^.Hardmax, Gattr.Atypep^.Hardmax);
      Toolarge := false;
      (* this next check must be done carefully, since Hmin can be MAXINT    *)
      (* while Hmin is MININT						     *)
      if Hmin < Hmax then begin
	if Hmax-Hmin+1 > Maxsetsize then begin
	  Error(177);
	  Toolarge := true;
	end;
      end;
      if not Toolarge then begin	(* not too big			     *)
	(* find the new soft min and max				     *)
	Smin := Min(Fattr.Atypep^.Softmin, Gattr.Atypep^.Softmin);
	(* make sure SMIN is large enough so that resulting set will be big  *)
	(* enough to hold HMAX without exceeding the max possible length     *)
	if Hmax > Smin then begin
	  if Hmax-Smin+1 > Maxsetsize then begin
	    Smin := Hmax-Maxsetsize+1;
	  end;
	end;
	Smax := Max(Fattr.Atypep^.Softmax, Gattr.Atypep^.Softmax);
	(* make sure SMAX is small enough so that resulting set won't be too *)
	(* big								     *)
	if Smax-Smin+1 > Maxsetsize then begin
	  Smax := Smin+Maxsetsize-1;
	end;
	Setsize := Smax-Smin+1;
	with Fattr.Atypep^ do begin	(* if Fattr is a constant and needs  *)
					(* adjusting, do it		     *)
	  Fadj := (Smin-Softmin <> 0) or (Setsize-Fattr.Asize <> 0);
	  if Fadj and (Fattr.Kind = Cnst) then begin
	    Shiftset(Fattr.Cval, Softmin-Smin, Setsize);
	    Stsize := Setsize;
	    Fattr.Asize := Setsize;
	    Fadjusted := true;
	  end else begin
	    Fadjusted := false;
	  end;
	end {with};
	with Gattr.Atypep^ do begin	(* if Gattr is a constant and needs  *)
					(* adjusting, do it		     *)
	  Gadj := (Smin-Softmin <> 0) or (Setsize-Gattr.Asize <> 0);
	  if Gadj and (Gattr.Kind = Cnst) then begin
	    Shiftset(Gattr.Cval, Softmin-Smin, Setsize);
	    Stsize := Setsize;
	    Gattr.Asize := Setsize;
	    Gadjusted := true;
	  end else begin
	    Gadjusted := false;
	  end;
	end {with};
	if (Fadj and not Fadjusted) or (Gadj and not Gadjusted) then begin
					(* emit code for runtime Adjust      *)
	  Loadboth(Fattr);
	  if Gadj and not Gadjusted then begin
	    if Runtimecheck then begin
	      if (Smin > Gattr.Atypep^.Softmin) then begin
		Uco2typint(Uchkl, Sdt, Smin-Gattr.Atypep^.Softmin);
	      end;
	      if Setsize < Gattr.Atypep^.Stsize then begin
		Uco2typint(Uchkh, Sdt, Setsize);
	      end;
	    end;
	    Uco3int(Uadj, Sdt, Setsize, Gattr.Atypep^.Softmin-Smin);
	  end;
	  if Fadj and not Fadjusted then begin
	    Swapstak;
	    if Runtimecheck then begin
	      if (Smin > Fattr.Atypep^.Softmin) then begin
		Uco2typint(Uchkl, Sdt, Smin-Fattr.Atypep^.Softmin);
	      end;
	      if Setsize < Fattr.Atypep^.Stsize then begin
		Uco2typint(Uchkh, Sdt, Setsize);
	      end;
	    end;
	    Uco3int(Uadj, Sdt, Setsize, Fattr.Atypep^.Softmin-Smin);
	    Swapstak;
	  end;
	end;
	if Gadj then begin
	  (* update GATTR.Atypep to describe set now on top		     *)
	  if not Fadj then begin
	    Gattr.Atypep := Fattr.Atypep;
	  end else begin		(* create new Structure to describe  *)
					(* set				     *)
	    new2(Gattr.Atypep, Power);
	    with Gattr.Atypep^ do begin
	      Basetype := Fattr.Atypep^.Basetype;
	      Stsize := Setsize;
	      Stsize := Setsize;
	      Form := Power;
	      Stdtype := Sdt;
	      ifd := -1;
	      packifd := -1;
	      Wheredeclared := Memblock;
	      Hasfiles := false;
	      Hasholes := false;
	      Softmin := Smin;
	      Softmax := Smax;
	      Hardmin := Hmin;
	      Hardmax := Hmax;
	    end {with};
	  end;
	end;
	if Fadj then begin
	  Fattr.Atypep := Gattr.Atypep;
	end;
	Fattr.Asize := Setsize;
	Gattr.Asize := Setsize;
      end;				(* if not too big		     *)
    end;				(* adjust sets			     *)
  end {procedure Matchsets};

procedure Adjtosetoffset (
	var Fattr : Attr;
	    Smin : integer);
  (* Increments or decrements the integer described in Fattr to conform to a *)
  (* set whose offset is Smin						     *)

  begin
    if Fattr.Kind = Cnst then begin
      Fattr.Cval.Ival := Fattr.Cval.Ival-Smin;
    end else begin
      if Smin > 0 then begin
	Uco2typint(Udec, Fattr.Adtype, Smin);
      end else if Smin < 0 then begin
	Uco2typint(Uinc, Fattr.Adtype, -Smin);
      end;
    end;
  end {procedure Adjtosetoffset};

procedure Setmatchtoassign /* ( var Fattr : Attr; Ftypep : Strp; Spacked :   */
					/* boolean)  */;

  (***************************************************************************)
  (* adjusts the set in Fattr to have the same size and offset as the one    *)
  (* described by Ftypep						     *)
  (***************************************************************************)

  var
    Shift : integer;
  begin
    if (Ftypep <> nil) and (Fattr.Atypep <> nil) then begin
      with Fattr.Atypep^ do begin
	Shift := Softmin-Ftypep^.Softmin;
	if (Shift <> 0) or (Ftypep^.Stsize <> Stsize) then begin
	  if Fattr.Kind = Cnst then begin
	    Shiftset(Fattr.Cval, Shift, Ftypep^.Stsize);
	  end else begin
	    Load(Fattr);
	    if Runtimecheck then begin
	      if Shift < 0 then begin
		Uco2typint(Uchkl, Sdt, -Shift);
	      end;
	      if Ftypep^.Softmax < Softmax then begin
		Uco2typint(Uchkh, Sdt, Ftypep^.Softmax);
	      end;
	    end;
	    Uco3int(Uadj, Sdt, Ftypep^.Stsize, Shift);
	  end;
	end;
      end {with};
      Fattr.Atypep := Ftypep;
      if Ftypep <> nil then begin
	Fattr.Asize := Ftypep^.Stsize;
      end;
    end;
  end {procedure Setmatchtoassign};

(*Generatecode*)
(************************************************************************)
(*									*)
(*	GENERATECODE  -- Generates code to perform an operation.	*)
(*									*)
(************************************************************************)
procedure Generatecode (
	    Finstr : Uopcode;
	    Fdtype : Datatype;
	var Fattr : Attr);

  var
    Lmin, Lmax : integer;
    Checkbounds : boolean;

  begin 				(* generatecode 		     *)
    with Gattr do begin
      if Finstr <> Uneg then begin
	Loadboth(Fattr);
	if ((Finstr = Udif) or (Finstr = Uint) or (Finstr = Uuni)
	 or (Finstr = Uinn)) and (Atypep <> nil) then begin
	  if (Finstr = Uinn) and (Fattr.Atypep <> nil) then begin
	    (* if the subrange of the variable is within the bounds of the   *)
	    (* set, then indicate (in the U-code) that a test-if-	     *)
	    (* within-bounds must be done				     *)
	    case Fattr.Kind of
	    Expr : Checkbounds := true;
	    Cnst :
		Checkbounds := (Fattr.Cval.Ival < Atypep^.Softmin) or (Fattr.
		    Cval.Ival > Atypep^.Softmax);
	    Varbl : begin
		if Fattr.Subkind <> nil then begin
		  Getbounds(Fattr.Subkind, Lmin, Lmax);
		end else begin
		  Getbounds(Fattr.Atypep, Lmin, Lmax);
		end;
		Checkbounds := (Lmin < Atypep^.Softmin)
		 or (Lmax > Atypep^.Softmax);
	      end {case Varbl};
	    end {case};
	    Uco3int(Finstr, Fdtype, Atypep^.Stsize, ord(Checkbounds));
	  end else begin
	    Uco2typint(Finstr, Fdtype, Atypep^.Stsize);
	  end;
	end else begin
	  Uco1type(Finstr, Fdtype);
	end;
      end else begin			(* negating single expression	     *)
	if (Fattr.Kind = Cnst) and (Kind = Cnst) and 
	        (Adtype <> Rdt) and ( not(Doubleonly and (Adtype = Qdt)) ) then
	  begin
	  with Cval do begin
	    Ival := -Ival;
	    if Ival >= 0 then begin
	      Adtype := Ldt;
	    end else begin
	      Adtype := Jdt;
	    end;
	  end {with};
	end else begin
	  if Fattr.Kind <> Expr then begin
	    Load(Fattr);
	  end;
	  (* make sure type is not positive-only			     *)
	  if Fattr.Adtype = Ldt then begin
	    Uco2typtyp(Ucvt, Jdt, Ldt);
	    Fattr.Adtype := Jdt;
	  end;
	  Uco1type(Finstr, Fattr.Adtype);
	end;
      end;
    end {with};
  end {procedure Generatecode};





(*Setconst[Setelement,Setpart]*)
(****************************************************************)
(****************************************************************)
(*								*)
(*	EXPRESSION MODULE -- parses and generates code for	*)
(*	   expression.	A variable or constant is generally	*)
(*	   not loaded until something is done with it, i.e.	*)
(*	   an operation is performed on it or it is assigned	*)
(*	   to something.					*)
(*	A description of the expression, variable, or constant	*)
(*	   parsed is returned in the global variable GATTR.	*)
(*								*)
(*	Contains the following procedures, each of which calls	*)
(*	   the one below it:					*)
(*								*)
(*	   Expression						*)
(*	   Simpleexpression					*)
(*	   Term 						*)
(*	   Factor						*)
(*	   Setconstant						*)
(*								*)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(*								*)
(*	SETCONSTANT -- parses a set constant			*)
(*								*)
(*   A set constant consists of a list of set parts, each of	*)
(*   which is a single set element or a range of elements.	*)
(*   A set part can be either constant or variable:		*)
(*								*)
(*   Example of constant parts:  3, 6*8, 1..5			*)
(*   Example of variable parts:  I, J*8, 1..K, J..K		*)
(*								*)
(*   The constant parts are combined in a TARGETSET, which is	*)
(*   an array of host sets.  For each variable part, code to	*)
(*   load it on the stack and to combine it with previous	*)
(*   variable parts is generated.  As each new part is read,	*)
(*   the lower bound and the set size must be figured out, and	*)
(*   appropriate actions to make previous parts conform to this *)
(*   new lower bound and set size must be taken.  The lower	*)
(*   bound and upper bounds must be at least as low and high as *)
(*   the minimum and maximum constants read so far.  In 	*)
(*   addition, they are adjusted to accomodate the varible	*)
(*   parts insofar as possible.  If the variable part is a	*)
(*   single variable of type subrange, then its lower and upper *)
(*   bounds can be used in the calculations;  otherwise, a	*)
(*   default lower and upper bound is used.			*)
(*								*)
(*   Contains procedures:					*)
(*								*)
(*	Setelement: parses a single set element or range part	*)
(*	Setpart:    parses a single set part			*)
(*								*)
(*   Calls procedures:						*)
(*								*)
(*	Expression: to get next set element			*)
(*	Shiftset:   to shift constant part of set		*)
(*								*)
(****************************************************************)
procedure Setconst (
	    Fsys : Setofsys);

  var
    Minc, Maxc, 			(* highest and lowest constants so   *)
					(* far				     *)
    Minlowbound, Maxhighbound,		(* highest and lowest subranges so   *)
					(* far				     *)
    Setmin, Setmax, Setsize,		(* current set min, max, and size    *)
    Lowval, Highval,			(* low and high value of current     *)
					(* constant set part		     *)
    Pmin, Pmax, 			(* low and high bound of current set *)
					(* part 			     *)
    Varsetsize, Varsetmin,		(* min and size of last set for      *)
					(* which code has been emmited	     *)
    Constsetmin : integer;		(* min of constant set		     *)
    Cstpart : Valu;			(* current constant part of the set, *)
					(* represented by an array of host   *)
					(* sets 			     *)
    Gotexpr,				(* true if not-constant set part has *)
					(* been read			     *)
    Gotconst,				(* true if constant set part has     *)
					(* been read			     *)
    Indexed, Isrange, Loopdone : boolean;
    Lstrp : Strp;			(* points to structure of set	     *)
					(* elements			     *)
    I, J, K, Shift : integer;
    Lattr : Attr;

  procedure Setelement (
	  var Minv,
	      Maxv : integer);

    (*************************************************************************)
    (* gets the next set element or part of a subrange; if this element is a *)
    (* constant, its value is returned in MINV and MAXV; else if it is a     *)
    (* variable of type subrange, then code is generated to load it and MINV *)
    (* and MAXV contain the subrange; else (it is a variable of type integer *)
    (* or an expression), it is loaded and MINV and MAXV are set to default  *)
    (* values								     *)
    (*************************************************************************)

    begin
      Minv := 0;
      Maxv := Defsetsize-1;
      Expression(Fsys+[Commasy, Rbracksy, Rangesy]);
      with Gattr do begin
	if Atypep <> nil then begin
	  if (Atypep^.Form <> Scalar) or (Atypep = Realptr)
	   or (Atypep = Doubleptr) or (Atypep = Extendedptr) then begin
	    Error(461);
	    Atypep := nil;
	  end else begin		(* legitimiate set type 	     *)
	    if Lstrp = nil then begin
	      Lstrp := Atypep;
	    end;			(* first set element		     *)
	    (* make sure is compatible with previous set elements	     *)
	    if not Comptypes(Lstrp, Atypep) then begin
	      Error(360);
	    end else if Kind = Cnst then begin
	      Minv := Cval.Ival;
	      Maxv := Cval.Ival;
	    end else if (Kind = Expr) and is_constant(stak^.tree) then begin
	      Kind := Cnst;
	      Cval.Ival := stak^.tree^.u.constval.ival;
	      Popstak;
	      Minv := Cval.Ival;
	      Maxv := Cval.Ival;
	    end else if Kind = Varbl then begin
	      Load(Gattr);
	      if Subkind <> nil then begin
		Minv := Subkind^.Vmin;
		Maxv := Subkind^.Vmax;
	      end else if (Atypep <> nil)
		  and (Atypep^.Form = Scalar)
		  and (Atypep^.Scalkind = Declared) then begin
		Minv := 0;
		Maxv := Atypep^.Dimension;
	      end;
	    end;
	  end;
	end;
      end {with};
    end {procedure Setelement};

  procedure Setpart (
	  var Pmin,
	      Pmax,
	      Lowval,
	      Highval : integer;
	  var Indexed,
	      Isrange : boolean);
    (* gets a set element or subrange; on return from this procedure, PMIN   *)
    (* is the smallest possible value for this part (may be a guess; will    *)
    (* always be a multiple of Setunitsize) PMAX is the largest possible     *)
    (* value for this part (ditto) LOWVAL is the actual lowest value, if     *)
    (* this part is constant HIGHVAL is the actual highest value, if this    *)
    (* part is constant INDEXED is true if code has been generated (a	     *)
    (* non-constant set part has been read) ISRANGE is true if the set part  *)
    (* read is a range rather than a single expression			     *)

    var
      Tmin, Tmax : integer;

    begin
      Setelement(Pmin, Pmax);
      Isrange := Sy = Rangesy;
      if not Isrange then begin
	Indexed := (Gattr.Kind <> Cnst);
	if not Indexed then begin
	  Pmax := Pmin;
	end;
      end else begin			(* parse second part of range	     *)
	Lattr := Gattr;
	Insymbol;
	Setelement(Tmin, Tmax);
#if 0
	Pmin := Min(Pmin, Tmin);
	Pmax := Max(Pmax, Tmax);
#else
	Pmax := Tmax;
#endif
	(* if one or the other is on the stack, make sure both are	     *)
	if Gattr.Kind = Cnst then begin
	  Indexed := (Lattr.Kind <> Cnst);
	  if Indexed then begin
	    Load(Gattr);
	  end;
	end else begin
	  Indexed := true;
	  if Lattr.Kind = Cnst then begin
	    Load(Lattr);
	    Swapstak;
	  end;
	end;
      end;
      Lowval := Pmin;
      Highval := Pmax;
      if Pmin mod Setunitsize <> 0 then begin
	Pmin := (Pmin div Setunitsize)*Setunitsize;
	(* this kludge is necessary because stupid old Pascal doesn't        *)
	(* truncate towards -maxint					     *)
	if Lowval < 0 then begin
	  Pmin := Pmin-Setunitsize;
	end;
      end;
      if Pmax mod Setunitsize+1 <> 0 then begin
	Pmax := abs(Pmax);
	Pmax := (Pmax div Setunitsize+1)*Setunitsize-1;
	if Highval < 0 then begin
	  Pmax := Pmax-Setunitsize;
	end;
      end;
    end {procedure Setpart};

  begin 				(* SETCONST			     *)
    Minc := maxint;
    Maxc := -maxint;
    Minlowbound := maxint;
    Maxhighbound := -maxint;
    Setmin := maxint;
    Setmax := -maxint;
    Setsize := 0;
    Gotexpr := false;
    Gotconst := false;
    Loopdone := false;
    Lstrp := nil;
    new1(Cstpart.Chars);
    Insymbol;
    if Sy <> Rbracksy then begin
      repeat				(* add next set part to set	     *)
	Setpart(Pmin, Pmax, Lowval, Highval, Indexed, Isrange);
	if not Indexed then begin	(* add constant to set		     *)
	  if Lowval <= Highval then begin
	    (* find the min and max constant so far			     *)
	    Minc := Min(Minc, Pmin);
	    Maxc := Max(Maxc, Highval);
	    (* check to see if range is too great 			     *)
	    if Maxc-Minc+1 > Maxsetsize then begin
	      Error(177);
	      Setmin := 0;
	      Setmax := Defsetsize-1;
	      Setsize := Defsetsize;
	    end else begin		(* not out of range		     *)
	      (* adjust SETMIN and SETMAX if necessary			     *)
	      if Minc < Setmin then begin
		Setmin := Pmin;
		if Setmax > Setmin then begin
		  if Setmax-Setmin+1 > Maxsetsize then begin
		    Setmax := Setmin+Maxsetsize-1;
		  end;
		end;
	      end;
	      if Maxc > Setmax then begin
		Setmax := Pmax;
		if Setmax-Setmin+1 > Maxsetsize then begin
		  Setmin := Setmax-Maxsetsize+1;
		end;
	      end;
	      Setsize := Setmax-Setmin+1;
	      (* add to set const 					     *)
	      if not Gotconst then begin
		Cstpart.ival := Emptytargetset.ival;
		Cstpart.chars^ := Emptytargetset.chars^;
		Constsetmin := 0;
	      end;
	      (* shift existing set constant				     *)
	      Shiftset(Cstpart, Constsetmin-Setmin, Setsize);
	      (* set Lowval through Highval in the set			     *)
	      for I := Lowval-Setmin to Highval-Setmin do begin
		with Cstpart do begin
		  if lsb_first then begin
		    J := (Setsize-1-I) div 4;
		    K := ord(Chars^.ss[J+1])-ord('0');
		    if K > 9 then begin
		      K := K-(ord('A')-ord('9')-1);
		    end;
		    K := bitor(K, lshift(1, I mod 4));
		    if K > 9 then begin
		      K := K+(ord('A')-ord('9')-1);
		    end;
		    Chars^.ss[J+1] := chr(K+ord('0'));
		  end else begin
		    J := I div 4;
		    K := ord(Chars^.ss[J+1])-ord('0');
		    if K > 9 then begin
		      K := K-(ord('A')-ord('9')-1);
		    end;
		    K := bitor(K, lshift(1, 3-(I mod 4)));
		    if K > 9 then begin
		      K := K+(ord('A')-ord('9')-1);
		    end;
		    Chars^.ss[J+1] := chr(K+ord('0'));
		  end;
		end {with};
	      end {for};
	    end;			(* not out of range		     *)
	    Gotconst := true;
	    Constsetmin := Setmin;
	    Cstpart.Ival := (Setmax-Setmin+1) div 4;
	  end;
	end else begin			(* add variable to set		     *)
	  (* adjust SETMIN and SETMAX					     *)
	  Minlowbound := Min(Minlowbound, Pmin);
	  if Minlowbound < Setmin then begin
	    (* only set SETMIN to MINLOWBOUND if resulting set will be big   *)
	    (* enough to hold HAXC					     *)
	    if Maxc = -maxint then begin
	      Setmin := Minlowbound;
	    end else if Maxc-Minlowbound+1 > Maxsetsize then begin
	      Setmin := Maxc-Maxsetsize+1;
	    end else begin
	      Setmin := Minlowbound;
	    end;
	  end;
	  Maxhighbound := Max(Maxhighbound, Pmax);
	  if Maxhighbound > Setmax then begin
	    if Maxhighbound-Setmin+1 > Maxsetsize then begin
	      Setmax := Setmin+Maxsetsize-1;
	    end else begin
	      Setmax := Maxhighbound;
	    end;
	  end;
	  Setsize := Setmax-Setmin+1;
	  (* generate final code to load this set part			     *)
	  if Isrange then begin
	    Matchtypes(Lattr);
	    if (Setmin <> 0) or Runtimecheck then begin
	      Swapstak;
	      if Runtimecheck then begin
		Uco2typint(Uchkl, Lattr.Adtype, Setmin);
	      end;
	      if Setmin <> 0 then begin
		Adjtosetoffset(Lattr, Setmin);
	      end;
	      Swapstak;
	      if Runtimecheck then begin
		Uco2typint(Uchkh, Gattr.Adtype, Setmax);
	      end;
	      if Setmin <> 0 then begin
		Adjtosetoffset(Gattr, Setmin);
	      end;
	    end;
	    Uco2typint(Umus, Gattr.Adtype, Setsize);
	  end else begin
	    if Runtimecheck then begin
	      Uco2typint(Uchkl, Gattr.Adtype, Setmin);
	      Uco2typint(Uchkh, Gattr.Adtype, Setmax);
	    end;
	    if Setmin <> 0 then begin
	      Adjtosetoffset(Gattr, Setmin);
	    end;
	    Uco2typint(Usgs, Gattr.Adtype, Setsize);
	  end;
	  if Gotexpr then begin
	    (* combine set just loaded with set already loaded		     *)
	    Shift := Varsetmin-Setmin;
	    if (Shift <> 0) or (Varsetsize <> Setsize) then begin
	      Swapstak;
	      Uco3int(Uadj, Sdt, Setsize, Shift);
	    end;
	    Uco2typint(Uuni, Sdt, Setsize);
	  end;
	  Varsetmin := Setmin;
	  Varsetsize := Setsize;
	  Gotexpr := true;
	end;
	Loopdone := (Sy = Commasy);
	if Loopdone then begin
	  Insymbol;
	end;
      until not Loopdone;
    end;
    if Sy = Rbracksy then begin
      Insymbol;
    end else begin
      Error(155);
    end;
    if not Gotconst and not Gotexpr then begin
      Cstpart.ival := Emptytargetset.ival;
      Cstpart.chars^ := Emptytargetset.chars^;
      Gotconst := true;
      Setmin := 0;
      Setmax := Setunitsize-1;
      Setsize := Setunitsize;
    end;
    if Gotconst and Gotexpr then begin
      (* add constant and var halves shift var half to conform with const    *)
      (* half								     *)
      Shift := Varsetmin-Setmin;
      if (Shift <> 0) or (Varsetsize <> Setsize) then begin
	Uco3int(Uadj, Sdt, Setsize, Shift);
      end;
      (* shift const half to conform with var half			     *)
      Shiftset(Cstpart, Constsetmin-Setmin, Setsize);
      (* load the const half						     *)
      Uco3val(Uldc, Sdt, Setsize, Cstpart);
      (* combine the two						     *)
      Uco2typint(Uuni, Sdt, Setsize);
    end;
    with Gattr do begin 		(* change GATTR to describe the      *)
					(* entire set constant		     *)
      new2(Atypep, Power);
      with Atypep^ do begin
	Basetype := Lstrp;
	Stsize := Setsize;
	ifd := -1;
	packifd := -1;
	Wheredeclared := Memblock;
	Packsize := Setsize;
	Form := Power;
	Stdtype := Sdt;
	Softmin := Setmin;
	Softmax := Setmax;
	Hasfiles := false;
	Hasholes := false;
	Hardmin := Minc;
	Hardmax := Maxc;
      end {with};
      Asize := Setsize;
      Adtype := Sdt;
      if Gotexpr then begin
	Kind := Expr;
#if 0
	dispose(Cstpart.Chars);
#endif
      end else begin
	Kind := Cnst;
	Cval := Cstpart;
      end;
    end {with};
  end {procedure Setconst};

(*Simplexpression,Factor*)
procedure Expression (* Fsys: Setofsys	*);
  var
    Lattr : Attr;
    Lsy : Symbol;
    Linstr : Uopcode;
    i : integer;
    nullset : Valu;

(****************************************************************)
(*								*)
(*	FACTOR -- parses one of the following:			*)
(*	    a variable, a Const constant, an unsigned integer	*)
(*	    or real constant, a string constant, a set constant,*)
(*	    a function call, NIL, NOT <factor>, 		*)
(*	    or ( <expression> ) 				*)
(*								*)
(*	Calls procedures Callspecial, Callinline, and		*)
(*	    Callregular to process function calls and Variable	*)
(*	    to process variables				*)
(*								*)
(****************************************************************)

  procedure Factor (
	      Fsys : Setofsys);
    var
      Lidp : Idp;
      Lklass : Idclass;
      dummy : Indirtype;

    begin				(* factor			     *)
      if not (Sy in Facbegsys) then begin
	Errandskip(173, Fsys+Facbegsys);
	Gattr.Atypep := nil;
      end;
      if Sy in Facbegsys then begin	(* construct the appropriate Gattr   *)
	case Sy of
	Identsy : begin
	    Searchid([Konst, Vars, Field, Func, Types], Lidp);
	    Insymbol;
	    Lklass := Lidp^.Klass;
	    if Lklass = Func then begin (* function call		     *)
	      if Lidp^.Prockind = Special then begin
		Callspecial(Fsys, Lidp);
	      end else if Lidp^.Prockind = Inline then begin
		Callinline(Fsys, Lidp);
	      end else begin
		Callregular(Fsys, Lidp);
	      end;
	    end else if Lklass = Types then begin
	      if Sy = Lparentsy then Insymbol else Warning(153);
	      Expression(Fsys+[Rparentsy]);
	      if not (Gattr.Adtype in [Ldt, Jdt, Hdt, Adt, Rdt, Qdt, Xdt])
		then Error(503);
	      if (Lidp^.Idtype <> nil) then begin 
	        if (Lidp^.Idtype^.Stdtype <> Gattr.Adtype) then begin
		  Load(Gattr);
		  Uco2typtyp(Ucvt, Lidp^.Idtype^.Stdtype, Gattr.Adtype);
	        end;
	        Gattr.Atypep := Lidp^.Idtype;
	        Gattr.Adtype := Gattr.Atypep^.Stdtype;
	      end;
	      if Sy = Rparentsy then Insymbol else Warning(152);
	    end else if Lklass = Konst then begin (* constant name	     *)
	      with Gattr, Lidp^ do begin
		Referenced := true;
		Atypep := Idtype;
		Kind := Cnst;
		if Lidp^.Isordinal then begin
		  Cval.Ival := Ival;
		end else begin
		  Cval.Ival := Sval.Len;
		  new1(Cval.Chars);
		  Cval.Chars^.ss := Sval.Chars^.ss;
		end;
		if Idtype <> nil then begin
		  Adtype := Idtype^.Stdtype;
		  Asize := Idtype^.Stsize;
		end;
	      end {with};
	    end else begin		(* variable			     *)
	      Selector(Fsys, Lidp, dummy);
	    end;
	    if Gattr.Atypep <> nil then begin
	      with Gattr, Atypep^ do begin
		if Form = Subrange then begin (* eliminate subrange types    *)
		  if Kind = Varbl then begin
		    Subkind := Atypep;
		  end;
		  Atypep := Hosttype;	(* to simplify later tests	     *)
		end else if Kind = Varbl then begin
		  Subkind := nil;
		end;
	      end {with};
	    end;
	    if Gattr.Kind = Varbl then begin
	      (* IF Gattr.Indexed THEN Loadaddress(Gattr); avoid	     *)
	      (* half-addressed objects 				     *)
	    end;
	  end {case Identsy};
	Intconstsy : begin		(* integer values		     *)
	    with Gattr do begin
	      Kind := Cnst;
	      Atypep := Intptr;
	      Asize := Intsize;
	      Cval.Ival := Val.Ival;
	      if Cval.Ival >= 0 then begin
		Adtype := Ldt;
	      end else begin
		Adtype := Jdt;
	      end;
	      Insymbol;
	    end {with};
	  end {case Intconstsy};
	Realconstsy : begin		(* real values			     *)
	  if Doubleonly then begin
	    with Gattr do begin
	      Atypep := Doubleptr;
	      Kind := Cnst;
	      Cval := Val;
	      new1(Cval.chars);
	      Cval.chars^ := Val.chars^;
	      Adtype := Qdt;
	      Asize := Doublesize;
	      Insymbol;
	    end {with};
	  end else begin
	    with Gattr do begin
	      Atypep := Realptr;
	      Kind := Cnst;
	      Cval := Val;
	      new1(Cval.chars);
	      Cval.chars^ := Val.chars^;
	      Adtype := Rdt;
	      Asize := Realsize;
	      Insymbol;
	    end {with};
	  end; { if Doubleonly }
	  end {case Realconstsy};
	Stringconstsy : begin 		(* string constant values	     *)
	    with Gattr do begin
	      Constant(Fsys, Atypep, Cval);
	      Kind := Cnst;
	      Adtype := Atypep^.Stdtype;
	      Asize := Atypep^.Stsize;
	    end {with};
	  end {case Stringconstsy};
	Lparentsy : begin		(* parenthesized expression	     *)
	    Insymbol;
	    Expression(Fsys+[Rparentsy]);
	    if Sy = Rparentsy then begin
	      Insymbol;
	    end else begin
	      Warning(152);
	    end;
	  end {case Lparentsy};
	Notsy : begin 			(* negated boolean		     *)
	    Insymbol;
	    Factor(Fsys);
	    if Gattr.Atypep = Boolptr then begin
	      if Gattr.Kind = Cnst then begin
		if Gattr.Cval.Ival = 0 then begin
		  Gattr.Cval.Ival := 1;
		end else begin
		  Gattr.Cval.Ival := 0;
		end;
	      end else begin
		Load(Gattr);
		Uco1type(Ulnot, Gattr.Adtype);
		if stak^.tree^.u.opc = Ulnot then begin
		  stak^.tree^.isbool := true;
		end;
	      end;
	    end else begin
	      Error(359);
	      Gattr.Atypep := nil;
	    end;
	  end {case Notsy};
	Nilsy : begin
	    with Gattr do begin
	      Atypep := Nilptr;
	      Kind := Cnst;
	      Cval.Ival := 0;
	      Adtype := Hdt;
	      Insymbol;
	    end {with};
	  end {case Nilsy};
	Lbracksy :			(* set constructor		     *)
	    Setconst(Fsys)
	end {case};
	Iferrskip(166, Fsys);
      end;
    end {procedure Factor};

(*Term,Simpleexpression,Expression*)
(****************************************************************)
(*								*)
(*	TERM -- parses expression of the form			*)
(*		   FACTOR OP FACTOR				*)
(*	where OP can be *, /, DIV, MOD, or AND			*)
(*								*)
(****************************************************************)
  procedure Term (
	      Fsys : Setofsys);
    var
      Lattr : Attr;
      Lsy : Symbol;

    begin				(* term 			     *)
      Factor(Fsys+Mulopsys);		(* get first factor		     *)
      (* if next symbol is a multiplying operator, get next factor and emit  *)
      (* code to perform the operation					     *)
      while Sy in Mulopsys do begin
	Lattr := Gattr;
	Lsy := Sy;
	Insymbol;
	Factor(Fsys+Mulopsys);
	with Gattr do begin
	  if (Lattr.Atypep = nil) or (Atypep = nil) then begin
	    Atypep := nil;
	  end else begin
	    case Lsy of
	    Mulsy : begin
		if (Lattr.Adtype = Sdt) and (Adtype = Sdt) then begin
					(* set intersection		     *)
		  Matchsets(Lattr);
		  Generatecode(Uint, Sdt, Lattr);
		end else begin		(* multiply			     *)
		  (* convert Lattr and Gattr to be the same type	     *)
		  Matchtypes(Lattr);
		  if (Adtype = Lattr.Adtype)
		   and (Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) then begin
		    Generatecode(Umpy, Adtype, Lattr);
		  end else begin
		    Error(311);
		    Atypep := nil;
		  end;
		end;
	      end {case Mulsy};
	    Rdivsy : begin		(* /, real divide		     *)
		(* convert Lattr and Gattr to the same real type	     *)
		Makereal(Lattr);
		if (Lattr.Adtype = Adtype) and (Gattr.Adtype in [Rdt, Qdt, Xdt]) then begin
		  Generatecode(Udiv, Adtype, Lattr);
		end else begin
		  Error(311);
		  Atypep := nil;
		end;
	      end {case Rdivsy};
	    Idivsy : begin		(* div				     *)
		(* convert Lattr and Gattr to same integer type 	     *)
		Matchtypes(Lattr);
		if (Adtype = Lattr.Adtype) and (Adtype in [Jdt, Ldt]) then
		  begin
		  Generatecode(Udiv, Adtype, Lattr);
		end else begin
		  Error(311);
		  Atypep := nil;
		end;
	      end {case Idivsy};
	    Modsy : begin		(* mod				     *)
		(* convert Lattr and Gattr to same integer type 	     *)
		Matchtypes(Lattr);
		if (Adtype = Lattr.Adtype) and (Adtype in [Jdt, Ldt]) then
		  begin
		  Generatecode(Umod, Adtype, Lattr);
		end else begin
		  Error(311);
		  Atypep := nil;
		end;
	      end {case Modsy};
	    Andsy : begin		(* and				     *)
		if (Lattr.Atypep = Boolptr) and (Atypep = Boolptr) then begin
		  Generatecode(Uand, Adtype, Lattr);
		  if stak^.tree^.u.opc = Uand then begin
		    stak^.tree^.isbool := true;
		  end;
		end else begin
		  Error(359);
		  Atypep := nil;
		end;
	      end {case Andsy};
	    end {case};
	  end;
	end {with};
      end {while};
    end {procedure Term};

    (*************************************************************************)
    (* SIMPLEEXPRESSION -- parses expression of the form SIGN TERM OP TERM   *)
    (* where OP can be +, -, or OR					     *)
    (*************************************************************************)

  procedure Simpleexpression (
	      Fsys : Setofsys);
    var
      Lattr : Attr;
      Lsy, Sign : Symbol;

    begin				(* simpleexpression		     *)
      (* get initial + or						     *)
      if (Sy in [Plussy, Minussy]) then begin
	Sign := Sy;
	Insymbol;
      end else begin
	Sign := Othersy;
      end;
      Term(Fsys+Addopsys);		(* get first term		     *)
      (* negate first term, if there was an initial			     *)
      if Sign <> Othersy then begin
	with Gattr do begin
	  if Atypep <> nil then begin
	    (* make sure item to be negated was a number		     *)
	    if Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt] then begin
	      if Sign = Minussy then begin
		Generatecode(Uneg, Adtype, Gattr);
	      end;
	    end else begin
	      Error(311);
	      Gattr.Atypep := nil;
	    end;
	  end;
	end {with};
      end;

      (***********************************************************************)
      (* if next symbol is an adding operator, get next term and emit code   *)
      (* to perform the operation					     *)
      (***********************************************************************)
      while Sy in Addopsys do begin
	Lattr := Gattr;
	Lsy := Sy;
	Insymbol;
	Term(Fsys+Addopsys);
	with Gattr do begin
	  if (Lattr.Atypep <> nil) and (Atypep <> nil) then begin
	    case Lsy of
	    Plussy : begin		(* +				     *)
		if (Lattr.Adtype = Sdt) and (Adtype = Sdt) then begin
					(* set union			     *)
		  Matchsets(Lattr);
		  Generatecode(Uuni, Sdt, Lattr);
		end else begin		(* addition			     *)
		  Matchtypes(Lattr);
		  if (Adtype = Lattr.Adtype)
		   and (Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) then begin
		    Generatecode(Uadd, Adtype, Lattr);
		  end else begin
		    Error(311);
		    Atypep := nil;
		  end;
		end;
	      end {case Plussy};
	    Minussy : begin
		if (Lattr.Adtype = Sdt) and (Adtype = Sdt) then begin
					(* set difference		     *)
		  Matchsets(Lattr);
		  Generatecode(Udif, Sdt, Lattr);
		end else begin		(* subtraction			     *)
		  Matchtypes(Lattr);
		  if (Adtype = Lattr.Adtype)
		   and (Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) then begin
		    Generatecode(Usub, Adtype, Lattr);
		  end else begin
		    Error(311);
		    Atypep := nil;
		  end;
		end;
	      end {case Minussy};
	    Orsy : begin		(* or				     *)
		if (Lattr.Atypep = Boolptr) and (Atypep = Boolptr) then begin
		  Generatecode(Uior, Adtype, Lattr);
		  if stak^.tree^.u.opc = Uior then begin
		    stak^.tree^.isbool := true;
		  end;
		end else begin
		  Error(359);
		  Atypep := nil;
		end;
	      end {case Orsy}
	    end {case};
	  end else begin
	    Atypep := nil;
	  end;
	end {with};
      end {while};
    end {procedure Simpleexpression};

    (*************************************************************************)
    (* EXPRESSION -- parses expression of the form SIMPLEEXPRESSION OP	     *)
    (* SIMPLEEXPRESSION where OP can be =, <>, <, >, <=, >=, or IN	     *)
    (*************************************************************************)

  begin 				(* expression			     *)
    Simpleexpression(Fsys+Relopsys);
    if Sy in Relopsys then begin
      Lattr := Gattr;
      Lsy := Sy;
      Insymbol;
      Simpleexpression(Fsys);
      with Gattr do begin
	if (Lattr.Atypep <> nil) and (Atypep <> nil) then begin
	  if Lsy = Insy then begin	(* in				     *)
	    if Adtype <> Sdt then begin
	      Error(213);
	      Atypep := nil;
	    end else if not Comptypes(Lattr.Atypep, Atypep^.Basetype) then
	      begin
	      (* make sure the element to be tested is the same kind of      *)
	      (* simple type that the set is composed of		     *)
	      Error(260);
	      Atypep := nil;
	    end else begin
	      if Atypep^.Softmin <> 0 then begin
		(* increment or decrement the element in accordance with the *)
		(* base of the set					     *)
		Loadboth(Lattr);
		Swapstak;
		Adjtosetoffset(Lattr, Gattr.Atypep^.Softmin);
		Swapstak;
	      end;
	      Generatecode(Uinn, Lattr.Adtype, Lattr);
	    end;
	  end else begin		(* Lsy <> Insy comparisons	     *)
	    if (Lattr.Atypep^.Form = Power) and (Gattr.Atypep^.Form = Power) then
	    begin
	      Matchsets(Lattr);
	    end else begin
	      Matchtypes(Lattr);
	    end;
	    if not (Comptypes(Lattr.Atypep, Atypep) or 
		    Stringpadpossible(Lattr.Atypep, Gattr) or 
		    Stringpadpossible(Gattr.Atypep, Lattr)) then begin
	      Error(260);
	    end else begin
	      case Lattr.Atypep^.Form of
	      Scalar, Subrange :
		  ;
	      Power : begin
		  if Lsy in [Ltsy, Gtsy] then begin
		    Error(313);
		  end;
		end {case Power};
	      Arrays, SPointer, Records :
		  (* only strings can be tested for anything but equality    *)
		  (* and inequality					     *)
		  begin
		  if not Strng(Lattr.Atypep) then begin
		    if Lsy in [Ltsy, Lesy, Gtsy, Gesy] then begin
		      Error(312);
		    end;
		  end;
		end {case Arrays};
	      Files : Error(314)
	      end {case};
	      (* if we are comparing two arrays or records, the operators    *)
	      (* should be IEQU and co. instead of EQU and co.		     *)
	      if (Lattr.Atypep^.Stdtype = Sdt)
		  and ((Lsy = Lesy) or (Lsy = Gesy)) then begin
	        if Lsy = Gesy then begin
		  Loadboth(Lattr);
		  Swapstak;
		end;
		Generatecode(Udif, Sdt, Lattr);
		Kind := Expr;
		nullset.ival := Lattr.Atypep^.Stsize div 4;
		new1(nullset.chars);
		for i := 1 to nullset.ival do nullset.chars^.ss[i] := '0';
		Uco3val(Uldc, Sdt, Lattr.Atypep^.Stsize, nullset);
#if 0
		dispose(nullset.chars);
#endif
		Uco2typint(Uequ, Sdt, Lattr.Atypep^.Stsize);
	      end else if (Lattr.Atypep^.Stdtype <> Mdt) then begin
		case Lsy of
		Ltsy : Linstr := Ules;
		Lesy : Linstr := Uleq;
		Eqsy : Linstr := Uequ;
		Gesy : Linstr := Ugeq;
		Gtsy : Linstr := Ugrt;
		Nesy : Linstr := Uneq;
		end {case};
		Generatecode(Linstr, Adtype, Lattr);
	      end else begin
		Loadboth(Lattr);
		case Lsy of
		Ltsy : Linstr := Uiles;
		Lesy : Linstr := Uileq;
		Eqsy : Linstr := Uiequ;
		Gesy : Linstr := Uigeq;
		Gtsy : Linstr := Uigrt;
		Nesy : Linstr := Uineq;
		end {case};
		Uco2intint(Linstr, 8, Atypep^.Stsize);
		Kind := Expr;
	      end;
	    end;
	  end;
	end;

	(*********************************************************************)
	(* the item on top of the stack is now a boolean. Change Gattr to    *)
	(* reflect this 						     *)
	(*********************************************************************)
	Atypep := Boolptr;
	Adtype := Jdt;
      end {with};
    end;
  end {procedure Expression};
