{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasfold.p,v 1030.7 88/02/18 14:55:27 bettina Exp $ }

{ Given an expression tree node with constant operands, return a
  constant tree node. }

#include "upasglob.h"
#include "upasfold.h"
#include "upastree.h"
#include "upaslex.h"
#include "upasexpr.h"
#include "allocator.h"

function is_constant
{ (
	   t : pttreerec)
   : boolean;
}
  ;
  begin
    is_constant := (t^.u.opc = Uldc) and (t^.u.dtype in [Adt, Hdt, Ldt, Jdt]);
  end {function is_constant};

function is_float_constant
{ (
	   t : pttreerec)
   : boolean;
}
  ;
  begin
    is_float_constant := (t^.u.opc = Uldc) and (t^.u.dtype in [Rdt, Qdt, Xdt]);
  end {function is_float_constant};


{-----------------------------------------------------------------------------}
{ Given an expression with integer operands, do constant folding to return an }
{ integer tree. 							      }
{-----------------------------------------------------------------------------}
function fold
{ (
       var u : bcrec;
	   fleft : pttreerec;
	   fright : pttreerec)
	: boolean;
}
  ;

  var
    fdt : Datatype;
    i, ileft, iright : integer;
    uleft, uright : cardinal;
    overlay :
      record
	case boolean of
	  true : (
	    sint : integer);
	  false : (
	    uint : cardinal);
      end {record};

  begin

    fdt := u.dtype;
    ileft := fleft^.u.constval.ival;
    overlay.sint := ileft;
    uleft := overlay.uint;
    if fright <> nil then begin
      iright := fright^.u.constval.ival;
      overlay.sint := iright;
      uright := overlay.uint;
    end;

    case u.opc of

    Ucvtl : begin
	iright := lshift(1, u.i1-1);
	i := bitand(ileft, iright*2-1);
	if fdt = Jdt then i := bitxor(i, iright)-iright;
      end {case Ucvtl};

    Ucvt : begin
	if fdt in [Jdt, Ldt, Adt, Hdt] then begin
	  i := ileft;
	end else begin
	  return false;
	end;
      end {case Ucvt};

    Uadd : i := ileft+iright;

    Usub : i := ileft-iright;

    Umpy : i := ileft*iright;

    Uinc : i := ileft+u.i1;

    Udec : i := ileft-u.i1;

    Udiv : begin
	if iright = 0 then begin
	  warning(178);
	  return false;
	end else if fdt = Jdt then begin
	  i := ileft div iright
#ifdef PASTEL
	end else if iright < 0 then begin
	  i := ord(uleft >= uright)
#endif
	end else begin
	  i := uleft div uright;
	end;
      end {case Udiv};

    Umod : begin
	if iright = 0 then begin
	  warning(178);
	  return false;
	end else if fdt = Jdt then begin
#if PASTEL
	  i := floormod(ileft, iright);
#else
	  i := ileft mod iright
#endif
#ifdef PASTEL
	end else if iright < 0 then begin
	  i := ileft;
	  if uleft >= uright then i := i-uright
#endif
	end else begin
	  i := uleft mod uright;
	end;
      end {case Umod};

    Uand : i := bitand(ileft, iright);

    Uior : i := bitor(ileft, iright);

    Uxor : i := bitxor(ileft, iright);

    Ushl : begin
	iright := bitand(iright, 2#11111);
	i := lshift(ileft, iright);
      end {case Ushl};

    Ushr : begin
	iright := bitand(iright, 2#11111);
	if fleft^.u.dtype = Jdt then begin
	  i := rshift(ileft, iright);
	  iright := lshift(1, 32-iright-1);
	  i := bitxor(bitand(i, iright*2-1), iright)-iright;
	end else begin
	  i := rshift(uleft, iright);
	end;
      end {case Ushr};

    Unot : i := bitnot(ileft);

    Ulnot : i := ord(ileft = 0);

    Usqr : i := ileft*ileft;

    Uneg : i := -ileft;

    Uabs : i := abs(ileft);

    Uodd : i := ord(odd(ileft));

    Ugeq : begin
	if fdt = Jdt then i := ord(ileft >= iright)
	else i := ord(uleft >= uright);
      end {case Ugeq};

    Ugrt : begin
	if fdt = Jdt then i := ord(ileft > iright)
	else i := ord(uleft > uright);
      end {case Ugrt};

    Uleq : begin
	if fdt = Jdt then i := ord(ileft <= iright)
	else i := ord(uleft <= uright);
      end {case Uleq};

    Ules : begin
	if fdt = Jdt then i := ord(ileft < iright)
	else i := ord(uleft < uright);
      end {case Ules};

    Uequ : i := ord(ileft = iright);

    Uneq : i := ord(ileft <> iright);

    Umin : begin
	if fdt = Jdt then i := min(ileft, iright)
	else i := min(uleft, uright);
      end {case Umin};

    Umax : begin
	if fdt = Jdt then i := max(ileft, iright)
	else i := max(uleft, uright);
      end {case Umax};

    Udup : i := ileft;

    otherwise:
      Error(171);
    end {case};

    fleft^.u.constval.ival := i;
    fleft^.u.dtype := fdt;
#if 0
    if fright <> nil then begin
      Reltreenode(fright);
      fright := nil;
    end;
#endif
    return true;
  end {function fold};


{-----------------------------------------------------------------------------}
{ Given an expression with integer operands, do constant folding to return an }
{ integer tree. 							      }
{-----------------------------------------------------------------------------}
function float_fold
{ (
       var u : bcrec;
	   fleft : pttreerec;
	   fright : pttreerec)
	: boolean;
}
  ;
  var
    fdt : Datatype;
    i : cardinal;
    left, right : ^Stringtext;
  begin
    fdt := u.dtype;
    left := fleft^.u.constval.chars;
    if fright <> nil then begin
      right := fright^.u.constval.chars;
    end;

    case u.opc of
    Ucvt : begin
	case fdt of
	  Rdt: fleft^.u.length := Realsize;
	  Qdt: fleft^.u.length := Doublesize;
	  Xdt: fleft^.u.length := Extendedsize;
	  otherwise:
	    return false;
	end {case};
	fleft^.u.dtype := fdt;
      end {case Ucvt};

    Uneg : begin
	new1(fleft^.u.constval.chars);
	if left^.ss[1] = '-' then begin
	  fleft^.u.constval.chars^.ss := left^.ss;
	  fleft^.u.constval.chars^.ss[1] := ' ';
	end else if left^.ss[1] = ' ' then begin
	  fleft^.u.constval.chars^.ss := left^.ss;
	  fleft^.u.constval.chars^.ss[1] := '-';
	end else begin
	  for i := fleft^.u.constval.ival downto 1 do begin
	    fleft^.u.constval.chars^.ss[i+1] := left^.ss[i];
	  end {for};
	  fleft^.u.constval.ival := fleft^.u.constval.ival + 1;
	  fleft^.u.constval.chars^.ss[1] := '-';
	end;
      end {case Uneg};

    Uabs : begin
	if left^.ss[1] = '-' then begin
	  new1(fleft^.u.constval.chars);
	  fleft^.u.constval.chars^.ss := left^.ss;
	  fleft^.u.constval.chars^.ss[1] := ' ';
	end;
      end {case Uabs};

    otherwise:
      Error(171);
    end {case};

#if 0
    if fright <> nil then begin
      Reltreenode(fright);
    end;
#endif
    return true;
  end {function float_fold};

(************************************************************************)
(*									*)
(*	CONSTANTEXPRESSION -- parses a constant expression		*)
(*									*)
(*									*)
(************************************************************************)

procedure ConstantExpression
{ (
	    Fsys : Setofsys;
	var Fstrp : Strp;
	var Fvalu : Valu);
}
  ;
  var
    Lstrp : Strp;

  begin 				(* constant			     *)
    Lstrp := nil;
    Fvalu.Ival := 0;
    Expression(Fsys);

    with Gattr do begin
      if (Kind = Cnst) then begin
	Lstrp := Atypep;
	Fvalu := Cval;
      end else begin
	if (stak^.tree <> nil) and (stak^.tree^.U.Opc = Uldc) then begin
	  if (Atypep = Charptr) or (Atypep = Intptr) or (Atypep = Boolptr)
	   or (Atypep = Realptr) or (Atypep = Doubleptr)
	   or (Atypep = Extendedptr) then begin
	    Lstrp := Atypep;
	    Fvalu := stak^.tree^.U.Constval;
	    Popstak;
	  end else Error(320);
	end else Error(320);
      end;
    end {with};

    if Lstrp = nil then begin
      new1(Lstrp);
      Lstrp^.Stdtype := Ldt;
    end;
    Fstrp := Lstrp;
  end {procedure ConstantExpression};
