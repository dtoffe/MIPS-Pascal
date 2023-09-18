{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasbutil.p,v 1030.7 88/02/18 14:55:13 bettina Exp $ }

#include "upasglob.h"
#include "upasutil.h"
#include "upaslex.h"
#include "upasbutil.h"
#include "allocator.h"

(*Getbounds,Strng,Comptypes,Constant*)


(************************************************************************)
(*									*)
(*	COMPTYPES -- decides whether two types are compatible		*)
(*									*)
(*	According to the standard:					*)
(*									*)
(*     Two types shall be designated compatible if they are  identical, *)
(*     or  if  one is a subrange of the other, or if both are subranges *)
(*     of the same type, or if they are  string  types	with  the  same *)
(*     number  of  components,	or  if they are set-types of compatible *)
(*     base-types.							*)
(*									*)
(************************************************************************)

function Comptypes /* ( Fstrp1, Fstrp2 : Strp) : boolean  */;

  begin 				(* comptypes			     *)
    if Fstrp1 = Fstrp2 then begin
      Comptypes := true;
    end else if (Fstrp1 <> nil) and (Fstrp2 <> nil) then begin
      if Fstrp1^.Form = Fstrp2^.Form then begin
	case Fstrp1^.Form of
	Scalar : begin
	    if ((Fstrp1 = Intptr) or (Fstrp1 = Cardinalptr))
		and ((Fstrp2 = Intptr) or (Fstrp2 = Cardinalptr)) then begin
	      Comptypes := true;
	    end else begin
	      Comptypes := false;
	    end;
	  end {case Scalar};
	Records, Files :
	    Comptypes := false;
	SPointer :
	    Comptypes := (Fstrp1 = Nilptr) or (Fstrp2 = Nilptr)
		or Comptypes(Fstrp1^.Eltype, Fstrp2^.Eltype);
	Subrange :
	    Comptypes := Comptypes(Fstrp1^.Hosttype, Fstrp2^.Hosttype);
	Power :
	    Comptypes := Comptypes(Fstrp1^.Basetype, Fstrp2^.Basetype);
	Arrays : begin
	    if Strng(Fstrp1) and Strng(Fstrp2) then begin
	      if (Fstrp1^.Inxtype = nil) or (Fstrp2^.Inxtype = nil) then begin
		Comptypes := true;
	      end else begin
		Comptypes :=
		    (not Standrdonly or (Fstrp1^.Arraypf = Fstrp2^.Arraypf))
		    and (Fstrp1^.Inxtype^.Vmax = Fstrp2^.Inxtype^.Vmax);
	      end;
	    end else begin
	      Comptypes := false;
	    end;
	  end {case Arrays};
	end {case};

	(*********************************************************************)
	(* fstrp1^.form <> fstrp2^.form 				     *)
	(*********************************************************************)
      end else if Fstrp1^.Form = Subrange then begin
	Comptypes := Comptypes(Fstrp1^.Hosttype, Fstrp2);
      end else if Fstrp2^.Form = Subrange then begin
	Comptypes := Comptypes(Fstrp1, Fstrp2^.Hosttype);
      end else begin
	Comptypes := false;
      end;
    end else begin			(* if one of them is nil, they are   *)
					(* compatible			     *)
      Comptypes := true;
    end;
  end {function Comptypes};

function Stringpadpossible /* ( Fstrp1: Strp; var Fattr: Attr) : boolean  */;
  (* if Fattr describes a string, check if it is possible to make compatible
     by padding the string *)
  begin
  if Standrdonly or (Fattr.Kind <> Cnst) or not Strng(Fstrp1) or 
     not Strng(Fattr.Atypep) then 
    Stringpadpossible := false
  else if (Fstrp1^.Inxtype^.Vmax > Fattr.Atypep^.Inxtype^.Vmax) and
	  (Fstrp1^.Inxtype^.Vmax <= Strglgth) then begin
    (* string padding is possible *)
    Stringpadpossible := true;
    (* extend the literal constant *)
    repeat
      Fattr.Cval.Ival := Fattr.Cval.Ival + 1;
      Fattr.Cval.Chars^.ss[Fattr.Cval.Ival] := ' ';
      Fattr.Atypep^.Stsize := Fattr.Atypep^.Stsize + Charsize;
      Fattr.Asize := Fattr.Asize + Charsize;
    until Fattr.Cval.Ival = Fstrp1^.Inxtype^.Vmax;
    Fattr.Atypep^.Inxtype^.Vmax := Fattr.Cval.Ival;
    end
  else Stringpadpossible := false;
  end {function Stringpadpossible};

(************************************************************************)
(*									*)
(*	GETBOUNDS -- given a pointer to a subrange or scalar type,	*)
(*		     returns upper and lower bounds			*)
(*									*)
(************************************************************************)

procedure Getbounds /* ( Fstrp : Strp; var Fmin, Fmax : integer)  */;

  (***************************************************************************)
  (* given a pointer to a subrange or scalar type, return upper and lower    *)
  (* bounds in fmin and fmax						     *)
  (***************************************************************************)

  begin 				(* getbounds			     *)
    Fmin := 0;
    Fmax := 0;
    if Fstrp <> nil then begin
#if 0
      if (Fstrp^.form = Subrange) and not Comptypes(Realptr, Fstrp) then begin
	Fmin := Fstrp^.vmin;
	Fmax := Fstrp^.vmax;
      end else if Fstrp^.form <> Scalar then begin
	Error(171);
      end else if Fstrp^.Scalkind = Declared then begin
	Fmin := 0;
	Fmax := Fstrp^.Dimension;
      end else if Fstrp = Intptr then begin
	Fmin := Tgtminint;
	Fmax := Tgtmaxint;
      end else if Fstrp = Cardinalptr then begin
	Fmin := 0;
	Fmax := Tgtmaxint;
      end else if Fstrp = Charptr then begin
	Fmin := Tgtfirstchar;
	Fmax := Tgtlastchar;
      end;
#else
      if Fstrp = Intptr then begin	(* type integer = minint..maxint     *)
	Fmin := Tgtminint;
	Fmax := Tgtmaxint;
      end else if Fstrp = Cardinalptr then begin
	Fmin := 0;
	Fmax := Tgtmaxint;
      end else if (Fstrp^.Form <= Subrange)
       and not Comptypes(Realptr, Fstrp) then begin
	with Fstrp^ do begin
	  if Form = Subrange then begin
	    Fmin := Vmin;
	    Fmax := Vmax;
	    (* scalar							     *)
	  end else if (Fstrp = Charptr) then begin
	    Fmin := Tgtfirstchar;
	    Fmax := Tgtlastchar;
	  end else if (Scalkind = Declared) then begin
	    Fmax := Dimension;
	  end else begin
	    Error(171);
	  end;
	end {with};
      end;
#endif
    end;				(* compiler error		     *)

  end {procedure Getbounds};

(************************************************************************)
(*									*)
(*	STRNG -- returns true if Fstrp describes a packed array of	*)
(*		  char whose lower index is 1				*)
(*									*)
(************************************************************************)

function Strng /* ( Fstrp : Strp) : boolean  */;
  (* returns true if fstrp describes a packed array of char		     *)
  begin 				(* strng			     *)
    Strng := false;
    if Fstrp <> nil then begin
      if Fstrp^.Form = Arrays then begin
	if Fstrp^.Inxtype <> nil then begin
	  Strng := (Fstrp^.Aeltype = Charptr)
	   and (Fstrp^.Inxtype^.Stdtype in [Jdt, Ldt])
	   and (Fstrp^.Inxtype^.Vmin = 1);
	end;
      end;
    end;
  end {function Strng};




(************************************************************************)
(*									*)
(*	CONSTANT -- parses a constant					*)
(*									*)
(*	The value is returned in FVALU and the type in FSTRP		*)
(*									*)
(************************************************************************)

procedure Constant (* Fsys : Setofsys; var Fstrp : Strp; var Fvalu : Valu  *);
  var
    i : integer;
    Lstrp, Lstrp1 : Strp;
    Lidp : Idp;

  begin 				(* constant			     *)
    Lstrp := nil;
    Fvalu.Ival := 0;
    Skipiferr(Constbegsys, 207, Fsys);
    if Sy in Constbegsys then begin
      if Sy = Stringconstsy then begin	(* string constant		     *)
	if Lgth = 1 then begin
	  Lstrp := Charptr;
	end else begin			(* not a predefined length	     *)
	  new2(Lstrp1, Subrange);
	  with Lstrp1^ do begin
	    Form := Subrange;
	    ifd := -1;
	    packifd := -1;
	    Wheredeclared := Memblock;
	    Stsize := Intsize;
	    Packsize := Intsize;
	    Stdtype := Jdt;
	    Vmin := 1;
	    Vmax := Lgth;
	    Hosttype := Intptr;
	    Hasholes := false;
	    Hasfiles := false;
	  end {with};
	  new2(Lstrp, Arrays);
	  with Lstrp^ do begin
	    Form := Arrays;
	    ifd := -1;
	    packifd := -1;
	    Wheredeclared := Memblock;
	    Aeltype := Charptr;
	    Inxtype := Lstrp1;
	    Stdtype := Mdt;
	    Arraypf := true;
	    Aelsize := Pcharsize;
	    Packsize := Stringsize(Lgth);
	    Stsize := Packsize;
	    Align := Charalign;
	    Hasholes := Lgth*Pcharsize <> Packsize;
	    Hasfiles := false;
	  end {with};
	end;
	Fvalu := Val;
	new1(Fvalu.chars);
	Fvalu.chars^ := Val.chars^;
	Insymbol;
      end else begin			(* sy <> stringconstsy		     *)
	Lastsign := None;		(* parse a +- sign		     *)
	if Sy in [Plussy, Minussy] then begin
	  if Sy = Plussy then begin
	    Lastsign := Pos;
	  end else begin
	    Lastsign := Neg;
	  end;
	  Insymbol;
	end;
	if Sy = Identsy then begin	(* constant idname		     *)
	  Searchid([Konst], Lidp);
	  with Lidp^ do begin
	    Lstrp := Idtype;
	    if Isordinal then begin
	      Fvalu.Ival := Ival;
	    end else begin
	      Fvalu.Ival := Sval.len;
	      new1(Fvalu.Chars);
	      Fvalu.Chars^.ss := Sval.Chars^.ss;
	    end;
	    Referenced := true;
	  end {with};
	  if Lastsign <> None then begin
	    if Lastsign = Neg then begin
	      if Lstrp = Intptr then begin
		Fvalu.Ival := -Fvalu.Ival;
	      end else if (Lstrp = Realptr) or (Lstrp = Doubleptr)
	       or (Lstrp = Extendedptr) then begin
		Fvalu.Chars^.ss[1] := '-';
	      end else begin
		Error(167);
	      end;
	    end else if Lstrp^.Form <> Scalar then begin
	      Error(167);
	    end;
	  end;
	  Insymbol;
	  (* number							     *)
	end else if Sy in [Intconstsy, Realconstsy] then begin
	  if Sy = Intconstsy then begin
	    Lstrp := Intptr;
	  end else begin
	    Lstrp := Realptr;
	  end;
	  Fvalu := Val;
	  Insymbol;
	end else begin			(* invalid constant		     *)
	  Errandskip(168, Fsys);
	end;
      end;
      Iferrskip(166, Fsys);
    end;
    Fstrp := Lstrp;
  end {procedure Constant};
