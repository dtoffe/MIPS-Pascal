{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasdecl.p,v 1030.7 88/02/18 14:55:16 bettina Exp $ }

#include "upasglob.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upasfold.h"
#include "upasbutil.h"
#include "upasmain.h"
#include "upassym.h"
#include "upasdecl.h"
#include "upasexpr.h"
#include "allocator.h"
#include "cmplrs/stsupport.h"

const
  Halfsize = 2*Addrunit;


(*Simpletype,Sizeofsubrange*)
(************************************************************************)
(*									*)
(*	TYPE DEFINITION MODULE						*)
(*									*)
(*	The main procedure Typedefinition, parses a type definition	*)
(*	and returns a ponter to a structure that describes the		*)
(*	type.								*)
(*									*)
(*	Principle procedures are:					*)
(*									*)
(*	Simpletype:parses ennumerated types and subranges		*)
(*	Fieldlist: parses a field list for a record, calculating the	*)
(*		   size of the record as it goes			*)
(*	Typedefinition: parses a pointer, array, record, or set type	*)
(*			definition					*)
(*									*)
(************************************************************************)

(************************************************************************)
(*									*)
(*	SIMPLETYPE							*)
(*									*)
(*	   Parses:							*)
(*	     1) An ennumerated type of the form (Id1, Id2, ..., Idn)	*)
(*	     2) A subrange						*)
(*	     3) A previously declared type identifier (renaming types)	*)
(*									*)
(************************************************************************)
procedure Simpletype (
	    Fsys : Setofsys;
	var Fstrp : Strp);
  (* parses the definition of a nonstructured type. i.e. previously defined  *)
  (* type, subrange, or ennumerated type (declared scalars)		     *)
  var
    Lstrp : Strp;
    Lidp : Idp;
    Lcnt, Maxval : integer;
    Lvalu : Valu;

  procedure Sizeofsubrange (
	      Fstrp : Strp);

    (*************************************************************************)
    (* FSTRP points to a structure record of form SUBRANGE whose lower bound *)
    (* and STSIZE has been filled in. This procedure parses the upper bound, *)
    (* fills it in, an then calculates the packed size for the subrange      *)
    (*************************************************************************)
    var
      Lstrp : Strp;
      Lvalu : Valu;

    begin				(* sizeofsubrange		     *)
      ConstantExpression(Fsys, Lstrp, Lvalu);
      with Fstrp^ do begin
	if not (Hosttype^.Stdtype in [Jdt, Ldt]) or
	   not (Lstrp^.Stdtype in [Jdt, Ldt]) then begin
	  Error(329);
	  { prevent from crashing with div by 0 }
	  Packsize := Stsize;
	  Packalign := Align;
	end else if not Comptypes(Hosttype, Lstrp) then begin
	  Error(304);
	  { prevent from crashing with div by 0 }
	  Packsize := Stsize;
	  Packalign := Align;
	end else begin
	  Vmax := Lvalu.Ival;
	  if Hosttype <> nil then begin
	    if (Hosttype = Boolptr) or (Hosttype = Charptr) then begin
	      Packsize := Hosttype^.Packsize;
	      Packalign := Hosttype^.Packalign;
	    end else begin
	      case Hosttype^.Stdtype of
	      Jdt, Ldt : begin
		  if (Vmax = Tgtmaxint) or (Vmin <= -Tgtmaxint) then begin
		    Packsize := Intsize;
		    Packalign := Intalign;
		  end else if Vmin < 0 then begin (* signed integer	     *)
		    if Vmax+1 > -Vmin then begin
		      Maxval := Vmax+1;
		    end else begin
		      Maxval := -Vmin;
		    end;
		    Packsize := Log2(Maxval)+1;
		    Packalign := Rpackunit;
		  end else begin	(* unsigned integer		     *)
		    Packsize := Log2(Vmax+1);
		    Packalign := Rpackunit;
		    Stdtype := Ldt;
		  end;
		  Packsize := ((Packsize+Rpackunit-1) div Rpackunit)*Rpackunit;
		  if Packsize <= Addrunit then begin
		    Stsize := Addrunit;
		  end else if Packsize <= Halfsize then begin
		    Stsize := Halfsize;
		  end else begin
		    Stsize := Wordsize;
		  end;
		  Align := Stsize;
		end {case Jdt};
	      end {case};
	    end;
	  end;
	end;
      end {with};
    end {procedure Sizeofsubrange};

  procedure Declscalars (
	  var Fstrp : Strp);
    var
      Ttop : Disprange;
      Listhead, Listtail, Lidp : Idp;

      (***********************************************************************)
      (* Parses a list of declared scalars for an ennumerated type). A	     *)
      (* Structure record to decribe this type is created and returned, and  *)
      (* is added to the global list headed by Declscalarptr		     *)
      (***********************************************************************)
    begin
      (* This declaration might be in the middle of a record declaration, in *)
      (* which casethe top of the display might point to the record. But we  *)
      (* want the declared scalars to be entered as local identifiers, so we *)
      (* must temporarily pop the stack back down to that level.	     *)
      Ttop := Top;
      while Display[Top].Occur <> Blck do begin
	Top := Top-1;
      end {while};
      new3(Fstrp, Scalar, Declared);
      Listhead := nil;
      Lcnt := 0;
      repeat
	(* Get next declared scalar					     *)
	Insymbol;
	new3(Lidp, Konst, true);
	if Sy = Identsy then begin
	  if Listhead = nil then begin
	    Listhead := Lidp;
	  end else begin
	    Listtail^.Next := Lidp;
	  end;
	  with Lidp^ do begin
	    Klass := Konst;
	    Idname := Id;
	    symndx := 0;
	    Idtype := Fstrp;
	    Ival := Lcnt;
	    Isordinal := true;
	    Referenced := true;
	  end {with};
	  Enterid(Lidp);
	  Lcnt := Lcnt+1;
	  Insymbol;
	end else begin
	  Error(209);
	end;
	Iferrskip(166, Fsys+[Commasy, Rparentsy]);
	Listtail := Lidp;
      until Sy <> Commasy;
      Listtail^.Next := nil;
      Top := Ttop;			(* restore display		     *)

      with Fstrp^ do begin
	Form := Scalar;
	Scalkind := Declared;
	ifd := -1;
	packifd := -1;
	Wheredeclared := Memblock;
	Fconst := Listhead;
	Packsize := Log2(Lcnt);
	if Packsize <= Addrunit then begin
	  Stsize := Addrunit;
	end else if Packsize <= Halfsize then begin
	  Stsize := Halfsize;
	end else begin
	  Stsize := Wordsize;
	end;
	Align := Stsize;
	Packalign := Rpackunit;
	Saddress := -1;
	Hasholes := false;
	Hasfiles := false;
	while Packsize mod Rpackunit > 0 do begin
	  Packsize := Packsize+1;
	end {while};
	Stdtype := Ldt;
	Dimension := Lcnt-1;
	Tlev := Level;
      end {with};
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
    end {procedure Declscalars};

  label
    non_subrange;

  begin 				(* simpletype			     *)
    Skipiferr(Simptypebegsys, 208, Fsys);
    if not (Sy in Simptypebegsys) then begin
      Fstrp := nil;
    end else begin
      if Sy = Lparentsy then begin
	Declscalars(Fstrp);		(* ennumerated type		     *)
      end else begin
#if 0
	if Sy = Identsy then begin
	  Searchid([Types, Konst], Lidp);
	  Insymbol;
	  if Lidp^.Klass = Konst then begin (* subrange delimited by a named *)
					(* constant			     *)
	    (* create record to describe the subrange and fill in Vmin	     *)
	    new2(Fstrp, Subrange);
	    with Fstrp^, Lidp^ do begin
	      Referenced := true;
	      Form := Subrange;
	      ifd := -1;
	      packedifd := -1;
	      Wheredeclared := Memblock;
	      Hasholes := false;
	      Hasfiles := false;
	      if Strng(Idtype) or (Idtype = Realptr) or (Idtype = Doubleptr)
	       or (Idtype = Extendedptr) then begin
		Error(303);
		Idtype := nil;
	      end else begin
		Hosttype := Idtype;
	      end;
	      Vmin := Ival;
	      Stsize := Intptr^.Stsize;
	      Align := Intptr^.Align;
	      if Idtype <> nil then begin
		Stdtype := Idtype^.Stdtype;
	      end;
	    end {with};
	    if Sy = Rangesy then begin
	      Insymbol;
	    end else begin
	      Error(151);
	    end;
	    Sizeofsubrange(Fstrp);	(* get vmax and compute size	     *)
	  end else begin		(* renaming types		     *)
	    Fstrp := Lidp^.Idtype;
	    Lidp^.Referenced := true;
	  end;
	end else begin			(* subrange delimited by constant    *)
					(* values			     *)
#endif
	  if Sy = Identsy then begin
	    Searchid([Types, Konst, Vars, Func], Lidp);
	    if Lidp^.Klass = Types then begin	(* renaming types *)
	      Insymbol;
	      Fstrp := Lidp^.Idtype;
	      Lidp^.Referenced := true;
	      goto non_subrange;
	    end;
	  end;
	  new2(Fstrp, Subrange);
	  ConstantExpression(Fsys+[Rangesy], Lstrp, Lvalu);
	  if Strng(Lstrp) then begin
	    Error(303);
	    Lstrp := nil;
	  end;
	  with Fstrp^ do begin
	    Form := Subrange;
	    ifd := -1;
	    packifd := -1;
	    Wheredeclared := Memblock;
	    Hasholes := false;
	    Hasfiles := false;
	    Stsize := Intptr^.Stsize;
	    Align := Intptr^.Align;
	    Hosttype := Lstrp;
	    Vmin := Lvalu.Ival;
	    if Lstrp <> nil then begin
	      Stdtype := Lstrp^.Stdtype;
	    end;
	  end {with};
	  if Sy = Rangesy then begin
	    Insymbol;
	  end else begin
	    Error(151);
	  end;
	  if Lstrp <> nil then begin
	    Sizeofsubrange(Fstrp);
	  end;
#if 0
	end;
#endif
non_subrange:
	if Fstrp <> nil then begin	(* check that Vmin <= Vmax *)
	  with Fstrp^ do begin
	    if (Form = Subrange)
	        and (Hosttype <> nil)
		and (Vmin > Vmax) then begin
	      Error(451);
	    end;
	  end {with};
	end;
      end;
      Iferrskip(166, Fsys);
    end;
  end {procedure Simpletype};

(*Fieldlist,Recsection*)
(************************************************************************)
(*									*)
(*	FIELDLIST -- parses the list of fields in the definition of a	*)
(*		     record or one of its variants			*)
(*									*)
(*	On return, Ffirstfield points to the list of fields for the	*)
(*	fixed part of the record, and Tagstrp points to the Tagwithid	*)
(*	or the Tagwithoutid for the variant part. Recsize is the	*)
(*	size of the record.  It also acts as a counter, and MUST be	*)
(*	initialized by the calling procedure.				*)
(*									*)
(************************************************************************)
procedure Typedefinition (
	    Fsys : Setofsys;
	var Fstrp : Strp);
  forward;

procedure Fieldlist (
	    Fsys : Setofsys;
	    Packflag : boolean;
	var Tagstrp : Strp;
	var Ffirstfield : Idp;
	var Recsize : integer;
	var Recalign : integer;
	var FHoles,
	    FFiles : boolean);
  label
    555;
  var
    Lidp, Tagidp, Sametypelist, Lastfield : Idp;
    Minsize, Maxsize : Sizerange;
    Caselisthead, Caselisttail, Sametypehead, Lstrp, Tagtype,
	  Lsubvarlist : Strp;
    Lvalu : Valu;
    Lid : Identname;

  procedure Recsection (
	      Fidp : Idp);
    (* Allocates memory for the field pointed to by fidp. Increments Recsize *)
    (* to reflect the new allocation					     *)
    var
      Asize, Align : integer;
      Oldrecsize : integer;
    begin				(* recsection			     *)
      Oldrecsize := Recsize;
      if Fidp^.Idtype <> nil then begin
	if not Packflag then begin
	  Asize := Fidp^.Idtype^.Stsize;
	  Align := Fidp^.Idtype^.Align;
	end else begin
	  Asize := Fidp^.Idtype^.Packsize;
	  Align := max(Fidp^.Idtype^.Packalign, Rpackunit);
	  (* pack records no closer than specified			     *)
	end;
#if 0
	(* If record or array, make sure it begins on an addrunit boundary.  *)
	if Fidp^.Idtype^.Stdtype = Mdt then begin
	  Align := max(Align, Addrunit);
	end;
#endif
	Recsize := Alignobject(Recsize, Asize, Align);
	Recalign := max(Recalign, Fidp^.Idtype^.Align);
	FHoles := FHoles or (Oldrecsize <> Recsize);
	Fidp^.Inpacked := Packflag;
	Fidp^.Fldaddr := Recsize;
	Fidp^.Fieldsize := Asize;
	Recsize := Recsize+Asize;
      end;
    end {procedure Recsection};

  function OkVariantTag (
	     Fvalu : Valu)
     : boolean;
    var
      bad : boolean;
    begin
      if Tagtype = nil then return(false);
      bad := true;
      case Tagtype^.Form of
        Scalar : begin
	  if Tagtype^.Scalkind = Standrd then begin
	    bad := (Tagtype = Cardinalptr) and (Fvalu.Ival < 0);
	  end else begin (* enumerated *)
	    bad :=  Fvalu.Ival > Tagtype^.Dimension;
          end;
        end;
        Subrange : begin
          bad := (Fvalu.Ival < Tagtype^.Vmin) or (Fvalu.Ival > Tagtype^.Vmax);
        end;
      end {case};
      return (not bad);
    end {function OkVariantTag};

  function DuplicateTag (
	     Fvalu : Valu)
     : boolean;
    var
      Lstrp : Strp;
    begin
      Lstrp := Caselisthead;
      while Lstrp <> nil do begin
        if Fvalu.Ival = Lstrp^.Varval then return(true);
	Lstrp := Lstrp^.Nxtvar;
      end {while}; 
      return false;
    end {function DuplicateTag};

  begin 				(* fieldlist			     *)

    (*************************************************************************)
    (* FIRST PART -- get the fixed parts of the record			     *)
    (*************************************************************************)

    Ffirstfield := nil;
    while Sy = Semicolonsy do begin
      Insymbol;
    end {while};
    Skipiferr(Fsys+[Identsy, Casesy], 452, Fsys);
    (* a fieldlist consists of an arbitrary number of fixed parts followed   *)
    (* by AT MOST one case variant					     *)
    while Sy = Identsy do begin 	(* for each field		     *)
      Sametypelist := nil;
      (* get a list of IDs separated by commas at the end, Sametypelist      *)
      (* points to a backwards chain of IDs				     *)
      repeat
	if Sy = Commasy then begin
	  Insymbol;
	end;
	if Sy = Identsy then begin
	  new2(Lidp, Field);
	  with Lidp^ do begin
	    Klass := Field;
	    Idname := Id;
	    symndx := 0;
	    Idtype := nil;
	    Next := nil;
	  end {with};
	  if Ffirstfield = nil then begin
	    Ffirstfield := Lidp;
	  end else begin
	    Lastfield^.Next := Lidp;
	  end;
	  if Sametypelist = nil then begin
	    Sametypelist := Lidp;
	  end;
	  Lastfield := Lidp;
	  Enterid(Lidp);
	  Insymbol;
	end else begin
	  Error(209);
	end;
	Skipiferr([Commasy, Colonsy], 166, Fsys+[Semicolonsy, Casesy]);
      until Sy <> Commasy;
      if Sy = Colonsy then begin
	Insymbol;
      end else begin
	Error(151);
      end;
      (* parse the type definition for this field; return in LSTRP	     *)
      Typedefinition(Fsys+[Casesy, Semicolonsy], Lstrp);
      if Lstrp <> nil then begin
	FHoles := FHoles or Lstrp^.Hasholes;
	FFiles := FFiles or Lstrp^.Hasfiles;
      end;
      (* hang the type descriptor from all the identifiers and allocate      *)
      (* memory space for them						     *)
      while Sametypelist <> nil do begin
	Sametypelist^.Idtype := Lstrp;
	Recsection(Sametypelist);
	Sametypelist := Sametypelist^.Next;
      end {while};

      while Sy = Semicolonsy do begin
	Insymbol;
	Skipiferr(Fsys+[Identsy, Casesy, Semicolonsy], 452, Fsys);
      end {while};
    end {while};

    (*************************************************************************)
    (* SECOND PART -- get the variant part of the record		     *)
    (*************************************************************************)

    if Sy <> Casesy then begin		(* parse the variant part	     *)
      Tagstrp := nil;
    end else begin			(* tagfield and tag type	     *)
      Tagidp := nil;			(* possibility of no tagfield	     *)
					(* identifier			     *)
      Insymbol;
      if Sy <> Identsy then begin
	Tagstrp := nil;
	Errandskip(209, Fsys+[Lparentsy]);
      end else begin			(* tagfield name and case list type  *)
	Lid := Id;
	Insymbol;
	if (Sy <> Colonsy) and (Sy <> Ofsy) then begin
	  Error(151);
	  Errandskip(160, Fsys+[Lparentsy]);
	end else begin
	  if Sy = Colonsy then begin	(* tagfield exists		     *)
	    new2(Tagstrp, Tagfwithid);
	    Tagstrp^.Form := Tagfwithid;
	    new2(Tagidp, Field);
	    with Tagidp^ do begin
	      Klass := Field;
	      Idname := Lid;
	      symndx := 0;
	      Idtype := nil;
	      Next := nil;
	    end {with};
	    Enterid(Tagidp);
	    Insymbol;
	    if Sy <> Identsy then begin
	      Errandskip(209, Fsys+[Lparentsy]);
	      goto 555;
	    end else begin
	      Lid := Id;
	      Insymbol;
	      if Sy <> Ofsy then begin
		Errandskip(160, Fsys+[Lparentsy]);
		goto 555;
	      end;
	    end;
	  end else begin		(* sy = ofsy. no tagfield exists     *)
	    new2(Tagstrp, Tagfwithoutid);
	    Tagstrp^.Form := Tagfwithoutid;
	  end;
	  with Tagstrp^ do begin
	    ifd := -1;
	    packifd := -1;
	    Wheredeclared := Memblock;
	    Stsize := 0;
	    Align := 0;
	    Hasholes := false;
	    Hasfiles := false;
	    Fstvar := nil;
	    if Form = Tagfwithid then begin
	      Tagfieldp := nil;
	    end else begin
	      Tagfieldtype := nil;
	    end;
	  end {with};
	  Id := Lid;
	  (* find the tag type in the symbol table			     *)
	  Searchid([Types], Lidp);
	  Tagtype := Lidp^.Idtype;
	  if Tagtype <> nil then begin
	    if (Tagtype^.Form > Subrange) then begin
	      Error(402);
	    end else begin		(* scalar or subrange		     *)
	      if Comptypes(Realptr, Tagtype) then begin
		Error(210);
	      end;
	      with Tagstrp^ do begin
		Packsize := Tagtype^.Packsize;
		Packalign := Tagtype^.Packalign;
		if Form = Tagfwithid then begin
		  Tagfieldp := Tagidp;
		end else begin
		  Tagfieldtype := Tagtype;
		end;
	      end {with};
	      if Tagidp <> nil then begin
		Tagidp^.Idtype := Tagtype;
		Recsection(Tagidp);	(* reserves space for the tagfield   *)
	      end;
	    end;
	  end;
	  Insymbol;
	end;
      end;				(* tagfield name and type	     *)

555 :					(* parse each case value; call	     *)
					(* recsection to get field list for  *)
					(* that 			     *)
      (* value								     *)
      Caselisthead := nil;
      Minsize := Recsize;
      Maxsize := Recsize;
      (* Elsevar describes all the variant cases that are not specified,     *)
      (* which have no extra fields and hence have the current value of      *)
      (* Recsize for their size (used for New and Dispose)		     *)
      if Tagstrp <> nil then begin
	new2(Lstrp, Variant);
	Lstrp^.Stsize := Recsize;
	Tagstrp^.Elsevar := Lstrp;
      end;
      while Sy = Semicolonsy do begin
	Insymbol;
      end {while};
      repeat
	Sametypehead := nil;
	repeat				(* parse the list of values	     *)
	  if Sy = Commasy then begin
	    Insymbol;
	  end;
	  ConstantExpression(Fsys+[Commasy, Colonsy, Lparentsy], Lstrp, Lvalu);
	  if not Comptypes(Tagtype, Lstrp) then begin
	    Error(305);
	  end else if not OkVariantTag(Lvalu) then begin
	    Error(305);
	  end;
	  if DuplicateTag(Lvalu) then begin
	    Error(261);
	  end;
	  new2(Lstrp, Variant);
	  with Lstrp^ do begin
	    Form := Variant;
	    ifd := -1;
	    packifd := -1;
	    Wheredeclared := Memblock;
	    Varval := Lvalu.Ival;
	    Nxtvar := nil;
	    if Tagstrp <> nil then begin
	      Packsize := Tagstrp^.Packsize;
	      Packalign := Tagstrp^.Packalign;
	    end;
	  end {with};
	  if Sametypehead = nil then begin
	    Sametypehead := Lstrp;
	  end;
	  if Caselisthead = nil then begin
	    Caselisthead := Lstrp;
	  end else begin
	    Caselisttail^.Nxtvar := Lstrp;
	  end;
	  Caselisttail := Lstrp;
	until Sy <> Commasy;
	if Sy = Colonsy then begin
	  Insymbol;
	end else begin
	  Error(151);
	end;
	if Sy = Lparentsy then begin	(* parse the fieldlist		     *)
	  Insymbol;
	end else begin
	  Error(153);
	end;
	Fieldlist(Fsys+[Rparentsy, Semicolonsy], Packflag, Lsubvarlist, Lidp,
	    Recsize, Recalign, FHoles, FFiles);
	Maxsize := max(Maxsize, Recsize);
	Lstrp := Sametypehead;
	while Lstrp <> nil do begin
	  Lstrp^.Subvar := Lsubvarlist;
	  Lstrp^.Varfirstfield := Lidp;
	  Lstrp^.Stsize := Recsize;
	  Lstrp^.Align := Recalign;
	  Lstrp := Lstrp^.Nxtvar;
	end {while};
	if Sy = Rparentsy then begin
	  Insymbol;
	  Iferrskip(166, Fsys+[Semicolonsy]);
	end else begin
	  Warning(152);
	end;
	while Sy = Semicolonsy do begin
	  Insymbol;
	end {while};
	Recsize := Minsize;
      until Sy in Fsys;
      Recsize := Maxsize;
      if Tagstrp <> nil then begin
	Tagstrp^.Fstvar := Caselisthead;
      end;
    end;

    (*************************************************************************)
    (* make sure the record ends on an addrunit boundary		     *)
    (*************************************************************************)
    Recsize := Roundup(Recsize, Addrunit);
  end {procedure Fieldlist};

(*Typedefinition*)
(************************************************************************)
(*									*)
(*	TYPEDEFINITION -- parses a type definition, and constructs	*)
(*	   a Structure record to describe it.  Returns pointer to	*)
(*	   record in Fstrp.						*)
(*									*)
(************************************************************************)
procedure Typedefinition (* Fsys: Setofsys; VAR Fstrp: Strp  *);
  var
    Lstrp, Lstrp1, Lstrp2 : Strp;
    Oldtop : Disprange;
    Lidp : Idp;
    Lsize, Oldlsize, Lalign : integer;
    Lholes, Lfiles : boolean;
    I, Lmin, Lmax : integer;
    Loopdone, Packflag : boolean;
    Elementsperword : Bitrange;
    junk : integer;
    LNilElement : boolean;

  procedure pointertype ();
    begin
      new2(Fstrp, SPointer);
      with Fstrp^ do begin
	Form := SPointer;
	ifd := -1;
	packifd := -1;
	Wheredeclared := Memblock;
	Eltype := nil;
	Stsize := Pointersize;
	Packsize := Pointersize;
	Align := Pointeralign;
	Packalign := Pointeralign;
	Stdtype := Hdt;
	Hasfiles := false;
	Hasholes := false;
      end {with};
      Insymbol;
      (* The type of the pointer may not have been declared yet, so make   *)
      (* up a temporary record to save its name and a pointer to Fstrp,    *)
      (* and put in on the global Forwardpointertype list. Then, at the    *)
      (* end of all declarations, the list can be used to do the final     *)
      (* binding of Eltype						     *)
      if Sy = Identsy then begin
	new2(Lidp, Types);
	with Lidp^ do begin
	  Klass := Types;
	  Idname := Id;
	  symndx := 0;
	  Idtype := Fstrp;
	  Next := Forwardpointertype;
	end {with};
	Forwardpointertype := Lidp;
	Insymbol;
      end else begin
	Error(209);
      end;
    end {pointertype};

  procedure arraytype ();
    label
      ReverseArrayChainCont;
    begin
      if Sy = Lbracksy then begin
	Insymbol;
      end else begin
	Error(154);
      end;
      Lstrp1 := nil;
      Loopdone := false;	(* parse the subscript type	     *)

      (***************************************************************)
      (* The following gets the subscript types. If there are	     *)
      (* multiple subscripts, e.g. 'ARRAY [1..5,1..6] of CHAR', then *)
      (* the resulting structure must be the same as if it were      *)
      (* 'ARRAY[1..5] of ARRAY[1..6] OF CHAR'. To do this, for each  *)
      (* new subscript, a new Strp of type Array is made and linked  *)
      (* backwards through the field Aeltype. Lstrp1 always points   *)
      (* to the most recent. Later, the chain is reversed so that    *)
      (* the subscripts are in the right order. 		     *)
      (***************************************************************)

      repeat
	(* get next subrange					     *)
	new2(Lstrp, Arrays);
	with Lstrp^ do begin
	  Form := Arrays;
	  Aeltype := Lstrp1;
	  Inxtype := nil;
	  Arraypf := Packflag;
	  Aelsize := Salign; {dummy, so that in case of error, not be left 0}
	  Stsize := 0;
	  Align := 0;
	  Stdtype := Mdt;
	  ifd := -1;
	  packifd := -1;
	  Wheredeclared := Memblock;
	end {with};
	Lstrp1 := Lstrp;
	Simpletype(Fsys+[Commasy, Rbracksy, Ofsy], Lstrp2);

	if Lstrp2 <> nil then begin
	  if Lstrp2^.Form <= Subrange then begin
	    if Lstrp2^.Stdtype in [Rdt, Qdt, Xdt] then begin
	      Error(210);
	      Lstrp2 := nil;
	    end else if (Lstrp2 = Intptr)
	     or (Lstrp2 = Cardinalptr) then begin
	      Error(306);
	      Lstrp2 := nil;
	    end;
	    Lstrp^.Inxtype := Lstrp2;
	  end else begin
	    Error(403);
	    Lstrp2 := nil;
	  end;
	end;
	Loopdone := Sy <> Commasy;
	if not Loopdone then begin
	  Insymbol;
	end;
      until Loopdone;
      if Sy = Rbracksy then begin
	Insymbol;
      end else begin
	Error(155);
      end;
      if Sy = Ofsy then begin
	Insymbol;
      end else begin
	Error(160);
      end;
      Typedefinition(Fsys, Lstrp); (* parse the element type	     *)

      if Lstrp = nil then begin
	Lholes := false;
	Lfiles := false;
	Lsize := 1;
	Lalign := 1;
	LNilElement := true;
      end else begin
	LNilElement := false;
	Lholes := Lstrp^.Hasholes;
	Lfiles := Lstrp^.Hasfiles;
	if Lstrp1^.Arraypf then begin
	  Lsize := max(1, Lstrp^.Packsize); {prevent lsize from becoming 0}
	  Lalign := Lstrp^.Packalign;
	end else begin
	  Lsize := max(1, Lstrp^.Stsize); {prevent lsize from becoming 0}
	  Lalign := Lstrp^.Align;
	end;
      end;
      (* Reverse chain and calculate total size for array. Where     *)
      (* declaration is ARRAY [1..J,1..K,1..L] of M, Lsize will be,  *)
      (* each time through the loop: 1. L * size(M) 2. K * L *	     *)
      (* size(M) 3. j * K * L * size (M)			     *)
      repeat
	with Lstrp1^ do begin
	  Lstrp2 := Aeltype;
	  Aeltype := Lstrp;
	  if LNilElement then goto ReverseArrayChainCont;
	  if Inxtype <> nil then begin
	    Getbounds(Inxtype, Lmin, Lmax);
	    junk := Typetoaux(Inxtype, false, true, false, false);
	    I := Lmax-Lmin+1;
	    if Arraypf then begin (* pack arrays no closer than      *)
				(* specified			     *)
	      Lalign := max(Lalign, Apackunit);
	    end else begin
	      Lalign := max(Lalign, ArrAlign);
	    end;
	    Lsize := Roundup(Lsize, Lalign);
	    (* make sure size of large array elements is a multiple  *)
	    (* of Salign					     *)
	    Oldlsize := Lsize;
	    if Lsize > Salign then begin
	      Lsize := Roundup(Lsize, Salign);
	      Lalign := max(Lalign, Salign);
	      Aelsize := Lsize;
	      Lsize := Lsize*I;
	    end else if Apackeven then begin
	      (* for small array elements, pack evenly or unevenly   *)
	      (* without overlapping words			     *)
	      while Salign mod Lsize <> 0 do begin
		Lsize := Lsize+1;
	      end {while};
	      Aelsize := Lsize;
	      if Lsize mod Addrunit <> 0 then begin
		Lalign := max(Lalign, Wordsize);
	      end else begin
		Lalign := max(Lalign, Lsize);
	      end;
	      Lsize := Lsize*I;
	      Lsize := Roundup(Lsize, Lalign);
	    end else begin	(* uneven packing		     *)
	      Elementsperword := Salign div Lsize;
	      if Elementsperword = 1 then begin
		Lsize := Salign;
	      end;
	      Aelsize := Lsize;
	      Lsize := (I div Elementsperword)*Salign+(I mod
		  Elementsperword)*Lsize;
	    end;
	    (* arrays must always end on an addrunit boundary	     *)
	    Lsize := Roundup(Lsize, Addrunit);
	    Hasholes := Lholes or (Oldlsize*I <> Lsize);
	    Hasfiles := Lfiles;
	    Packsize := Lsize;
	    Stsize := Lsize;
	    Align := Lalign;
	    Packalign := Lalign;
	  end else begin { to prevent crashing later with div by 0 }
	    Packsize := Intsize;
	    Stsize := Intsize;
	    Align := Intalign;
	    Packalign := Intalign;
	    Aelsize := Intsize;
	  end;
	end {with};
ReverseArrayChainCont:
	Lstrp := Lstrp1;
	Lstrp1 := Lstrp2;
      until Lstrp1 = nil;
      Fstrp := Lstrp;
    end {arraytype};

  begin 				(* typedefinition		     *)
    Fstrp := nil;
    Skipiferr(Typebegsys, 170, Fsys);
    if Sy in Typebegsys then begin
      if Sy in Simptypebegsys then begin
	Simpletype(Fsys, Fstrp);
      end else if Sy = Arrowsy then begin (* pointer type		     *)
	pointertype ();
      end else begin			(* structured types		     *)
	if Sy = Packedsy then begin	(* packed			     *)
	  Insymbol;
	  Skipiferr(Typedels, 170, Fsys);
	  Packflag := true;
	end else begin
	  Packflag := false;
	end;
	if Sy in [Arraysy, Recordsy, Setsy, Filesy] then begin
	  case Sy of
	  Arraysy : begin		(* array type			     *)
	      Insymbol;
	      arraytype ();
	    end {case Arraysy};
	  Recordsy : begin		(* record type			     *)
	      Insymbol;
	      (* Push a new entry onto the display to hold the fields of the *)
	      (* new record						     *)
	      Oldtop := Top;
	      if Top < Displimit then begin
		Top := Top+1;
		Display[Top].Fname := nil;
		Display[Top].Occur := Crec;
	      end else begin
		Error(404);
	      end;
	      Lsize := 0;
	      Lalign := 1;
	      Lholes := false;
	      Lfiles := false;
	      Fieldlist(Fsys-[Semicolonsy]+[Endsy], Packflag, Lstrp, Lidp,
		  Lsize, Lalign, Lholes, Lfiles);
	      Lsize := Roundup(Lsize, Lalign);
	      new2(Fstrp, Records);
	      with Fstrp^ do begin
		Form := Records;
		Stdtype := Mdt;
		ifd := -1;
		packifd := -1;
		Wheredeclared := Memblock;
		(* if we assigned Lidp, records with no fixed part would     *)
		(* lose 						     *)
		Recfirstfield := Display[Top].Fname;
		Recvar := Lstrp;
		Stsize := Lsize;
		Packsize := Lsize;
		Recordpf := Packflag;
#if 0
		if Packflag then Lalign := max(Lalign, Wordsize);
#endif
		Align := Lalign;
		Packalign := Lalign;
		Hasholes := Lholes;
		Hasfiles := Lfiles;
	      end {with};
	      Top := Oldtop;
	      if Sy = Endsy then begin
		Insymbol;
	      end else begin
		Error(163);
	      end;
	    end {case Recordsy};
	  Setsy : begin 		(* set type			     *)
	      Insymbol;
	      if Sy = Ofsy then begin
		Insymbol;
	      end else begin
		Error(160);
	      end;
	      Simpletype(Fsys, Lstrp);
	      (* defaults in case of error:				     *)
	      Lmin := 0;
	      Lmax := Defsetsize-1;
	      if Lstrp <> nil then begin
		with Lstrp^ do begin
		  if Form = Scalar then begin
		    if Scalkind = Standrd then begin
		      if Lstrp = Charptr then begin
			Lmax := Tgtlastchar;
			Lmin := Tgtfirstchar;
		      end else begin
			Error(177);
		      end;
		    end else begin	(* enumerated types		     *)
		      Lmax := Dimension;
		      Lmin := 0;
		    end;
		  end else if Form = Subrange then begin
		    if (Hosttype = Realptr) or (Hosttype = Doubleptr)
		     or (Hosttype = Extendedptr) then begin
		      Error(177);
		    end else begin
		      Lmin := Vmin;
		      Lmax := Vmax;
		    end;
		  end else begin	(* not Subrange or Scalar	     *)
		    Error(461);
		    Lstrp := nil;
		  end;
		end {with};
	      junk := Typetoaux(Lstrp, false, true, false, false);
	      end;
	      (* make sure LMIN begins on SETUNIT boundary		     *)
	      if Lmin mod Setunitsize <> 0 then begin
		if Lmin >= 0 then begin
		  Lmin := (Lmin div Setunitsize)*Setunitsize;
		end else begin
		  Lmin := (Lmin div Setunitsize-1)*Setunitsize;
		end;
	      end;
	      new2(Fstrp, Power);
	      with Fstrp^ do begin
		Form := Power;
		Stdtype := Sdt;
		ifd := -1;
		packifd := -1;
		Wheredeclared := Memblock;
		Hasfiles := false;
		Hasholes := false;
		Basetype := Lstrp;
		Hardmin := Lmin;
		Hardmax := Lmax;
		Packsize := Hardmax-Hardmin+1;
		Align := Salign;
		(* round unpacked size up to nearest SETUNIT		     *)
		if Packsize mod Setunitsize <> 0 then begin
		  Stsize := (Packsize div Setunitsize+1)*Setunitsize;
		end else begin
		  Stsize := Packsize;
		end;
		if Stsize > Maxsetsize then begin
		  Error(177);
		  Stsize := Defsetsize;
		end;
		(* if large set, do not pack				     *)
		if Packsize >= Salign then begin
		  Packsize := Stsize;
		  Packalign := Salign;
		end else begin		(* otherwise, calculate packed size  *)
		  Packsize := max(Packsize, Psetsize);
		  Packalign := Rpackunit;
		  while Packsize mod Rpackunit > 0 do begin
		    Packsize := Packsize+1;
		  end {while};
		end;
		Softmin := Hardmin;
		Softmax := Stsize+Hardmin-1;
	      end {with};
	    end {case Setsy};
	  Filesy : begin		(* file type			     *)
	      Insymbol;
	      if Sy = Ofsy then begin
		Insymbol;
	      end else begin
		Error(160);
	      end;
	      Typedefinition(Fsys, Lstrp);
	      if Lstrp = nil then begin
		Lsize := 0;
	      end else if Packflag then begin
		Lsize := Roundup(Lstrp^.Packsize, Fpackunit);
		Lalign := Lstrp^.Packalign;
	      end else begin
		Lsize := Lstrp^.Stsize;
		Lalign := Lstrp^.Align;
	      end;
	      new2(Fstrp, Files);
	      with Fstrp^ do begin
		ifd := -1;
		packifd := -1;
		Wheredeclared := Memblock;
		Form := Files;
		Stdtype := Mdt;
		Componentsize := Lsize;
		Hasfiles := true;
		Hasholes := false;
		(* size of file buffer is Fdbsize + room for one record from *)
		(* the file						     *)
		Lsize := Roundup(Lsize, Addrunit);
		Filetype := Lstrp;
		Stsize := Filesize;
		Filepf := Packflag;
		Packsize := Filesize;
		Align := Filealign;
		Packalign := Filealign;
		Textfile := false;
#if 0
		if (Filetype <> nil)
		    and (Filetype^.Form = Records)
		    and (Filetype^.Recfirstfield^.Idname = 'PBUFFER         ')
		    then begin
		      Textfile := true;
		end;
#endif
	      end {with};
	    end {case Filesy};
	  end {case};
	end;
      end;
      Iferrskip(166, Fsys);
    end;				(* sy in typebegsys		     *)
  end {procedure Typedefinition};

(*Resolvepointers,Labeldecl,Constantdecl,Typedecl,Variabledecl*)
(************************************************************************)
(*									*)
(*	DECLARATIONS MODULE  -- handles Label, Const, Type, Var,	*)
(*	    Procedure, and Function declarations			*)
(*									*)
(*	Principle procedures are: Labeldeclaration, Constdeclaraton,	*)
(*	    Typedeclaration, Vardeclaration, and Proceduredeclaration.	*)
(*	Procedure Resolvepointers is called at the end of a set of	*)
(*	    Type or Var definitions to resolve all pointer type 	*)
(*	    references							*)
(*									*)
(************************************************************************)
procedure Resolvepointers;
  (* For each pointer type that was declared, find the type and patch up     *)
  (* Eltype in the pointer structure record to point to it		     *)
  var
    Lidp : Idp;
  begin
    while Forwardpointertype <> nil do begin
      Searcherror := false;
      Id := Forwardpointertype^.Idname;
      Searchid([Types], Lidp);
      Searcherror := true;
      if Lidp = nil then begin
	Errorwithid(405, Forwardpointertype^.Idname);
      end else if Lidp^.Idtype <> nil then begin
	Lidp^.referenced := true;
	Forwardpointertype^.Idtype^.Eltype := Lidp^.Idtype;
      end;
      Forwardpointertype := Forwardpointertype^.Next;
    end {while};
    Resolveptrauxes;
  end {procedure Resolvepointers};


procedure Labeldeclaration /* (Fsys: Setofsys)	*/;
  (* parses a set of label declarations 				     *)
  var
    Lidp : Idp;
    Loopdone : boolean;
  begin 				(* labeldeclaration		     *)
    Loopdone := false;
    repeat
      if (Sy = Intconstsy) or (Sy = Identsy) then begin
	new2(Lidp, Labels);
	with Lidp^ do begin
	  Klass := Labels;
	  Scope := Level;
	  Idname := Id;
	  symndx := st_idn_index_fext(
		st_symadd(Symaddstr(Id), 0/*value*/,
			stLabel, scText, indexNil/* no type info*/),
		0/*local*/);
	  Idtype := nil;
	  Referenced := false;
	  Defined := false;
	  Next := nil;
	  Externallab := false;
	  (* allocate a label number for it				     *)
	  Lastuclabel := Lastuclabel+1;
	  Uclabel := Lastuclabel;
	end {with};
	Enterid(Lidp);
	Insymbol;
      end else begin
	Error(255);
      end;
      Iferrskip(166, Fsys+[Commasy, Semicolonsy]);
      Loopdone := Sy <> Commasy;
      if not Loopdone then begin
	Insymbol;
      end;
    until Loopdone;
    if Sy = Semicolonsy then begin
      Insymbol;
    end else begin
      Warning(156);
    end;
  end {procedure Labeldeclaration};

procedure Constantdeclaration /* (Fsys: Setofsys)  */;
  (* parses a set of constant declarations				     *)
  var
    I : integer;
    Lidp : Idp;
    Lstrp : Strp;
    Lvalu : Valu;
    Lisordinal : boolean;
    Lname : Identname;
  begin 				(* constantdeclaration		     *)
    Skipiferr([Identsy], 209, Fsys);
    while Sy = Identsy do begin
      Lname := Id;
      Insymbol;
      if Sy = Eqsy then begin
	Insymbol;
      end else begin
	Error(157);
      end;

      ConstantExpression(Fsys+[Semicolonsy], Lstrp, Lvalu);
      Lisordinal := Lstrp^.Stdtype in [Adt, Hdt, Jdt, Ldt];
      if Lisordinal then begin
	new3(Lidp, Konst, true);
      end else begin
	new3(Lidp, Konst, false);
      end;
      with Lidp^ do begin
	Klass := Konst;
	Idname := Lname;
	symndx := 0;
	Next := nil;
	Referenced := false;
	Isordinal := Lisordinal;
	if Lisordinal then begin
	  Ival := Lvalu.Ival;
	end else begin
	  Sval.Len := Lvalu.Ival;
	  new1(Sval.Chars);
	  Sval.Chars^.ss := Lvalu.Chars^.ss;
	end;
	Idtype := Lstrp;
      end {with};
      Enterid(Lidp);
      if debugging_symbols then begin (* enter in symbol table *)
	Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), 0, 
		    stConstant, scData, Typetoaux(Lstrp, false, true, false, false));
	Lidp^.symndx := st_idn_index_fext(Lidp^.symndx, 0);
	if Lstrp^.Align > Wordsize then begin
	  Ucosym(Ulsym, Lidp^.symndx, 3, Lstrp^.Stsize div Bytesize)
	end else begin
	  Ucosym(Ulsym, Lidp^.symndx, 2, Lstrp^.Stsize div Bytesize);
	end;
        Ucoinit(Lstrp^.Stdtype, Lidp^.symndx, 0, 0, Lstrp^.Stsize, Lvalu);
      end;
#if 0
      if debugging_symbols then begin (* enter in symbol table *)
	if Lidp^.Isordinal then begin
	  Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), Lidp^.Ival, 
				    stConstant, scInfo, 0);
	end;
      end;
#endif
      if Sy = Semicolonsy then begin
	Insymbol;
	Iferrskip(166, Fsys+[Identsy]);
      end else begin
	Warning(156);
      end;
    end {while};
  end {procedure Constantdeclaration};

procedure Typedeclaration /* (Fsys: Setofsys)  */;
  (* parses a set of type declarations					     *)
  var
    Lidp : Idp;
    Lstrp : Strp;
    junk : integer;

  begin 				(* typedeclaration		     *)
    Skipiferr([Identsy], 209, Fsys);
    while Sy = Identsy do begin 	(* parse the type declaration	     *)
      new2(Lidp, Types);
      with Lidp^ do begin
	Klass := Types;
	Idname := Id;
	symndx := 0;
	Next := nil;
	Referenced := false;
      end {with};
      Insymbol;
      if Sy = Eqsy then begin
	Insymbol;
      end else begin
	Error(157);
      end;

      Typedefinition(Fsys+[Semicolonsy], Lstrp);

      Lidp^.Idtype := Lstrp;
      Enterid(Lidp);
      if debugging_symbols then begin (* enter in symbol table *)
	if Lidp^.Idtype^.Form = Records then begin
	  junk := Typetoaux(Lidp^.Idtype, false, false, false, false);
	  st_fixiss(Lidp^.Idtype^.recidn, Symaddstr(Lidp^.Idname));
	end else if Lidp^.Idtype^.Form = Scalar then begin
	  junk := Typetoaux(Lidp^.Idtype, false, false, false, false);
	  if Lidp^.Idtype^.Scalkind <> Standrd then begin
	    st_fixiss(Lidp^.Idtype^.Scalaridn, Symaddstr(Lidp^.Idname));
	  end;
	end else begin
	  Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), 0, stTypedef, 
			scInfo, Typetoaux(Lidp^.Idtype, false, true, false, false));
	end;
      end;
      if Sy = Semicolonsy then begin
	Insymbol;
	Iferrskip(166, Fsys+[Identsy, Eofsy]);
      end else begin
	Warning(156);
      end;
    end {while};

    (*************************************************************************)
    (* resolve forward pointer references				     *)
    (*************************************************************************)
    Resolvepointers;
  end {procedure Typedeclaration};

type
  Valulist = ^Valulistrec;
  Valulistrec =
      record
	next : Valulist;
	offset : Addrrange;
	size : Sizerange;
	Cstrp : Strp;
	Cvalu : Valu;
      end {record};


function MatchInitType (
	   Fstrp1 : Strp;
       var Fstrp2 : Strp;
       var Fvalu : Valu
    ): boolean;
  label
    err;
  var i: integer;
  begin
    if (Fstrp1 = nil) or (Fstrp2 = nil) then return false;
    if Fstrp1 = Fstrp2 then return true;
    if Fstrp1^.Form = Fstrp2^.Form then begin
      case Fstrp1^.Form of
      Scalar :
	begin
	  if Fstrp1^.Scalkind = Declared then goto err;
	  if not (
		     (    ((Fstrp1^.Stdtype = Ldt) or (Fstrp1^.Stdtype = Jdt))
		      and ((Fstrp2^.Stdtype = Ldt) or (Fstrp2^.Stdtype = Jdt)))
		  or (    ((Fstrp1^.Stdtype = Rdt) or (Fstrp1^.Stdtype = Qdt))
		      and ((Fstrp2^.Stdtype = Rdt) or (Fstrp2^.Stdtype = Qdt)))
	  ) then goto err;
	  Fstrp2 := Fstrp1;	{ convert types }
	end {case Scalar};
      SPointer : begin
	  if Fstrp2 <> Nilptr then goto err;
	  Fstrp2 := Fstrp1;
	end;
      Subrange : begin
	  if not Comptypes(Fstrp1^.Hosttype, Fstrp2^.Hosttype) then goto err;
	  Fstrp2 := Fstrp1;
	end;
      Power : begin
	  if not Comptypes(Fstrp1^.Basetype, Fstrp2^.Basetype) then goto err;
	  if (Fstrp2^.Softmin <> Fstrp1^.Softmin)
	  or (Fstrp2^.Stsize <> Fstrp1^.Stsize) then begin
	    Shiftset(Fvalu, Fstrp2^.Softmin-Fstrp1^.Softmin, Fstrp1^.Stsize);
	    Fstrp2 := Fstrp1;
	  end;
	end;
      Arrays : begin
	  if not (Strng(Fstrp1) and Strng(Fstrp2)) then goto err;
	  if (Fstrp1^.Inxtype = nil) or (Fstrp2^.Inxtype = nil) then return false;
	  if (Fstrp2^.Inxtype^.Vmax > Fstrp1^.Inxtype^.Vmax) then goto err;
	  if (Fstrp2^.Inxtype^.Vmax < Fstrp1^.Inxtype^.Vmax) then begin
	    assert (Fvalu.Ival = Fstrp2^.Inxtype^.Vmax);
	    { extend the literal constant }
	    repeat
	      Fvalu.Ival := Fvalu.Ival+1;
	      Fvalu.Chars^.ss[Fvalu.Ival] := ' ';
	    until Fvalu.Ival = Fstrp1^.Inxtype^.Vmax;
	    Fstrp2^.Inxtype^.Vmax := Fvalu.Ival;
	    Fstrp2^.Stsize := Fvalu.Ival * Charsize;
	    Fstrp2 := Fstrp1;
	  end;
	end {case Arrays};
      otherwise :
	goto err;
      end {case};
    end else if Fstrp1^.Form = Subrange then begin
      if not Comptypes(Fstrp1^.Hosttype, Fstrp2) then goto err;
      Fstrp2 := Fstrp1;
      return true;
    end else if Fstrp2^.Form = Subrange then begin
      if not Comptypes(Fstrp1, Fstrp2^.Hosttype) then goto err;
      Fstrp2 := Fstrp1;
      return true;
    end else if Strng(Fstrp1) and Comptypes(Fstrp2, Charptr) then begin
      if Fstrp1^.Inxtype = nil then return false;
      new1 (Fvalu.Chars);
      for i := 1 to Strglgth do
        Fvalu.Chars^.ss[i] := ' ';
      Fvalu.Chars^.ss[1] := chr(Fvalu.Ival);
      Fvalu.Ival := Fstrp1^.Inxtype^.Vmax;
      Fstrp2 := Fstrp1;
    end else begin
      goto err;
    end;
    return true;
err:
    Error (454);
    return false;
  end {function MatchInitType};

function Initialvalue (
	   Fsys : Setofsys;
	   Fstrp : Strp)
   : Valulist;
  var
    v, p, firstv, prevv : Valulist;
    Dstrp : Strp;
    Dvalu : Valu;
    i, Vmin, Vmax, shiftamt : integer;
    warn : boolean;
  label
    exitloop,
    next;
  begin
    if (Fstrp^.Form <> Arrays) or (Sy <> Lbracksy) then begin
      new1 (v);
      v^.offset := 0;
      v^.next := nil;
      ConstantExpression (Fsys+[Semicolonsy]+Typedels, v^.Cstrp, v^.Cvalu);
      if not MatchInitType(Fstrp, v^.Cstrp, v^.Cvalu) then begin
	v := nil;
      end else begin
	v^.size := v^.Cstrp^.Stsize;
      end;
      return v;
    end;

    { Array initialization }

    Insymbol;
    { Parse element specs and keep sorted list of values.  Firstv is
      smallest element spec, prevv is last spec at current position.
      I is current array index. }
    firstv := nil;
    prevv := nil;
    Dstrp := nil;
    Getbounds (Fstrp^.Inxtype, Vmin, Vmax);
    if Sy <> Rbracksy then begin
      i := Vmin;
      while true do begin
	new1(v);
	if Sy = Otherwisesy then begin
	  Insymbol;
	  if Sy <> Colonsy then Warning(180) else Insymbol;
	  { Default element value specified.  Put value in Dvalu and process
	    at end. }
	  if Dstrp <> nil then Error (560);
	  ConstantExpression(Fsys+[Commasy,Colonsy,Rbracksy], Dstrp, Dvalu);
	  if not MatchInitType(Fstrp^.Aeltype, Dstrp, Dvalu) then begin
	    Dstrp := nil;
	  end;
	  goto next;
	end;
	ConstantExpression(Fsys+[Commasy,Colonsy,Rbracksy], v^.Cstrp, v^.Cvalu);
	if Sy = Colonsy then begin
	  Insymbol;
	  if not Comptypes(v^.Cstrp, Fstrp^.Inxtype) then Error(372);
	  i := v^.Cvalu.Ival;
	  ConstantExpression(Fsys+[Commasy,Rbracksy], v^.Cstrp, v^.Cvalu);
	  if (prevv <> nil) and (prevv^.offset < i) then begin
	    p := prevv^.next;
	  end else begin
	    prevv := nil;
	    p := firstv;
	  end;
	  while (p <> nil) and (p^.offset < i) do begin
	    prevv := p;
	    p := p^.next;
	  end {while};
	end;
	if (i < Vmin) or (i > Vmax) then begin
	  Error (467);
	  goto next;
	end;
	if MatchInitType (Fstrp^.Aeltype, v^.Cstrp, v^.Cvalu) then begin
	  v^.offset := i;
	  if prevv = nil then begin
	    if (firstv <> nil) and (firstv^.offset = i) then begin
	      Error (373);
	      goto next;
	    end;
	    v^.next := firstv;
	    firstv := v;
	  end else begin
	    if (prevv^.next <> nil) and (prevv^.next^.offset = i) then begin
	      Error (373);
	      goto next;
	    end;
	    v^.next := prevv^.next;
	    prevv^.next := v;
	  end;
	  prevv := v;
	end;
	i := i + 1;
next:
	if Sy <> Commasy then {break}goto exitloop;
	Insymbol;
      end {while};
exitloop: ;
    end;
    if Sy = Rbracksy then Insymbol else Warning(181);
    { Scan list, find holes and either insert default value, or complain. }
    { Also convert array index to bit offset. }
    prevv := nil;
    p := firstv;
    warn := false;
    for i := Vmin to Vmax do begin
      if (p <> nil) and (p^.offset = i) then begin
	p^.offset := (p^.offset - Vmin) * Fstrp^.Aelsize;
#if 0
	p^.Cstrp := Fstrp^.Aeltype;
	p^.size := Fstrp^.Aelsize;
#else
	p^.size := p^.Cstrp^.Stsize;
#endif
	prevv := p;
	p := p^.next;
      end else if Dstrp = nil then begin
	warn := true;
      end else begin
	new1 (v);
	v^.offset := (i - Vmin) * Fstrp^.Aelsize;
#if 0
	v^.Cstrp := Fstrp^.Aeltype;
	v^.size := Fstrp^.Aelsize;
#else
	v^.Cstrp := Dstrp;
	v^.size := Dstrp^.Stsize;
#endif
	v^.Cvalu := Dvalu;
	v^.next := p;
	if prevv = nil then firstv := v else prevv^.next := v;
	prevv := v;
      end;
    end {for};
    if warn then Warning (328);
    { another iteration to process bitwise initialization p moves thru list;  }
    { prevv is the previous node on word boundary			      }
    p := firstv;
    prevv := nil;
    while p <> nil do begin
      if p^.Cstrp^.Stdtype in [Jdt, Ldt] then begin
	if (prevv = nil) or ((p^.offset div Fstrp^.Align) <> 
				(prevv^.offset div Fstrp^.Align))
	  then begin {adjust to word boundary}
	  shiftamt := p^.offset mod Fstrp^.Align;
	  p^.offset := p^.offset - shiftamt;
	  p^.size := min(p^.offset + Fstrp^.Align, Fstrp^.Stsize) - p^.offset;
	  if lsb_first then begin
	    p^.Cvalu.Ival := lshift(p^.Cvalu.Ival, shiftamt);
	  end else begin
	    p^.Cvalu.Ival := lshift(p^.Cvalu.Ival, 
				p^.size - shiftamt - Fstrp^.Aelsize);
	  end;
	  prevv := p;
	end else begin {combine bits into the previous node}
	  shiftamt := p^.offset mod Fstrp^.Align;
	  if lsb_first then begin
	    prevv^.Cvalu.Ival := bitor(prevv^.Cvalu.Ival, 
				      lshift(p^.Cvalu.Ival, shiftamt));
	  end else begin
	    prevv^.Cvalu.Ival := bitor(prevv^.Cvalu.Ival, 
	      lshift(p^.Cvalu.Ival, prevv^.size - shiftamt - Fstrp^.aelsize));
	  end;
	  prevv^.next := p^.next; {delete the node}
	end;
      end else begin
	prevv := nil;
      end;
      p := p^.next;
      end;
    return firstv;
  end {function Initialvalue};

procedure Variabledeclaration /* (Fprocp: Idp; Fsys: Setofsys)	*/;

  (***************************************************************************)
  (* Parses a set of variable declarations, assigning memory to each	     *)
  (* variable. Also builds a list of files declared for this block.	     *)
  (***************************************************************************)
  var
    Lidp, Sametypehead, Sametypetail : Idp;
    Lstrp : Strp;
    Ivalu : Valu;
    Lsize : Sizerange;
    Loopdone : boolean;
    Tfilelisthead, Tfilelisttail : Idp; (* list of files		     *)
    loga : 0..3;
    SavedV, v, t : Valulist;
  begin 				(* variabledeclaration		     *)
    Tfilelisthead := nil;
    repeat
      Loopdone := false;		(* get a list of ids, separated by   *)
					(* commas			     *)
      Sametypehead := nil;
      repeat
	if Sy = Identsy then begin
	  new2(Lidp, Vars);
	  with Lidp^ do begin
	    Klass := Vars;
	    Idname := Id;
	    symndx := 0;
	    Next := nil;
	    Idtype := nil;
	    Vkind := Actual;
	    Vblock := Memblock;
	    Referenced := false;
	    Assignedto := false;
	    Isparam := false;
	    Loopvar := false;
	    Vexternal := false;
	  end {with};
	  Enterid(Lidp);
	  if Sametypehead = nil then begin
	    Sametypehead := Lidp;
	  end else begin
	    Sametypetail^.Next := Lidp;
	  end;
	  Sametypetail := Lidp;
	  Insymbol;
	end else begin
	  Error(209);
	end;
	Skipiferr(Fsys+[Commasy, Colonsy]+Typedels, 166, [Semicolonsy]);
	Loopdone := Sy <> Commasy;
	if not Loopdone then begin
	  Insymbol;
	end;
      until Loopdone;

      (***********************************************************************)
      (* get the type for this list					     *)
      (***********************************************************************)
      if Sy = Colonsy then begin
	Insymbol;
      end else begin
	Error(151);
      end;
      Typedefinition(Fsys+[Semicolonsy, Becomessy]+Typedels, Lstrp);

      v := nil;
      if (Sy = Becomessy) and not Standrdonly and (Lstrp <> nil) then begin
	if Memblock <> 0 then Error(504);
	Insymbol;
	v := Initialvalue(Fsys+[Semicolonsy]+Typedels, Lstrp);
      end;

      (***********************************************************************)
      (* assign memory to each variable in the list			     *)
      (***********************************************************************)
      while Sametypehead <> nil do begin
	with Sametypehead^ do begin
	  Idtype := Lstrp;		(* hand the type from the idname     *)
	  Vmty := Zmt;
	  Vaddr := 0;
	  if Lstrp <> nil then begin
	    if Vblock = 0 then begin
	      (* before entry into any procedure or the program block *)
	      Vmty := Smt;
	      if v <> nil then begin {initialized}
	        (* re-set Vblock to its own gsym block number *)
		symndx := st_extadd(Symaddextstr(Idname), 0,
		      stGlobal, scData, Typetoaux(Idtype, false, true, false, false));
		Vblock := st_idn_index_fext(symndx, 1);
		case Lstrp^.Align of
		  Addrunit : loga := 0;
		  Addrunit*2 : loga := 1;
		  Wordsize : loga := 2;
		  Wordsize*2 : loga := 3;
		end {case};
		Ucosym(Ugsym, Vblock, loga, Lstrp^.Stsize div Bytesize);
		SavedV := v; (* for dispose *)
		repeat
		  with v^ do begin
		    Ucoinit(Cstrp^.Stdtype, Vblock, offset, offset, 
				size, Cvalu);
		  end {with};
		  v := v^.next;
		until v = nil;
		v := SavedV;
	      end else begin
	        (* re-set Vblock to its own csym block number *)
		symndx := st_extadd(Symaddextstr(Idname), 
		    Idtype^.Stsize div Addrunit, 
		    stGlobal, scCommon, Typetoaux(Idtype, false, true, false, false));
		Vblock := st_idn_index_fext(symndx, 1);
		Ucosym(Ucsym, Vblock, 0, Lstrp^.Stsize div Bytesize);
	      end;
	    end else begin
	      Vmty := Mmt;
	      Vaddr := Assignnextmemoryloc(Vmty, Lstrp^.Stsize, Lstrp^.Align);
	      if debugging_symbols then (* enter in symbol table *)
	        symndx := st_symadd(Symaddstr(Idname), Vaddr div Addrunit, 
			stLocal, scAbs, Typetoaux(Idtype, false, true, false, false));
	    end;
	    if (Lstrp^.Hasfiles) or (Lstrp^.Hasholes) then begin
	      if Tfilelisthead = nil then begin
		Tfilelisthead := Sametypehead;
	      end else begin
		Tfilelisttail^.Next := Sametypehead;
	      end;
	      Tfilelisttail := Sametypehead;
	    end;
	  end;
	  Sametypehead := Next;
	end {with};
      end {while};

#if 0
      while v <> nil do begin
	t := v;
	v := v^.next;
	dispose (t);
      end {while};
#endif
      if Sy = Semicolonsy then begin
	Insymbol;
	Iferrskip(166, Fsys+[Identsy, Eofsy]);
      end else begin
	Warning(156);
      end;
    until not (Sy in Typedels+[Identsy]);

    (*************************************************************************)
    (* attach the file list to the Id of the program, procedure, or function *)
    (*************************************************************************)
    if (Fprocp <> nil) and (Tfilelisthead <> nil) then begin
      if Fprocp = Progidp then begin
	Tfilelisttail^.Next := Progidp^.Progfilelist;
	Progidp^.Progfilelist := Tfilelisthead;
      end else begin
	Tfilelisttail^.Next := Fprocp^.Filelist;
	Fprocp^.Filelist := Tfilelisthead;
      end;
    end;
    (* resolve forward pointer references				     *)
    Resolvepointers;
  end {procedure Variabledeclaration};

(*Functiontype,Parameterlist*)
(************************************************************************)
(*									*)
(*	FUNCTIONTYPE: parses the type of a function, and records	*)
(*	  the relevent information in the function's Id (Fidp).         *)
(*	Assigns memory for the function IF it is not the type of	*)
(*	  formal function (that is, a function parameter)		*)
(*									*)
(*	If the function result is too large to pass directly, adds	*)
(*	  an additional reference parameter to the paramter list	*)
(*	  of the function.						*)
(*									*)
(************************************************************************)
procedure Functiontype (
	    Fsys : Setofsys;
	var Fidp : Idp;
	    Formal : boolean);

  var
    Lidp, Lidp2 : Idp;
    Lstrp : Strp;

  begin
    Insymbol;
#if 1
    if Sy <> Identsy then begin
      Errandskip(209, Fsys+[Semicolonsy]);
    end else begin			(* Sy = Identsy 		     *)
      Searchid([Types], Lidp);
      Lidp^.Referenced := true;
      Lstrp := Lidp^.Idtype;
      Insymbol;
#else
      Typedefinition(Fsys+[Semicolonsy], Lstrp);
#endif
      Fidp^.Idtype := Lstrp;
      if Lstrp <> nil then begin
	with Lstrp^ do begin
	  if not (Form in [Scalar, Subrange, SPointer]) then begin
	    Error(551);
	    Fidp^.Idtype := nil;
	  end else if not Formal then begin
	    with Fidp^ do begin
	      Resmemtype := Mmt;
	      Resaddr := Assignnextmemoryloc(Resmemtype, Stsize, Align);
	    end {with};
	  end;
	end {with};
      end;
#if 1
    end;
#endif
  end {procedure Functiontype};

(************************************************************************)
(*									*)
(*	PARAMETERLIST -- parses a list of formal paramters to a 	*)
(*			 procedure or function				*)
(*									*)
(*	A linked list of paramters is created.	Its head is returned	*)
(*	in Fidp, and its tail in Lastidp.  The number is returned in	*)
(*	FParnumber.							*)
(*									*)
(*	The list being parsed may be a real list or it may be a list	*)
(*	for a procedural parameter.  This is indicated by the caller	*)
(*	through the Dummylist parameter.				*)
(*									*)
(************************************************************************)

procedure Parameterlist (
	    Fsys : Setofsys;
	var Fidp : Idp;
	var Fparnumber : integer;
	    Dummylist : boolean);
  var
    Lidp, Lidp2, Lidp3, Paridp, Lastidp : Idp;
    Lstrp : Strp;
    Lkind : Idkind;
    Lklass : Idclass;
    Loopdone, Loop2flag : boolean;
    Lparnumber : integer;
    Lmty : Memtype;
    Laddr : integer;
  begin 				(* parameterlist		     *)
    assert (Forwardpointertype = nil);
    Fidp := nil;
    Lstrp := nil;
    Fparnumber := 0;
    Lastidp := nil;
    Skipiferr(Fsys+[Lparentsy], 256, []);
    if Sy = Lparentsy then begin	(* get parameter list		     *)
      Insymbol;
      if Sy <> Rparentsy then begin
	Skipiferr([Proceduresy, Functionsy, Varsy, Identsy], 256,
	    Fsys+[Rparentsy]);
	if Sy in [Proceduresy, Functionsy, Varsy, Identsy] then begin
	  Loopdone := false;		(* for each parameter		     *)
	  repeat
	    Lidp2 := nil;
	    if Sy in [Proceduresy, Functionsy] then begin (* procedural	     *)
					  (* parameter			     *)
	      if Sy = Proceduresy then begin
		Lklass := Proc;
	      end else begin
		Lklass := Func;
	      end;
	      Insymbol;
	      if Sy <> Identsy then begin
		Errandskip(209, Fsys+[Colonsy, Commasy, Identsy]);
	      end else begin
		Fparnumber := Fparnumber+1;
		new4(Lidp, Proc, Regular, Formal);
		with Lidp^ do begin
		  Klass := Lklass;
		  Prockind := Regular;
		  Nonstandard := false;
		  Idtype := nil;
		  Idname := Id;
		  symndx := 0;
		  Next := nil;
		  Pfkind := Formal;
		  Referenced := false;
		  (* assign memory for the procedure descriptor		     *)
		  if not Dummylist then begin
		    Pfmty := Pmt;
		    Pfaddr := Assignnextmemoryloc(Pfmty, Entrysize, Pointeralign);
		  end;
		  Pfblock := Memblock;
		  Pflev := 0;
		  Fparam := Paridp;
		  Insymbol;
		  if Lklass = Func then begin
		    Parameterlist([Semicolonsy, Colonsy, Rparentsy], Paridp,
			Lparnumber, true);
		  end else begin
		    Parameterlist([Semicolonsy, Rparentsy], Paridp, Lparnumber,
			true);
		  end;
		  Fparam := Paridp;
		  Parnumber := Lparnumber;
		end {with};
		if Lklass = Func then begin
		  if Sy <> Colonsy then begin
		    Error(455);
		  end else begin
		    Functiontype(Fsys, Lidp, true);
		  end;
		end;
		(* add to parameter list					     *)
		if Fidp = nil then begin
		  Fidp := Lidp;
		end else begin
		  Lastidp^.Next := Lidp;
		end;
		Lastidp := Lidp;
		if not Dummylist then begin
		  Enterid(Lidp);
		end;
	      end;
	    end else begin		(* not (sy in [procsy, funcsy]):     *)
					  (* data parameters		     *)
	      if Sy = Varsy then begin	(* reference parameters 	     *)
		Lkind := Formal;
		Insymbol;
	      end else begin
		Lkind := Actual;
	      end;			(* value parameter		     *)
	      Loop2flag := false;
	      (* Get list of ids, separated by commas. At the end, Lidp2 will  *)
	      (* point to the head of this list				     *)
	      repeat
		if Sy <> Identsy then begin
		  Errandskip(209, Fsys+[Colonsy, Commasy, Identsy]);
		end else begin
		  Fparnumber := Fparnumber+1;
		  new2(Lidp, Vars);
		  with Lidp^ do begin
		    Klass := Vars;
		    Idname := Id;
		    symndx := 0;
		    Next := nil;
		    Vkind := Lkind;
		    Vblock := Memblock;
		    Assignedto := false;
		    Referenced := false;
		    Isparam := true;
		    Loopvar := false;
		    Vexternal := false;
		    Default := nil;
		  end {with};
		  if not Dummylist then begin
		    Enterid(Lidp);
		  end;
		  Insymbol;
		  if Fidp = nil then begin
		    Fidp := Lidp;
		  end else begin
		    Lastidp^.Next := Lidp;
		  end;
		  Lastidp := Lidp;
		  if Lidp2 = nil then begin
		    Lidp2 := Lidp;
		  end;
		end;
		Loop2flag := not (Sy in [Commasy, Identsy]);
		if not Loop2flag then begin
		  if Sy = Commasy then begin
		    Insymbol;
		  end else begin
		    Error(158);
		  end;
		end;
	      until Loop2flag (* idname list  *);
	      if Sy = Colonsy then begin	(* type definition	     *)
		Insymbol;
#if 1	/* bug here: it does not make sure it is not a composite type */
		Typedefinition(Fsys+[Semicolonsy,Rparentsy]+Typedels, Lstrp);
		if (Lstrp <> nil) and (Lkind = Actual)
		    and (Lstrp^.Form = Files) then begin
		  Error(355);
		end;
#else
		if Sy = Identsy then begin
		  Searchid([Types], Lidp3);
		  Insymbol;
		  Lstrp := Lidp3^.Idtype;
		  if (Lstrp <> nil) and (Lkind = Actual)
		      and (Lstrp^.Form = Files) then begin
		    Error(355);
		  end;
		end else begin
		  Error(209);
		end;
#endif
	      end else begin
		Error(151);
	      end;

	      (*****************************************************************)
	      (* assign memory for each					     *)
	      (*****************************************************************)
	      while Lidp2 <> nil do begin
		with Lidp2^ do begin
		  Idtype := Lstrp;
		  if not Dummylist then begin
		    if Vkind = Formal then begin
		      Vmty := Pmt;
		      Vaddr := Assignnextmemoryloc(Vmty,Pointersize,Pointeralign);
		      Vblock := Memblock;
		    end else begin
		      if Lstrp <> nil then begin
			with Lstrp^ do begin
#if 0
			  if ((Stdtype = Mdt)
			      and ((Stsize > Wordsize) or (Stsize > Align)))
			     or (Stsize > Parthreshold) then begin
			    Vindtype := Pmt;
			    Vindaddr := Assignnextmemoryloc(Vindtype,
				Pointersize, Pointeralign);
			    Vmty := Mmt;
			    Vaddr := Assignnextmemoryloc(Vmty, Stsize, Align);
			  end else begin
#endif
			    Vmty := Pmt;
			    Vaddr := Assignnextmemoryloc(Vmty, Stsize, 
					  max(Align, Wordalign));
#if 0
			  end;
#endif
			  Vblock := Memblock;
			end {with};
		      end;
		    end;
		  end;
		  Lidp2 := Next;
		end {with};
	      end {while};
	    end;
	    Skipiferr([Rparentsy, Semicolonsy], 256, [Proceduresy, Functionsy,
		Identsy, Varsy]+Fsys);
	    Loopdone := not (Sy in [Semicolonsy, Proceduresy, Functionsy,
		Varsy, Identsy]);
	    if not Loopdone then begin
	      if Sy = Semicolonsy then begin
		Insymbol;
	      end else begin
		Warning(156);
	      end;
	    end;
	  until Loopdone; (* for each parameter of this procedure	*)
	end;
      end;
      Resolvepointers;
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
      Skipiferr(Fsys, 166, []);
    end;

  end {procedure Parameterlist};


procedure Param_to_st (
	    cid : Idp);
  { enter parameter information in symbol table 			      }
  var
    iaux : integer;
  begin
    while cid <> nil do begin
      with cid^ do begin
	case Klass of
	Vars : begin
	    if Vkind = Formal then begin
	      symndx := st_symadd(Symaddstr(Idname), Vaddr div Addrunit,
		  stParam, scVar, Typetoaux(Idtype, false, true, false, false));
	    end else if Vmty = Mmt then begin
	      symndx := st_symadd(Symaddstr(Idname), Vaddr div Addrunit,
		  stLocal, scAbs, Typetoaux(Idtype, false, true, false, false));
	    end else begin
	      symndx := st_symadd(Symaddstr(Idname), Vaddr div Addrunit,
		  stParam, scAbs, Typetoaux(Idtype, false, true, false, false));
	    end;
	  end {case Vars};
	Func : begin
	    iaux := Typetoaux(Idtype, true, true, false, false);
	    symndx := st_symadd(Symaddstr(Idname),
		(Pfaddr+Wordsize) div Addrunit, stParam, scAbs, iaux);
	    st_shifttq(iaux, tqProc);
	  end {case Func};
	Proc : begin
	    iaux := st_auxbtadd(btNil);
	    symndx := st_symadd(Symaddstr(Idname),
		(Pfaddr+Wordsize) div Addrunit, stParam, scAbs, iaux);
	    st_shifttq(iaux, tqProc);
	  end {case Proc};
	end {case};
	cid := Next;
      end {with};
    end {while};
  end {procedure Param_to_st};


(*Proceduredeclaration*)
(************************************************************************)
(*									*)
(*	PROCEDUREDECLARATION -- processes entire procedure or		*)
(*	  function declaration						*)
(*									*)
(*	Saves memory count of current procedure 			*)
(*	Insures that any previous declarations have been forward	*)
(*	If has not been declared forward				*)
(*	   Gets parameters						*)
(*	   If function, gets function result type			*)
(*	Gets declarations and body of procedure, or FORWARD		*)
(*									*)
(************************************************************************)
procedure Proceduredeclaration /* (Fsys: Setofsys; var Forwardprocedures: Idp;
					 Procflag : boolean)	*/;
  (* processes a complete procedure declaration 			     *)
  var
    Oldlev : Levrange;
    Lidp, Lidp1 : Idp;
    Forw : boolean;
    Oldtop : Disprange;
    Oldcurrname : Identname;
    Lparnumber, I, Nameend : integer;
    OldMmtMemcnt, OldPmtMemcnt : Addrrange;
    Oldmemblock : Blockrange;
    Lmemtype : Memtype;
    Lid : Identname;
    junk, iaux, newid : integer;


  begin 				(* proceduredeclaration 	     *)

    (*************************************************************************)
    (* save current memory count at re-initialize			     *)
    (*************************************************************************)
    Oldcurrname := Currname;
#if 0
    if Memblock = Progidp^.progmemblock then begin
      Globalmemcnt := Memcnt;		(* save where LoadTableAddress can   *)
					(* get at it			     *)
    end else begin
      Oldmemcnt := Memcnt;
    end;
#endif
    OldMmtMemcnt := MmtMemcnt;
    OldPmtMemcnt := PmtMemcnt;
    MmtMemcnt := 0;
    PmtMemcnt := 0;
    Oldmemblock := Memblock;
    if Sy <> Identsy then begin
      Error(209);
      if Procflag then begin
	Lidp := Uprocptr;
      end else begin
	Lidp := Ufuncptr;
      end;
    end else begin
      Currname := Id;
      (* decide whether declared forward:				     *)
      Searchsection(Display[Top].Fname, Lidp);
      if Lidp <> nil then begin 	(* it should have been declared      *)
					(* forward			     *)
	with Lidp^ do begin
	  Forw := false;
	  if Klass in [Proc, Func] then begin
	    if Pfkind = Actual then begin
	      Forw := Forwdecl and (((Klass = Proc) and Procflag)
	       or ((Klass = Func) and not Procflag));
	    end;
	    Memblock := Pfmemblock;
	  end;
	  if not Forw then begin
	    Error(557);
	  end;
	end {with};
      end else begin			(* lidp <> nil			     *)
	Forw := false;
      end;
      if not Forw then begin		(* create the procedure/function     *)
					(* descriptor block		     *)
	if Procflag then begin		(* Procedure			     *)
	  new4(Lidp, Proc, Regular, Actual);
	  Lidp^.Klass := Proc;
	end else begin			(* Function			     *)
	  new4(Lidp, Func, Regular, Actual);
	  Lidp^.Klass := Func;
	end;
	with Lidp^ do begin
	  Prockind := Regular;
	  Pfkind := Actual;
	  Idname := Id;
	  Idtype := nil;
	  Testfwdptr := nil;
	  Filelist := nil;
	  Forwdecl := false;
	  Uinst := Unop;
	  lineno := Linecnt;
	  Pflev := Level+1;
	  Externproc := (Pflev = 2) and (Progidp = nil) or (Lidp = Progidp);
	  { get a dense block number, assuming it is not external	      }
	  symndx := st_idn_index_fext(0, 0);
	  Pfmemblock := symndx;
	  Memblock := Pfmemblock;
	  Resmemtype := Zmt;
	  Resaddr := 0;
	  Nonstandard := false;
	  Referenced := false;
	  Fassigned := false;
	end {with};
	Enterid(Lidp);
      end;
      Insymbol;
    end;
    Oldlev := Level;
    Oldtop := Top;			(* open a new display frame	     *)
    if Level >= Maxnest then begin
      Error(404);
    end else begin
      Level := Level+1;
    end;
    if Top >= Displimit then begin
      Error(404);
    end else begin
      Top := Top+1;
      with Display[Top] do begin
	Fname := nil;
	Occur := Blck;
	Mblock := Lidp^.Pfmemblock;
	if Forw then begin
	  Fname := Lidp^.Next;
	end;
      end {with};
    end;

    (* allocate locations for static link *)
    if (Lidp^.Pflev <> 2) or (Lidp^.Pflev = 2) and (Progidp <> nil) then begin
					(* the static link		     *)
      static_link_loc := Assignnextmemoryloc(Mmt, Pointersize, Pointeralign);
    end;

    if Procflag then begin
      Parameterlist([Semicolonsy], Lidp1, Lparnumber, false);
    end else begin
      Parameterlist([Semicolonsy, Colonsy], Lidp1, Lparnumber, false);
    end;
    if (Lparnumber > 0) and Forw then begin
      Error(553);
    end;
    if not Forw then begin
      with Lidp^ do begin
	Next := Lidp1;
	Parnumber := Lparnumber;
      end {with};
    end;
    if not Procflag then begin
      (* allocate space for savefp, savepc and static link		     *)
      if Sy <> Colonsy then begin
	if not Forw then begin
	  Error(455);
	end;
      end else begin			(* get function type		     *)
	if Forw then begin
	  Error(552);
	end;
	Functiontype(Fsys, Lidp, false);
      end;
    end;
    if Sy = Semicolonsy then begin
      Insymbol;
    end else begin
      Warning(156);
    end;
    if (Sy = Identsy) and (Id = 'forward') then begin
      (* forward declaration *)
#if 0
      Lidp^.Savedmsize := Memcnt;
#endif
      Lidp^.SavedMmtMemcnt := MmtMemcnt;
      Lidp^.SavedPmtMemcnt := PmtMemcnt;
      if Forw then begin
	Error(257);
      end else begin
	(* add to list of forward declared procedures			     *)
	with Lidp^ do begin
	  Testfwdptr := Forwardprocedures;
	  Forwardprocedures := Lidp;
	  Forwdecl := true;
	  if Externproc then begin
	    if (Klass = Func) then begin
	      iaux := Typetoaux(Idtype, false, true, false, false)
	    end else begin
	      iaux := indexNil;
	    end;
	    newid := st_extadd(Symaddextstr(Idname), 0, stProc, scNil, iaux);
	    st_changedn(symndx, ST_EXTIFD, newid);
	  end;
	end {with};
      end;
      Insymbol;
      if Sy = Semicolonsy then begin
	Insymbol;
      end else begin
	Warning(156);
      end;
      Iferrskip(166, Fsys+[Eofsy]);
    end else if (Sy = Identsy) and (Id = 'external') then begin
      (* external declaration *)
      with Lidp^ do begin
	if Forw then begin
	  Error(257);
	end else if not Externproc then begin
	  Error(561);
	end else begin
	  Forwdecl := true;
	  { Externproc has been set to true				      }
	  if (Klass = Func) then begin
	    iaux := Typetoaux(Idtype, false, true, false, false)
	  end else begin
	    iaux := indexNil;
	  end;
	  newid := st_extadd(Symaddextstr(Idname), 0, stProc, scNil, iaux);
	  st_changedn(symndx, ST_EXTIFD, newid);
	end;
#if 0
	Lidp^.Savedmsize := Memcnt;
#endif
	Lidp^.SavedMmtMemcnt := MmtMemcnt;
	Lidp^.SavedPmtMemcnt := PmtMemcnt;
	Insymbol;
	Pflev := 2;
      end {with};
      if Sy = Semicolonsy then begin
	Insymbol;
      end else begin
	Warning(156);
      end;
      Iferrskip(166, Fsys+[Eofsy]);
    end else begin			(* not forward or external *)
      with Lidp^ do begin
	(* If was declared forward, and hence memory has already been      *)
	(* allocated for parameters, restore memory count		     *)
	if Forw then begin
#if 0
	  Memcnt := Lidp^.Savedmsize;
#endif
	  MmtMemcnt := Lidp^.SavedMmtMemcnt;
	  PmtMemcnt := Lidp^.SavedPmtMemcnt;
	end;
	Forwdecl := false;

	iaux := st_auxadd(-1);
	if Externproc then begin
	  Internsymndx := st_symadd(Symaddstr(Idname), 0, stProc, scText, iaux);
	end else begin
	  Internsymndx := st_symadd(Symaddstr(Idname), 0, stStaticProc, 
					scText, iaux);
	end;
	{ Internsymndx is later used to call st_pdadd }
	if Externproc then begin
	  if not Forw then begin
	    newid := st_extadd(Symaddextstr(Idname), 0, stProc, scText, 
		  Internsymndx);  
	    st_changedn(symndx, ST_EXTIFD, newid);
#if 0
	    newid := st_idn_index_fext(newid, 1);
	    st_setidn(symndx, newid); {fix up old dense number table entry}
#endif
	  end else begin
	    st_fixextindex(symndx, Internsymndx);
	  end;
	end else begin
	  st_changedn(symndx, st_currentifd, Internsymndx);
#if 0
	  newid := st_idn_index_fext(Internsymndx, 0);
	  st_setidn(symndx, newid); {fix up old dense number table entry}
#endif
	end;
	if debugging_symbols then begin
	  if Klass = Func then begin {for the function variable}
	    junk := st_symadd(Symaddstr(Idname), Resaddr div addrunit,
		  stLocal, scAbs, Typetoaux(Idtype, true, true, false, false))
	  end else begin
	    junk := st_auxbtadd(btNil);
	  end;
	  Param_to_st(Lidp^.next);
	end else begin
	  junk := st_auxbtadd(btNil);
	end;
	Block(Lidp, Fsys, [Beginsy, Functionsy, Proceduresy, Periodsy,
	    Semicolonsy, Eofsy]);

	(*******************************************************************)
	(* check to see if function result was assigned		     *)
	(*******************************************************************)
	if (Lidp^.Klass = Func)
	    and not Lidp^.Fassigned then begin
	  Warningwithid(310, Lidp^.Idname);
	end;
	if Sy = Semicolonsy then begin
	  Insymbol;
	  Skipiferr([Beginsy, Labelsy, Constsy, Typesy, Varsy, Proceduresy, 
		     Functionsy, Eofsy, Periodsy, Programsy], 166, Fsys);
	end else begin
	  Warning(156);
	end;
      end {with};
    end;

    (*************************************************************************)
    (* restore display and memory count 				     *)
    (*************************************************************************)
    Level := Oldlev;
    Top := Oldtop;
#if 0
    if Oldmemblock = Progidp^.progmemblock then begin
      Memcnt := Globalmemcnt;
    end else begin
      Memcnt := Oldmemcnt;
    end;
#endif
    MmtMemcnt := OldMmtMemcnt;
    PmtMemcnt := OldPmtMemcnt;
    Currname := Oldcurrname;
    Memblock := Oldmemblock;
  end {procedure Proceduredeclaration};
