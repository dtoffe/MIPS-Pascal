{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasutil.p,v 1030.7 88/02/18 14:55:07 bettina Exp $ }

#include "upasglob.h"
#include "upasutil.h"
#include "upaslex.h"
#include "allocator.h"


(*Log2,Roundup,Rounddown,Alignobject,Aligndown,Findmemorytype,Assignnextmem,Getlabel,Stringsize,Stringchars,Calcfdbsize*)
(***********************************)
(*				   *)
(* MEMORY ASSIGNMENT PRIMITIVES    *)
(*				   *)
(***********************************)
function Log2 /* ( Fval : integer) : Bitrange */;
  (* logarithm base two of fval 					     *)
  var
    E : Bitrange;
    H : integer;
  begin
    E := 0;
    H := 1;
    repeat
      E := E+1;
      H := H*2;
    until Fval <= H;
    Log2 := E;
  end {function Log2};

function Roundup /* ( I : integer; J : integer) : integer */;
  (* only works for positive numbers					     *)
  begin
    if I mod J <> 0 then I := (I div J+1)*J;
    Roundup := I;
  end {function Roundup};

function Rounddown /* ( I : integer; J : integer) : integer */;
  (* only works for negative numbers					     *)
  begin
    if I mod J <> 0 then I := (I div J-1)*J;
    Rounddown := I;
  end {function Rounddown};

#ifndef PASTEL	/* Pastel's mod is not same as ISO's mod */
#  define floormod(a,b) ((a) mod (b))
#endif

function Alignobject /* (Memctr : integer; Fsize, Align : integer) : integer */
      ;
  (* rounds up a memory counter so that an object of length Fsize will be     *)
  (* properly aligned							     *)
  begin
    (* if larger than Salign, make sure it starts at a Salign boundary; else *)
    (* if smaller than Salign, make sure it does not overlap Salign boundary *)
    Memctr := Roundup(Memctr, Align);
    if Fsize > Salign then Memctr := Roundup(Memctr, Salign)
    else if floormod(Memctr, Salign)+Fsize > Salign then begin
      Memctr := Roundup(Memctr, Salign);
    end;
    Alignobject := Memctr;
  end {function Alignobject};

#if 0
function Aligndown /* ( Memctr : integer; Fsize, Align : integer) : integer */;
  (* rounds down a memory counter so that an object of length Fsize will be  *)
  (* properly aligned							     *)
  begin
    (* if larger than Salign, make sure it starts at a Salign boundary; else *)
    (* if smaller than Salign, make sure it does not overlap Salign boundary *)
    Memctr := Rounddown(Memctr, Align);
    if Fsize > Salign then Memctr := Rounddown(Memctr, Salign)
    else if floormod(Memctr, Salign)+Fsize > Salign then begin
      Memctr := Rounddown(Memctr, Salign);
    end;
    Aligndown := Memctr;
  end {function Aligndown};
#endif


function Findmemorytype /* ( Dty : Datatype; Fsize : Sizerange; Isparam, */
					/* Istemp : boolean) : Memtype	*/;
  (* given a data object, which is either a parameter, a local variable, or  *)
  (* a temporary, figures out the appropriate memory area to put the object  *)
  (* in 								     *)

  begin
    if Isparam then begin
      if Dty = Mdt then Error(171);	(* compiler error		     *)
      Findmemorytype := Pmt;
    end else begin
      Findmemorytype := Mmt;
    end;
  end {function Findmemorytype};

function Assignnextmemoryloc /* (Mty : Memtype; Fsize : Sizerange; Align : cardinal) : integer */;

  (***************************************************************************)
  (* assigns the next available location within a memory area, after making  *)
  (* sure alignment is correct. Updates memory counter			     *)
  (***************************************************************************)

  begin
    case Mty of
    Mmt: begin
      MmtMemcnt := MmtMemcnt - Fsize;
      MmtMemcnt := Rounddown(MmtMemcnt, max(Align, Salign));
      { put byte and halfword variables in least significant end of
	a full word }
      Assignnextmemoryloc := MmtMemcnt;
      if not lsb_first and (Fsize < Salign) then begin
	Assignnextmemoryloc := MmtMemcnt + (Salign - Fsize);
      end;
      end;
    Pmt: begin
      if lsb_first then begin
        if align <> 0 then begin
	  PmtMemcnt := Alignobject(PmtMemcnt, Fsize, Align);
	end;
	Assignnextmemoryloc := PmtMemcnt;
	PmtMemcnt := PmtMemcnt+Fsize;
      end else begin
        if align <> 0 then begin
	  PmtMemcnt := Alignobject(PmtMemcnt, Fsize, Align);
	end;
	if Fsize < Wordsize then begin
	  PmtMemcnt := PmtMemcnt+Wordsize;
	  Assignnextmemoryloc := PmtMemcnt-Fsize;
	end else begin
	  Assignnextmemoryloc := PmtMemcnt;
	  PmtMemcnt := PmtMemcnt+Fsize;
	end;
      end;
      end;
    Smt: begin
      if align <> 0 then begin
        SmtMemcnt := Alignobject(SmtMemcnt, Fsize, Align);
      end;
      Assignnextmemoryloc := SmtMemcnt;
      SmtMemcnt := SmtMemcnt+Fsize;
      end;
    end {case};
  end {function Assignnextmemoryloc};

function Getlabel /* : integer	*/;
  begin
    Lastuclabel := Lastuclabel+1;
    Getlabel := Lastuclabel;
  end {function Getlabel};

function Stringsize /* ( Charcount : integer) : integer */;
  (* given the size of a string in chars, returns the size in bits	     *)
  begin
    Stringsize := Roundup((Charcount div CharsperSalign)*Salign+(Charcount mod
	CharsperSalign)*Pcharsize, Addrunit);
  end {function Stringsize};

function Stringchars /* ( Strsize : integer) : integer	*/;
  (* given the size of a string in bits, returns the size in chars	     *)

  begin
    Stringchars := Strsize div Salign*CharsperSalign+Strsize mod Salign div
	Pcharsize;
  end {function Stringchars};


function Intlen /* ( I : integer) : integer */;
  (* Returns printed length of integer. 				     *)
  var
    J : integer;
  begin
    if (I >= 0) and (I <= 9) then Intlen := 1
    else begin
      if I < 0 then begin
	J := 1;
	I := -I;
      end else J := 0;
      while I > 0 do begin
	J := J+1;
	I := I div 10;
      end {while};
      Intlen := J;
    end;
  end {function Intlen};

function Idln /* ( Id : Identname) : integer */;
  (* returns the length of the identifier, not counting trailing spaces      *)
  label
    99;

  var
    I : integer;

  begin
    for I := Identlength downto 1 do begin
      if Id[I] <> ' ' then goto 99;
    end {for};
99 :
    Idln := I;
  end {function Idln};


function Fnln (* ( Fn : Filename) : integer *);
  (* returns the length of the identifier, not counting trailing spaces      *)
  var i : integer;
  begin
    i := 0;
    repeat
      if Fn[i+1] = ' ' then return i;
      i := i + 1; 
    until i = Filenamelen;
    return Filenamelen;
  end {function Fnln};

(*Makeexternalname,Enterid,Searchsection,Searchid,Newstruct*)
(************************************************************************)
(************************************************************************)
(*									*)
(*	SYMBOL TABLE MODULE						*)
(*									*)
(*	The symbol table consists of an stack of "sections", each	*)
(*	of which is a binary tree.  There is one section for each	*)
(*	lexical level.	Thus, when a new procedure is entered,		*)
(*	a new section is pushed onto the stack, and when it is exited,	*)
(*	its section is popped.	When searching the symbol table, by	*)
(*	starting at the topmost section, proper scoping is preserved.	*)
(*									*)
(*	The fields of a record also constitute a section when a WITH	*)
(*	statement is encountered.   The global variable TOP points to	*)
(*	the top of the stack, which may be either a procedure section	*)
(*	(a tree of its local symbols) or a record section (a tree of	*)
(*	its fields).  The variable LEVEL always points to the topmost	*)
(*	procedure section.						*)
(*									*)
(*	Procedures:							*)
(*									*)
(*	   Enterid -- enter an Id into the table			*)
(*	   Searchsection -- search a single section for a given Id	*)
(*	   Searchid -- search the whole stack for a given Id.  Also	*)
(*	      check that the Id is of the correct type by comparing	*)
(*	      it with the type passed.					*)
(*									*)
(************************************************************************)
#if 0
procedure Makeexternalname /* ( var Fid : Identname) */;

  (***************************************************************************)
  (* Conjures up a unique name for an external variable or procedure. Name   *)
  (* must be in a form suitable for use by the system loader. This version   *)
  (* creates names of the form: MMM$NN where MMM are leading letters from    *)
  (* the current module name, and NN is a counter of names generated for     *)
  (* this module so far. The number of significant characters in MMM is      *)
  (* dtermined by the MODCHARS constant. Since all alphanumeric letters are  *)
  (* used for NN, this system generates up to 1295 unique names per module   *)
  (***************************************************************************)

  var
    I : integer;

  begin
    Fid := Progidp^.Idname;		(* whole module name		     *)
    (* if id name is less than Modchars long, fill in holes with '$'         *)
#if 0
    for I := 2 to Modchars do begin
      if Fid[I] = Underbar then Fid[I] := '$';
    end {for};
#endif
    if Modchars <= Idln(Fid) then I := Modchars
    else I := Idln(Fid);
    Fid[I+1] := '$';
    (* turn Extnamcounter into a character string as part of the external    *)
    (* name								     *)
    if Extnamcounter >= 1296 then Error(473) (* too many exported id's       *)
    else if Extnamcounter >= 360 then begin
      Fid[I+2] := chr(ord('A')+Extnamcounter div 36-10);
    end else Fid[I+2] := chr(ord('0')+Extnamcounter div 36);
    if Extnamcounter mod 36 >= 10 then begin
      Fid[I+3] := chr(ord('A')+Extnamcounter mod 36-10);
    end else Fid[I+3] := chr(ord('0')+Extnamcounter mod 36);
    for I := Labchars+1 to Identlength do Fid[I] := ' ';
    Extnamcounter := Extnamcounter+1;	(* so we don't reuse the same name   *)
  end {procedure Makeexternalname};	(* makeexternalname		     *)
#endif


procedure Enterid /* ( Fidp : Idp) */;
  (* Enter Id pointed to by Fidp into the symbol table, checking for	     *)
  (* duplications							     *)

  var
    Newname : Identname;
    Lidp, Lidp1 : Idp;
    Lleft : boolean;
  begin 				(* enterid			     *)
    Lidp := Display[Top].Fname;
    if Lidp = nil then Display[Top].Fname := Fidp
    else begin
      Newname := Fidp^.Idname;
      repeat
	Lidp1 := Lidp;
	if Lidp^.Idname <= Newname then begin
	  if Lidp^.Idname = Newname then begin (* idname conflict	     *)
	    if (Newname[1] >= '0') and (Newname[1] <= '9') then Error(266)
					(* multi-declared label 	     *)
	    else Error(302);		(* multi-declared identifier	     *)
	  end;
	  Lidp := Lidp^.Rlink;
	  Lleft := false;
	end else begin
	  Lidp := Lidp^.Llink;
	  Lleft := true;
	end;
      until Lidp = nil;
      if Lleft then Lidp1^.Llink := Fidp
      else Lidp1^.Rlink := Fidp;
    end;
    with Fidp^ do begin
      Llink := nil;
      Rlink := nil;
    end {with};
  end {procedure Enterid};


procedure Searchsection /* ( Fidp : Idp; var Fidp1 : Idp)  */;

  (***************************************************************************)
  (* Searches binary tree whose head is FIDP; This procedure is used	     *)
  (* directly by Proceduredeclaration to find forward declared procedure     *)
  (* id's and by Variable to find record fields                              *)
  (***************************************************************************)

  begin 				(* searchsection		     *)
    Fidp1 := nil;
    while Fidp <> nil do begin
      with Fidp^ do begin
	if Idname = Id then begin
	  Fidp1 := Fidp;
	  Fidp := nil;
	end else if Idname < Id then Fidp := Rlink
	else Fidp := Llink;
      end {with};
    end {while};
  end {procedure Searchsection};

procedure Searchid /* ( Fidcls : Setofids; var Fidp : Idp) */;

  (***************************************************************************)
  (* Finds an identifier in the symbol table. An error results if the class  *)
  (* of the id is not in the set FIDCLS. This error is not reported if the   *)
  (* caller has turned off the global switch SEARCHERROR. This is done when  *)
  (* checking forward referenced pointer types. 			     *)
  (***************************************************************************)

  label
    444;

  var
    i : integer;
    Lidp : Idp;

  begin 				(* searchid			     *)
    for i := Top downto 0 do begin	(* search each lexical level in turn *)
      Lidp := Display[i].Fname;
      while Lidp <> nil do begin
	with Lidp^ do begin
	  if Idname = Id then begin
	    Disx := i;
	    if Klass in Fidcls then goto 444
	    else begin
	      if Searcherror then Error(401);
	      Lidp := Rlink;
	    end;
	  end else if Idname < Id then Lidp := Rlink
	  else Lidp := Llink;
	end {with};
      end {while};
    end {for};

    (*************************************************************************)
    (* search not succsessful						     *)
    (*************************************************************************)

    if Searcherror then begin
      if (Id[1] >= '0') and (Id[1] <= '9') then Error(215) (* undeclared     *)
					(* label			     *)
      else Error(253) (* undeclared identifier	*);

      (***********************************************************************)
      (* to avoid returning nil, reference an entry for an undeclared id of  *)
      (* appropriate class						     *)
      (***********************************************************************)

      new1(Lidp);
      if Types in Fidcls then Lidp^ := Utypptr^
      else if Vars in Fidcls then Lidp^ := Uvarptr^
      else if Field in Fidcls then Lidp^ := Ufldptr^
      else if Konst in Fidcls then Lidp^ := Ucstptr^
      else if Proc in Fidcls then Lidp^ := Uprocptr^
      else Lidp^ := Ufuncptr^;
      Lidp^.Idname := Id;
      (* enter in symbol table, in order to lessen subsequent error	     *)
      (* messages, but NOT in field list, since new record will go away at   *)
      (* end of block							     *)
      if Display[Top].Occur = Blck then Enterid(Lidp);
    end;
444 :
    Fidp := Lidp;
  end {procedure Searchid};

procedure assertion_error;
  begin
    writeln(err, 'Assertion failed');
    flush(err);
  end {procedure assertion_error};

procedure Filenameassign/*(var f: filename; str: identname)*/;
  {Since filename is real long, this routine assigns a short string to
   a filename and blank-fill the remaining part of it; str must have at least
   one blank at its end}
  var i: integer;
  begin
  i := 1;
  while str[i] <> ' ' do begin
    f[i] := str[i];
    i := i + 1;
    end {while};
  for i := i to Filenamelen do
    f[i] := ' ';
  end {Filenameassign};
