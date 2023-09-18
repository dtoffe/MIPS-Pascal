{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upascall.p,v 1030.7 88/02/18 14:55:19 bettina Exp $ }

#include "upasglob.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upasbutil.h"
#include "upasexpr.h"
#include "upastree.h"
#include "upascall.h"
#include "upasfold.h"
#include "allocator.h"


(*Formalcheck,Savregs,Restregs*)
procedure Formalcheck (
	var Fattr : Attr );
  begin
    with Fattr do begin
      (* check for passing elements of packed structures by ref 	     *)
#if 0	/* Too restrictive */
      if Apacked and (Atypep^.Form <> Files) then begin
	Error(357);
      end;
#else
      if (Atypep <> nil) and (Dplmt mod Atypep^.Align <> 0) then begin
	Error(357);
      end;
#endif
    end {with};
  end {procedure Formalcheck};

(*Callspecial,Getfilename,Getvariable,Savefile,Loadtableaddress*)
procedure Getvariable (
	    Fsys : Setofsys);

  (***************************************************************************)
  (* parses a variable, for use as a reference parameter in a standard	     *)
  (* procedure or function						     *)
  (***************************************************************************)

  var
    Lidp : Idp;
    dummy : Indirtype;
  begin
    if Sy = Identsy then begin
      Searchid([Vars, Field], Lidp);
      Insymbol;
    end else begin
      Error(209);
      Lidp := Uvarptr;
    end;
    Parseleft := true;
    Selector(Fsys, Lidp, dummy);
    Parseleft := false;
  end {procedure Getvariable};

(************************************************************************)
(************************************************************************)
(*									*)
(*	SPECIAL-PROCEDURE-CALL MODULE					*)
(*									*)
(*	Contains a main procedure, Callspecial, and several		*)
(*	subprocedures, each of which processes calls to a small 	*)
(*	number of similar standard procedures and functions.		*)
(*									*)
(************************************************************************)
(************************************************************************)

procedure Callspecial /* ( Fsys : Setofsys; Fidp : Idp)  */;
  var
    Lstamp : integer;
(************************************************************************)
(*									*)
(*	GETFILENAME -- reads the first parameter for READ and WRITE.	*)
(*	  This may or may not be a file.				*)
(*									*)
(*     if no parameters then						*)
(*	  the default file (INPUT or OUTPUT) is returned in IOFILEATTR; *)
(*	  example: WRITELN;						*)
(*     else								*)
(*	  parses first parameter					*)
(*	  if it is a file, it is returned in IOFILEATTR 		*)
(*	     example: WRITELN(OUTPUT,I);				*)
(*	  else it is returned in GATTR and the default file in		*)
(*	     IOFILEATTR and FIRSTREAD is set to TRUE			*)
(*	     example: WRITELN(I)					*)
(*									*)
(*     if READEXPR then Expression will be used to parse the parameter	*)
(*     else GetVariable will be used and the file's Idp will be         *)
(*	  returned in Iofileidp 					*)
(*									*)
(************************************************************************)

  procedure Getfilename (
	      Defaultfilep : Idp;
	      Followsys : Setofsys;
	      Readexpr : boolean;	{true if write, false if read}
	  var Iofileattr : Attr;
	  var Iofileidp : Idp;
	  var Iofiletypep,
	      Iofilep : Strp;
	  var Firstread,
	      Istextfile,
	      Norightparen : boolean);


    var
      dummy : Indirtype;
    begin				(* getfilename			     *)

      Norightparen := true;
      Firstread := false;
      Iofileidp := Uvarptr;

      if Sy = Lparentsy then begin
	Norightparen := false;
	Insymbol;
	if Readexpr then begin
	  Expression(Followsys);
	end else if Sy = Identsy then begin
	  Searchid([Vars, Func, Field], Iofileidp);
	  Insymbol;
	  Parseleft := not Readexpr;    {to control setting of assignedto; will
				 wrongly cause file variable as being assigned}
	  Selector(Followsys, Iofileidp, dummy);
	  Parseleft := false;
	end else begin
	  Error(209);
	end;
	if Gattr.Atypep = nil then begin
	  Firstread := true;
	end else begin
	  Firstread := (Gattr.Atypep^.Form <> Files);
	end;
	if not Firstread then begin	(* file 			     *)
	  Iofileattr := Gattr;
	  Iofilep := Gattr.Atypep;
	  Iofiletypep := Iofilep^.Filetype;
	  Istextfile := Gattr.Atypep^.Textfile;
	  Iofileidp^.Referenced := true;
	  with Iofileattr do begin
	    Dplmt := Dplmt + File_stdio_offset;
	    Atypep := Addressptr;
	    Adtype := Adt;
	    Asize := Pointersize;
	  end {with};
	end;
      end {there is left paren};

      if Firstread or Norightparen then begin
	(* make up an ATTR describing the default file			     *)
	Iofileidp := Defaultfilep;
	if Iofileidp^.Vexternal then
	  st_fixextsc(Iofileidp^.Vblock, scUndefined);
	Iofilep := Defaultfilep^.Idtype;
	Iofiletypep := Defaultfilep^.Idtype^.Filetype;
	Istextfile := Defaultfilep^.Idtype^.Textfile;
	with Iofileattr do begin
	  Kind := Varbl;
	  Apacked := false;
	  Indexed := false;
	  Indirect := Notind;
	  Indexmt := Zmt;
	  Indexr := 0;
	  Subkind := nil;
	  Aclass := Vars;
	  Amty := Defaultfilep^.Vmty;
	  Ablock := Defaultfilep^.Vblock;
	  Baseaddress := Defaultfilep^.Vaddr;
	  Dplmt := Defaultfilep^.Vaddr + File_stdio_offset;
	  Atypep := Addressptr;
	  Adtype := Adt;
	  Asize := Pointersize;
	end {with};
      end;
    end {procedure Getfilename};


  procedure Savefile (
	  var Fattr : Attr);

    (*************************************************************************)
    (* if FATTR is indexed, saves it in a temporary so it can be used again; *)
    (* updates FATTR to describe the temporary				     *)
    (*************************************************************************)

    var
      Lattr : Attr;
    begin
#if 0
      if (Fattr.Indirect in [Aind, Hind]) and Fattr.Indexed then begin
	Loadaddress(Fattr);
      end;
      if Fattr.Indexed then begin
	Load(Fattr);
	Getatemp(Lattr, Heapptr, Lstamp, false);
	Store(Lattr);
	Fattr := Lattr;
	with Fattr do begin
	  Indirect := Hind;
	  Indexmt := Amty;
	  Indexr := Dplmt;
	  Dplmt := 0;
	  Indexed := false;
	end {with};
      end;
#else
      if Fattr.Indexed or (Fattr.Indirect <> Notind) then begin
	Load(Fattr);
	Getatemp(Lattr, Heapptr, Lstamp, false);
	Store(Lattr);
	Fattr := Lattr;
      end;
#endif
    end {procedure Savefile};


  procedure LoadTableaddress (
	      Scalarstrp : Strp);
    (* Loads the address of the scalar name table for an ennumerated type,   *)
    (* Generates table if has not been generated before.		     *)

    var
      Lidp : Idp;
      Loffset : Addrrange;
      Lvalu : Valu;
      Lsize : Sizerange;
      I, J : 1..Identlength;
    begin
      if Scalarstrp <> nil then begin
	with Scalarstrp^ do begin
	  if Saddress = -1 then begin	(* table has not yet been allocated  *)
	    new1(Lvalu.Chars);
	    Lidp := Fconst;		(* find first string		     *)
	    /*
	    Lsize := Stringsize(Identlength);
	    */
	    while Lidp <> nil do begin
	      (* allocate global memory for string			     *)
	      (* if first string in table, save its address		     *)
	      if Saddress = -1 then begin
		Saddress := Assignnextmemoryloc(Smt, 0, Addrunit);
	      end;
	      (* copy it into a Valu record				     *)
	      for I := 1 to Identlength do begin
		Lvalu.Chars^.ss[I] := Lidp^.Idname[I];
	      end {for};
	      Lvalu.Chars^.ss[Identlength] := ' ';
	      J := Identlength;
	      while Lvalu.Chars^.ss[J-1] = ' ' do J := J-1;
	      Lvalu.Chars^.ss[J] := chr(0);
	      if Lidp^.Next = nil then begin
		J := J + 1;
		Lvalu.Chars^.ss[J] := chr(0);
		end;
	      J := bitand(J+3, -4);
	      Lvalu.Ival := J;
	      (* and emit the INIT instruction				     *)
	      Lsize := Stringsize(J);
	      Loffset := Assignnextmemoryloc(Smt, Lsize, Addrunit);
	      Ucoinit(Mdt, Display[0].Mblock, Loffset, Loffset, Lsize, Lvalu);
	      Lidp := Lidp^.Next;
	    end {while};
#if 0
	    dispose(Lvalu.Chars);
#endif
	  end;
	  Ucolda(Smt, Display[0].Mblock, Saddress, Pointersize, Saddress);
	end {with};
      end;
    end {procedure LoadTableaddress};

(*Readreadln*)
(************************************************************************)
(*									*)
(*	READREADLN -- parses call to READ or READLN			*)
(*									*)
(*	If the file is not a text file, then for each variable, the	*)
(*	   current copy of the file buffer is put into the variable,	*)
(*	   and a GET is done to get the next element of the file.	*)
(*	   If the variable is of type subrange, a check is emitted to	*)
(*	   ensure the file buffer is within that range. 		*)
(*	For text files, a call to one of many runtime routines is	*)
(*	   done, passing the address of the variable to be stored	*)
(*	   into.  For simple types this straightforward.  For		*)
(*	   enumerated types, the address of a vector containing the	*)
(*	   string representations of each member must be passed.	*)
(*	   This vector is generated at the end of the program.		*)
(*	   This address must also be passed for sets of enumerated	*)
(*	   types.							*)
(*									*)
(*	Here are two sample runtime procedure headers:			*)
(*									*)
(*	Procedure $RDC (VAR Ch: Char; VAR Fdb: Textfile);		*)
(*	Procedure $RDSET (VAR Setvariable: Targetset;			*)
(*			  VAR Fdb: Textfile;				*)
(*			  Minvalue, Maxvalue: Integer;			*)
(*			  Scalarnames: Scalarvptr;			*)
(*			  Elementform: Scalarform);			*)
(*									*)
(*									*)
(************************************************************************)
  procedure Readreadln;
    type
      Scalarform = (Integerform, Charform, Declaredform); (* for sets	     *)
    var
      Iofileidp : Idp;
      Iofiletypep, Iofilep : Strp;
      Firstread, Istextfile, Norightparen : boolean;
      Iofileattr : Attr;
      Fileattr, Bufferattr : Attr;
      Baseform : Structform;
      Testflag, More : boolean;
      Parcount : integer;
      read_function : boolean;

    begin				(* readreadln			     *)
      Lstamp := 0;
      (* get file and maybe first variable				     *)
      Getfilename(Inputptr, [Arrowsy, Rparentsy, Commasy], false, Iofileattr,
	  Iofileidp, Iofiletypep, Iofilep, Firstread, Istextfile, Norightparen);

      if not Firstread then begin
	if Sy = Commasy then begin
	  Insymbol;
	end;
      end;
      (* save addr of file block in temporary, if necessary		     *)
      Savefile(Iofileattr);
      Stdcallinit(Parcount);
      More := false;
      if (Fidp^.Key = Spread) or (Sy = Identsy) or Firstread then begin
	repeat
	  Fileattr := Iofileattr;	(* get unloaded version of FILEATTR  *)
	  if not Istextfile then begin
	    (* store the record just read into the variable and then do a    *)
	    (* GET to get the next record from the file 		     *)
	    if not Firstread then begin
	      Getvariable(Fsys+[Commasy]);
	    end;

	    (* make sure variable type corresponds to file type 	     *)
	    if not Comptypes(Gattr.Atypep, Iofiletypep) then begin
	      Errandskip(366, Statbegsys+[Rparentsy, Semicolonsy]);
	    end;
	    if (Gattr.Atypep <> nil) then begin
	      (* load address of array or record *)
	      if (Gattr.Atypep^.Stdtype = Mdt) then begin
	        Loadaddress(Gattr);
	      end;

	      if Iofiletypep <> nil then begin
		Bufferattr := Iofileattr;
		Load(Bufferattr);
		with Bufferattr do begin
		  Atypep := Addressptr;
		  Adtype := Adt;
		  Asize := Pointersize;
		  Indexed := true;
		  Dplmt := 1*Wordsize;		(* see stdio.h *)
		  Kind := Varbl;
		  Aclass := Vars;
		  Apacked := false;
		end {with};
		Load(Bufferattr);
		with Bufferattr do begin
		  Apacked := Iofilep^.Filepf;
		  Asize := Iofilep^.Componentsize;
		  Atypep := Iofiletypep;
		  Adtype := Atypep^.Stdtype;
		  Indexed := true;
		  Dplmt := 0;
		  Kind := Varbl;
		  Aclass := Vars;
		end {with};
		Load(Bufferattr);
		Matchtoassign(Bufferattr, Gattr.Atypep);
		with Gattr.Atypep^ do begin
		  (* check the subrange of the just read item		     *)
		  if Runtimecheck and (Form = Subrange) then begin
		    if Iofiletypep^.Form <> Subrange then begin
		      Testflag := true;
		    end else begin
		      Testflag := (Iofiletypep^.Vmin < Vmin)
		       or (Iofiletypep^.Vmax > Vmax);
		    end;
		    if Testflag then begin
		      Uco2typint(Uchkl, Gattr.Adtype, Vmin);
		      Uco2typint(Uchkh, Gattr.Adtype, Vmax);
		    end;
		  end;
		end {with};
		(* store previous record in variable			     *)
		Store(Gattr);
		(* get the next record from the file			     *)
		Load(Fileattr);
		Par(Adt, Parcount);
		Uco3intval(Uldc, Jdt, Intsize,
			   Iofilep^.Componentsize div Fpackunit);
		Par(Jdt, Parcount);
		Uco1idp(Ucup, Getptr);
	        st_fixextsc(Getptr^.symndx, scUndefined);
	      end;
	    end;
	  end else begin		(* textfile			     *)
	    (* load address of file block				     *)
	    read_function := true;
	    Load(Fileattr);
	    Par(Adt, Parcount);
	    (* load address of variable 				     *)
	    if not Firstread then begin
	      Getvariable(Fsys+[Commasy]);
	      if (Gattr.Kind = Varbl) and Gattr.Indexed then begin
		Swapstak;	{ swap MST and indexing code }
	      end;
	    end;
	    with Gattr do begin 	(* load any other parameters and     *)
					(* emit call			     *)
	      if Atypep <> nil then begin
		if Strng(Atypep) then begin (* strings			     *)
		  if (Gattr.Kind = Varbl) and Gattr.Indexed then begin
		    Swapstak;	{ swap MST and indexing code }
		  end;
		  Loadaddress(Gattr);
		  Par(Adt, Parcount);
		  read_function := false;
		  with Atypep^.Inxtype^ do begin
		    (* load length of string				     *)
		    Uco3intval(Uldc, Jdt, Intsize, Vmax-Vmin+1);
		    Par(Jdt, Parcount);
		  end {with};
		  Support(Readstring);
		end else if Atypep^.Form in [Scalar, Subrange, Power] then
		  begin
		  Baseform := Atypep^.Form;
		  if Baseform = Power then begin (* sets		     *)
		    if Standrdonly then begin
		      Warning(212);
		    end;
		    if (Gattr.Kind = Varbl) and Gattr.Indexed then begin
		      Swapstak;	{ swap MST and indexing code }
		    end;
		    Loadaddress(Gattr);
		    Par(Adt, Parcount);
		    read_function := false;
		    Uco3intval(Uldc, Jdt, Intsize, Atypep^.Softmin);
		    Par(Jdt, Parcount);
		    Uco3intval(Uldc, Jdt, Intsize, Atypep^.Softmax);
		    Par(Jdt, Parcount);
		    Atypep := Atypep^.Basetype;
		  end;
		  (* ATYPEP^.FORM is now either a SCALAR or SUBRANGE	     *)
		  if (Atypep <> nil) then begin
		    if Atypep^.Form = Subrange then begin (* subranges	     *)
	        /*    if (Atypep = Charptr) and (Baseform = Subrange) then
			begin
			(* type CHAR has its subrange checked explicitly by  *)
			(* $GETC					     *)
			Baseform := Scalar;
		      end else */ if Baseform <> Power then begin
			with Atypep^ do begin
			  Uco3intval(Uldc, Jdt, Intsize, Vmin);
			  Par(Jdt, Parcount);
			  Uco3intval(Uldc, Jdt, Intsize, Vmax);
			  Par(Jdt, Parcount);
			end {with};
		      end;
		      Atypep := Atypep^.Hosttype;

		      (*******************************************************)
		      (* enumerated types				     *)
		      (*******************************************************)
		    end else if (Atypep^.Scalkind = Declared)
		     and (Atypep <> Boolptr) and (Baseform <> Power) then
		      begin
		      Uco3intval(Uldc, Ldt, Intsize, 0);
		      Par(Ldt, Parcount);
		      Uco3intval(Uldc, Ldt, Intsize, Atypep^.Dimension);
		      Par(Ldt, Parcount);
		    end;
		  end;
		  (* at this point, ATYPEP^.FORM must be SCALAR. If we are   *)
		  (* reading a set or subrange, this will be its base type   *)
		  if Atypep <> nil then begin
		    with Atypep^ do begin
		      if (Scalkind = Declared) and (Atypep <> Boolptr) then
			begin
			(* address of the names of a scalar		     *)
			if Standrdonly then begin
			  Warning(212);
			end;
			LoadTableaddress(Atypep);
			Par(Adt, Parcount);
			if Baseform = Power then begin
			  Uco3intval(Uldc, Ldt, Intsize, ord(Declaredform));
			  Par(Ldt, Parcount);
			  Support(Readset);
			end else begin
			  /*
			  Uco3intval(Uldc, Ldt, Intsize, 10);
			  Par(Ldt, Parcount);
			  Support(Readsupport[Ldt, Baseform]);
			  */
			  Support(Readenum);
			end;
		      end else begin	(* scalkind = standard		     *)
			if Baseform = Power then begin
			  Uco3intval(Uldc, Adt, Pointersize, -1);
			  Par(Adt, Parcount);
			  if Comptypes(Atypep, Charptr) then begin
			    Uco3intval(Uldc, Ldt, Intsize, ord(Charform));
			  end else if (Atypep = Intptr)
			   or (Atypep = Cardinalptr) then begin
			    Uco3intval(Uldc, Ldt, Intsize, ord(Integerform));
			  end else begin
			    Error(458);
			  end;
			  Par(Ldt, Parcount);
			  Support(Readset);
			end else begin
			  if Atypep = Boolptr then begin
			    Support(Readboolean);
			  end else if Atypep = Charptr then begin
			    if Baseform = Subrange then
			      Support(Readcharrange)
			    else Support(Readchar);
			  end else begin
			    Uco3intval(Uldc, Ldt, Intsize, 10);
			    Par(Ldt, Parcount);
			    Support(Readsupport[Stdtype, Baseform]);
			  end;
			end;
		      end;
		    end {with};
		  end;
		  if read_function then begin
		    Store(Gattr);
		    do_expr := false;
		  end;
		end else begin		(* arrays, records, files, pointers  *)
		  Error(169);
		end;
	      end;
	    end {with};
	  end;
	  More := (Sy = Commasy);
	  if More then begin
	    if do_expr then begin
	      Exprprepass(stak^.tree);
	      (* no need call Genexpr because it is not a function	     *)
	      Popstak;
	    end;
	    do_expr := true;
	    Firstread := false;
	    Stdcallinit(Parcount);
	    Insymbol;
	  end else if Fidp^.Key = Spreadln then begin
	    if do_expr then begin
	      Exprprepass(stak^.tree);
	      (* no need call Genexpr because it is not a function	     *)
	      Popstak;
	    end;
	    do_expr := true;
	    Stdcallinit(Parcount);
	  end;
	until not More;
      end;
      if Fidp^.Key = Spreadln then begin
	if not Istextfile then begin
	  Error(366);
	end;
	Fileattr := Iofileattr;
	Load(Fileattr);
	Par(Adt, Parcount);
	Support(Readline);
      end;

      if not Norightparen then begin
	if Sy = Rparentsy then begin
	  Insymbol;
	end else if not Norightparen then begin
	  Warning(152);
	end;
      end;
      if Lstamp > 0 then begin
	Freetemps(Lstamp);
      end;
    end {procedure Readreadln};

(*Writewriteln*)
(************************************************************************)
(*									*)
(*	WRITEWRITELN -- parses a call to WRITE or WRITELN		*)
(*									*)
(*	For non-text files, puts the value parsed in the file buffer	*)
(*	   and does a PUT						*)
(*	For text files, gets each expression and field widths (if any)	*)
(*	   and emits call to the proper runtime routine.		*)
(*									*)
(************************************************************************)
  procedure Writewriteln;
    type
      Scalarform = (Integerform, Charform, Declaredform); (* for sets	     *)
    var
      Iofileidp : Idp;
      Iofiletypep, Iofilep : Strp;
      Firstread, Istextfile, Norightparen : boolean;
      Iofileattr : Attr;
      Fileattr, Bufferattr, Iobufferattr, Lattr : Attr;
      Defaultwidth : integer;
      Base : integer;
      Llstrp, Lstrp : Strp;
      Lsize, Lmin, Lmax : integer;
      Scalartype : Scalarform;
      More : boolean;
      Parcount : integer;
      Lsupport : Supports;
      Firstexpr : pttreerec;

    begin				(* writewriteln 		     *)
      Lstamp := 0;
      Stdcallinit(Parcount);

      (***********************************************************************)
      (* get file and maybe first expression				     *)
      (***********************************************************************)
      Getfilename(Outputptr, [Arrowsy, Rparentsy, Commasy, Colonsy], true,
	  Iofileattr, Iofileidp, Iofiletypep, Iofilep, Firstread, Istextfile,
	  Norightparen);
      Firstexpr := nil;
      if not Firstread then begin
	if Sy = Commasy then begin
	  Insymbol;
	end;
      end else begin
	if (Gattr.Kind = Expr)
	    or ((Gattr.Kind = Varbl) and Gattr.Indexed) then begin
	  Firstexpr := stak^.tree; Popstak;
	end;
      end;

      (***********************************************************************)
      (* save addr of file block in temporary, if necessary		     *)
      (***********************************************************************)
      Savefile(Iofileattr);

#if 0
      if not Istextfile then begin
	(* create ATTR to describe the file buffer, for later use	     *)
	Iobufferattr := Iofileattr;
	with Iobufferattr do begin
	  Dplmt := Iofileattr.Dplmt+Fdbsize;
	  Asize := Iofilep^.Componentsize;
	  Atypep := Iofiletypep;
	  Adtype := Iofiletypep^.Stdtype;
	  Apacked := Iofilep^.Filepf;
	end {with};
      end;
#endif

      (***********************************************************************)
      (* if there is an expression to write out, (there MUST be one for      *)
      (* WRITE, MAY be one for WRITELN) then generate the appriopriate calls *)
      (* to runtimes for each expression				     *)
      (***********************************************************************)

      More := false;
      if (Fidp^.Key = Spwrite) or (Sy in Facbegsys+Addopsys) or Firstread then
	begin
	repeat				(* for each parameter of write	     *)

	  Fileattr := Iofileattr;	(* get unloaded version of FILEATTR  *)
	  (*****************************************************************)
	  (* load address of file block				     *)
	  (*****************************************************************)
	  Load(Fileattr);
	  Par(Adt, Parcount);

	  if not Firstread then begin
	    Expression(Fsys+[Commasy, Colonsy]);
	  end else if Firstexpr <> nil then begin
	    Pushstak(Firstexpr);
	    Firstexpr := nil;
	  end;
	  Lstrp := Gattr.Atypep;
	  if Lstrp <> nil then begin
	    (* load expression on the stack, if not already there if string  *)
	    (* or set, must be passed indirectly			     *)
	    if Strng(Lstrp) then begin
	      Loadaddress(Gattr);
	      if Istextfile then begin
		Par(Adt, Parcount);
	      end;
	    end else if Lstrp^.Form = Power then begin
	      if (Gattr.Kind <> Varbl) or Gattr.Apacked then begin
		Load(Gattr);
		Getatemp(Lattr, Gattr.Atypep, Lstamp, false);
		Store(Lattr);
		Gattr := Lattr;
	      end;
	      Loadaddress(Gattr);
	      if Istextfile then begin
		Par(Adt, Parcount);
	      end;
	    end else begin
	      Load(Gattr);
	      if Istextfile then begin
		Par(Gattr.Adtype, Parcount);
	      end;
	    end;
	  end;
	  if not Istextfile then begin
	    if Lstrp <> nil then begin
	      if not Comptypes(Lstrp, Iofilep^.Filetype) then begin
		Errandskip(366, Statbegsys+[Rparentsy, Semicolonsy]);
	      end;
	      (* store variable in the file buffer			     *)
#if 0
	      Bufferattr := Iobufferattr;
(* These 4 lines are replaced by next two lines --Per Bothner April 6, 1984
	      Loadaddress(Bufferattr);
	      Uco2typtyp(Uswp,Adt,Gattr.Adtype);
	      Matchtoassign(Gattr,Bufferattr.Atypep);
	      Uco1attr(Uistr,Bufferattr);
*)
#else
	      Bufferattr := Iofileattr;
	      Load(Bufferattr);
	      with Bufferattr do begin
		Atypep := Addressptr;
		Adtype := Adt;
		Asize := Pointersize;
		Indexed := true;
		Dplmt := 1*Wordsize;		(* see stdio.h *)
		Kind := Varbl;
		Aclass := Vars;
		Apacked := false;
	      end {with};
	      Load(Bufferattr);
	      with Bufferattr do begin
		Apacked := Iofilep^.Filepf;
		Asize := Iofilep^.Componentsize;
		Atypep := Iofiletypep;
		Adtype := Atypep^.Stdtype;
		Indexed := true;
		Dplmt := 0;
		Kind := Varbl;
		Aclass := Vars;
	      end {with};
	      Swapstak;
#endif
	      Matchtoassign(Gattr, Bufferattr.Atypep);
	      Store(Bufferattr);
	      Uco3intval(Uldc, Jdt, Intsize,
			 Iofilep^.Componentsize div Fpackunit);
	      Par(Jdt, Parcount);
	      Uco1idp(Ucup, Putptr);
	      st_fixextsc(Putptr^.symndx, scUndefined);
	    end;
	  end else begin		(* textfile			     *)

	    (*****************************************************************)
	    (* for each parameter, get one or possibly two field widths,     *)
	    (* load the appropriate parameters, and call the appropriate     *)
	    (* runtime							     *)
	    (*****************************************************************)
	    if Lstrp <> nil then begin
	      if Lstrp^.Form = Subrange then begin
		Lstrp := Lstrp^.Hosttype;
	      end;
	    end;
	    if Lstrp <> nil then begin
	      with Lstrp^ do begin
		if (Form = Scalar) and ((Scalkind <> Declared)
		 or (Stdtype <> Ldt) or (Lstrp = Boolptr)) then begin
		  (* integer, real, character, boolean, but NOT enumerated   *)
		  (* type						     *)
		  Lsupport := Writesupport[Stdtype];
		  Defaultwidth := Widthdefault[Stdtype];
		  if Lstrp = Boolptr then begin
		    Lsupport := Writeboolean;
		    Defaultwidth := 6;
		  end else if Lstrp = Charptr then begin
		    Lsupport := Writechar;
		    Defaultwidth := 1;
		  end;
		end else if Strng(Lstrp) then begin
		  if Inxtype <> nil then begin
		    Getbounds(Inxtype, Lmin, Lmax);
		    Lsize := Lmax-Lmin+1;
		  end else begin
		    Lsize := 0;
		  end;
		  Defaultwidth := Lsize;
		  Uco3intval(Uldc, Ldt, Intsize, Lsize);
		  Par(Ldt, Parcount);
		  Lsupport := Writestring;
		end else if Form = Scalar then begin
		  (* enumerated type					     *)
		  if Standrdonly then begin
		    Warning(212);
		  end;
		  LoadTableaddress(Lstrp);
		  Par(Adt, Parcount);
		  Lsupport := Writeenum;
		  Defaultwidth := 0;
		end else if Form = Power then begin
		  (* set						     *)
		  if Basetype <> nil then begin
		    if Basetype^.Form = Subrange then begin
		      Llstrp := Basetype^.Hosttype;
		    end else begin	(* not subrange 		     *)
		      Llstrp := Basetype;
		    end;
		  end;
		  if Llstrp <> nil then begin
		    with Llstrp^ do begin
		      if not (Form = Scalar) then begin
			Error(458);
		      end;
		      if (Scalkind = Declared) then begin
			Defaultwidth := 0;
			LoadTableaddress(Llstrp);
			Par(Adt, Parcount);
			Scalartype := Declaredform;
		      end else begin
			if Llstrp = Charptr then begin
			  Defaultwidth := 3;
			end else begin
			  Defaultwidth := Widthdefault[Stdtype];
			end;
			Uco3intval(Uldc, Adt, Pointersize, -1);
			Par(Adt, Parcount);
			if Llstrp = Charptr then begin
			  Scalartype := Charform;
			end else if Stdtype in [Jdt, Ldt] then begin
			  Scalartype := Integerform;
			end else begin
			  Error(458);
			end;
		      end;
		    end {with};
		  end;

		  Uco3intval(Uldc, Jdt, Intsize, Softmin);
		  Par(Jdt, Parcount);
		  Uco3intval(Uldc, Jdt, Intsize, Softmax);
		  Par(Jdt, Parcount);
		  Uco3intval(Uldc, Jdt, Intsize, ord(Scalartype));
		  Par(Jdt, Parcount);
		  Lsupport := Writeset;
		end else begin		(* illegal type 		     *)
		  Lsupport := Writechar; {dummy}
		  Error(458);
		end;
	      end {with};
	    end;

	    if Sy = Colonsy then begin	(* field width			     *)
	      Insymbol;
	      Expression(Fsys+[Commasy, Colonsy]);
	      if Lstrp <> nil then begin
		if (Gattr.Atypep <> Intptr)
		 and (Gattr.Atypep <> Cardinalptr) then begin
		  Error(458);
		end;
		Load(Gattr);
		Par(Gattr.Adtype, Parcount);
	      end;
	    end else begin		(* sy <> colonsy		     *)
	      Uco3intval(Uldc, Ldt, Intsize, Defaultwidth);
	      Par(Ldt, Parcount);
	    end;
	    if Sy = Colonsy then begin	(* second format modifier	     *)
	      Insymbol;
	      if ((Lstrp = Intptr) or (Lstrp = Cardinalptr)) then begin
		if Standrdonly then begin
		  Warning(212);
		end;
		Expression(Fsys+[Commasy]);
		if (Gattr.Adtype <> Jdt) and (Gattr.Adtype <> Ldt) then begin
		  Error(269);
		end;
		Load(Gattr);
		Par(Gattr.Adtype, Parcount);
	      end else if Comptypes(Realptr, Lstrp)
		  or Comptypes(Doubleptr, Lstrp) then begin
		Expression(Fsys+[Commasy]);
		if (Gattr.Atypep <> Intptr)
		 and (Gattr.Atypep <> Cardinalptr) then begin
		  Error(458);
		end;
		Load(Gattr);
		Par(Gattr.Adtype, Parcount);
	      end else begin
		Error(258);
	      end;
	    end else if Lstrp <> nil then begin
	      with Lstrp^ do begin
		if ((Stdtype = Jdt) or (Stdtype = Ldt) or (Form = Power)) then begin
		  Uco3intval(Uldc, Ldt, Intsize, 10);
		  Par(Ldt, Parcount);
		end else if Stdtype in [Rdt, Qdt, Xdt] then begin
		  Uco3intval(Uldc, Jdt, Intsize, -1);
		  Par(Jdt, Parcount);
		end;
	      end {with};
	    end;

	    if Lstrp <> nil then begin
	      Support(Lsupport);
	    end;
	  end;

	  More := (Sy = Commasy);
	  if More then begin
	    Exprprepass(stak^.tree);
	    (* no need call Genexpr because it is not a function	     *)
	    Popstak;
	    Insymbol;
	    Firstread := false;
	    Stdcallinit(Parcount);
	  end else if Fidp^.Key = Spwriteln then begin
	    Exprprepass(stak^.tree);
	    (* no need call Genexpr because it is not a function	     *)
	    Popstak;
	    Stdcallinit(Parcount);
	  end;
	until not More;
      end;

      if Fidp^.Key = Spwriteln then begin
	if not Istextfile then begin
	  Error(366);
	end;
	Fileattr := Iofileattr;
	Load(Fileattr);
	Par(Adt, Parcount);
	Support(Writeline);
      end;

      if not Norightparen then begin
	if Sy = Rparentsy then begin
	  Insymbol;
	end else if not Norightparen then begin
	  Warning(152);
	end;
      end;
      if Lstamp > 0 then begin
	Freetemps(Lstamp);
      end;
    end {procedure Writewriteln};

(************************************************************************)
(*									*)
(*  PACKUNPACK -- generates code to pack or unpack arrays		*)
(*	       -- this really should call a primitive subroutine	*)
(*		  instead						*)
(*									*)
(*  algorithm for PACK(A,I,Z), where A is unpacked array, Z is packed	*)
(*	array, and I is the element of A to start with			*)
(*									*)
(*     T1 := address (A) + (I-lowerbound(A))*stsize(aeltype(A)) 	*)
(*     T2 := address (Z)						*)
(*     T3 := T2 + stsize(Z)						*)
(*									*)
(* 1:  ILOD T1								*)
(*     ISTR T2								*)
(*     T1 := T1 + stsize(aetype(A))					*)
(*     T2 := T2 + packsize(aeltype(Z))					*)
(*     if T2 < T3 then goto 1						*)
(*									*)
(************************************************************************)
  procedure Packunpack;
    var
      A, I, Z, T1, T2, T3, T4, T5, T6, T1save, T2save, T3save, T4save, T5save, T6save: Attr;
      Amin, Amax, Aelsize: integer;
      Zmin, Zmax, Zelsize : integer;
      Commondtype : Datatype;
      Lstamp : integer;

    procedure Createt1;
      var
	indirkind : Indirtype;
      begin
	if I.Kind = Cnst then begin
	  A.Dplmt := A.Dplmt+((I.Cval.Ival-Amin)*Aelsize);
	end;
	if A.Indirect = Hind then begin
	  indirkind := Hind;
	end else begin
	  indirkind := Aind;
	end;
	Loadaddress(A);
	if I.Kind <> Cnst then begin
	  Load(I);
	  if Amin > 0 then begin
	    Uco2typint(Udec, I.Adtype, Amin);
	  end else if Amin < 0 then begin
	    Uco2typint(Uinc, I.Adtype, -Amin);
	  end;
	  Uco2typint(Uixa, I.Adtype, Aelsize);
	end;
	if indirkind = Hind then begin
	  Getatemp(T1save, Heapptr, Lstamp, true);
	end else begin
	  Getatemp(T1save, Addressptr, Lstamp, true);
	end;
	T1 := T1save; Store(T1);
      end {procedure Createt1};

    procedure Createt2;
      var
	indirkind : Indirtype;
      begin
	if Z.Indirect = Hind then begin
	  indirkind := Hind;
	end else begin
	  indirkind := Aind;
	end;
	Loadaddress(Z);
	if indirkind = Hind then begin
	  Getatemp(T2save, Heapptr, Lstamp, true);
	end else begin
	  Getatemp(T2save, Addressptr, Lstamp, true);
	end;
	T2 := T2save; Store(T2);
	if Zelsize < addrunit then begin
	  Getatemp(T4save, Cardinalptr, Lstamp, true);
	  Uco3intval(Uldc, Ldt, Intsize, 0);
	  T4 := T4save; Store(T4);
	end;
      end {procedure Createt2};

    procedure Createt3;
      var
	indirkind : Indirtype;
      begin
	if Z.Atypep <> nil then begin
	  Getbounds(Z.Atypep^.Inxtype, Zmin, Zmax);
	end;
	T1 := T1save; Load(T1);
	Uco2typint(Uinc, Adt, (Zmax - Zmin + 1) * Aelsize div addrunit);
	if indirkind = Hind then begin
	  Getatemp(T3save, Heapptr, Lstamp, true);
	end else begin
	  Getatemp(T3save, Addressptr, Lstamp, true);
	end;
	T3 := T3save; Store(T3);
      end {procedure Createt3};

    procedure Getoffset (
	    var Fattr : Attr;
		Fsys : Setofsys;
		Compatypep : Strp);
      begin				(* getoffset			     *)
	Expression(Fsys);
	Fattr := Gattr;
	with Fattr do begin
	  if (Atypep <> nil) and not Comptypes(Atypep, Compatypep) then Error(458);
	end {with};
	if (Sy = Commasy) and (Commasy in Fsys) then begin
	  Insymbol;
	end else if (Sy <> Rparentsy) or not (Rparentsy in Fsys) then begin
	  Error(458);
	end;
      end {procedure Getoffset};

    procedure Getvar (
	    var Fattr : Attr;
		Fsys : Setofsys;
		Compatypep : Strp);
      var
	Atypep : Strp;
      begin				(* getvar			     *)
	Getvariable(Fsys);
	Fattr := Gattr;
	Atypep := Fattr.Atypep;
	if Atypep <> nil then begin
	  if Atypep^.Form <> Arrays then begin
	    Error(458);
	  end else if Atypep^.Aeltype <> nil then begin
	    if Compatypep = nil then begin (* getting first array	     *)
	      (* if packing and array already packed or vice-versa, error  *)
	      if Atypep^.Arraypf = (Fidp^.Key = Sppack) then begin
		Error(458);
	      end;
	      if Fidp^.Key = Sppack then begin
		Aelsize := Atypep^.Aelsize;
	      end else begin
		Zelsize := Atypep^.Aelsize;
	      end;
	      Commondtype := Atypep^.Aeltype^.Stdtype;
	    end else begin		(* getting second array 	     *)
	      if (Atypep^.Arraypf = Compatypep^.Arraypf)
#if 0
	       or not Comptypes(Atypep^.Inxtype, Compatypep^.Inxtype)
#endif
	       or (Atypep^.Aeltype <> Compatypep^.Aeltype) then begin
		Error(458);
	      end;
	      if Fidp^.Key = Sppack then begin
		Zelsize := Atypep^.Aelsize;
	      end else begin
		Aelsize := Atypep^.Aelsize;
	      end;
	    end;
	  end;
	end;
	if (Sy = Commasy) and (Commasy in Fsys) then begin
	  Insymbol;
	end else if (Sy <> Rparentsy) or not (Rparentsy in Fsys) then begin
	  Error(458);
	end;
      end {procedure Getvar};

    begin				(* packunpack *)
      Lstamp := 0;
      if Sy = Lparentsy then begin
	Insymbol;
      end else begin
	Warning(153);
      end;
      Amin := 0;
      Amax := 0;
      Zmin := 0;
      Zmax := 0;
      Aelsize := 0;
      Zelsize := 0;
      if Fidp^.Key = Sppack then begin
	Getvar(A, [Commasy], nil);
	if A.Atypep <> nil then begin
	  Getbounds(A.Atypep^.Inxtype, Amin, Amax);
	  Getoffset(I, [Commasy], A.Atypep^.Inxtype);
	end else begin
	  Getoffset(I, [Commasy], nil);
	end;
	Createt1;
	Getvar(Z, [Commasy, Rparentsy], A.Atypep);
	Createt2;
      end else begin			(* unpack *)
	Getvar(Z, [Commasy], nil);
	Createt2;
	Getvar(A, [Commasy], Z.Atypep);
	if A.Atypep <> nil then begin
	  Getbounds(A.Atypep^.Inxtype, Amin, Amax);
	  Getoffset(I, [Commasy, Rparentsy], A.Atypep^.Inxtype);
	end else begin
	  Getoffset(I, [Commasy, Rparentsy], nil);
	end;
	Createt1;
      end;
      Createt3;

      Lastuclabel := Lastuclabel+1;
      Ucolab(Lastuclabel, 0, 0);

      if Fidp^.Key = Sppack then begin
	if Zelsize >= addrunit then begin
	  T2 := T2save; Load(T2);
	  T1 := T1save; Load(T1);
	  Uco3int(Uilod, Commondtype, Aelsize, 0);
	  Genexpr(stak^.next^.tree);
	  Genexpr(stak^.tree);
	  Popstak;
	  Popstak;
	  Uco3int(Uistr, Commondtype, Zelsize, 0);
	end else begin
	  T2 := T2save; Load(T2);
	  T4 := T4save; Load(T4);
	  assert((Bytesize = 8) and (Wordsize = 32));
	  Uco3intval(Uldc, Ldt, Intsize, 5);
	  Uco1type(Ushr, Ldt);
	  Uco2typint(Uixa, Ldt, Wordsize);
	  Getatemp(T6save, Cardinalptr, Lstamp, true);
	  T6 := T6save; Store(T6);
	  T6 := T6save; Load(T6);
	  Uco3int(Uilod, Ldt, Wordsize, 0);
	  Getatemp(T5save, Cardinalptr, Lstamp, true);
	  T5 := T5save; Store(T5);	(* save word containing bit-field *)
	  T6 := T6save; Load(T6);
	  T5 := T5save; Load(T5);
	  T4 := T4save; Load(T4);
	  if lsb_first then begin
	    Uco1type(Ushr, Ldt);
	    T1 := T1save; Load(T1);
	    Uco3int(Uilod, Commondtype, Aelsize, 0);
	    Uco1type(Uxor, Ldt);
	    Uco3intval(Uldc, Ldt, Intsize, lshift(1,Zelsize)-1);
	    Uco1type(Uand, Ldt);
	    T4 := T4save; Load(T4);
	    Uco1type(Ushl, Ldt);
	    T5 := T5save; Load(T5);
	    Uco1type(Uxor, Ldt);
	  end else begin
	    Uco1type(Ushl, Ldt);
	    Uco3intval(Uldc, Ldt, Intsize, Wordsize-Zelsize);
	    Uco1type(Ushr, Ldt);
	    T1 := T1save; Load(T1);
	    Uco3int(Uilod, Commondtype, Aelsize, 0);
	    Uco1type(Uxor, Ldt);
	    Uco3intval(Uldc, Ldt, Intsize, Wordsize-Zelsize);
	    Uco1type(Ushl, Ldt);
	    T4 := T4save; Load(T4);
	    Uco1type(Ushr, Ldt);
	  end;
	  T5 := T5save; Load(T5);
	  Uco1type(Uxor, Ldt);
	  Genexpr(stak^.next^.tree);
	  Genexpr(stak^.tree);
	  Popstak;
	  Popstak;
	  Uco3int(Uistr, Ldt, Wordsize, 0);
	end;
      end else begin			(* Fidp^.Key = SPUNPACK 	     *)
	T1 := T1save; Load(T1);
	T2 := T2save; Load(T2);
	if Zelsize >= addrunit then begin
	  Uco3int(Uilod, Commondtype, Zelsize, 0);
	end else begin
	  T4 := T4save; Load(T4);
	  assert((Bytesize = 8) and (Wordsize = 32));
	  Uco3intval(Uldc, Ldt, Intsize, 5);
	  Uco1type(Ushr, Ldt);
	  Uco2typint(Uixa, Ldt, Wordsize);
	  Uco3int(Uilod, Ldt, Wordsize, 0);
	  T4 := T4save; Load(T4);
	  if lsb_first then begin
	    if Commondtype = Jdt then begin
	      Uco3intval(Uldc, Ldt, Intsize, Wordsize-Zelsize);
	      Uco1type(Uxor, Ldt);
	      Uco1type(Ushl, Ldt);
	      Uco2typtyp(Ucvt, Ldt, Jdt);
	      Uco3intval(Uldc, Ldt, Intsize, Wordsize-Zelsize);
	      Uco1type(Ushr, Jdt);
	    end else begin
	      Uco1type(Ushr, Ldt);
	      Uco3intval(Uldc, Ldt, Intsize, lshift(1,Zelsize)-1);
	      Uco1type(Uand, Ldt);
	    end;
	  end else begin
	    Uco1type(Ushl, Ldt);
	    if Commondtype <> Ldt then begin
	      Uco2typtyp(Ucvt, Ldt, Commondtype);
	    end;
	    Uco3intval(Uldc, Ldt, Intsize, Wordsize-Zelsize);
	    Uco1type(Ushr, Commondtype);
	  end;
	end;
	Genexpr(stak^.next^.tree);
	Genexpr(stak^.tree);
	Popstak;
	Popstak;
	Uco3int(Uistr, Commondtype, Aelsize, 0);
      end;
      T1 := T1save; Load(T1);
      Uco2typint(Uinc, Adt, Aelsize div addrunit);
      T1 := T1save; Store(T1);
      if Zelsize < addrunit then begin
	T4 := T4save; Load(T4);
	Uco2typint(Uinc, Ldt, Zelsize);
	T4 := T4save; Store(T4);
      end else begin
	T2 := T2save; Load(T2);
	Uco2typint(Uinc, Adt, Zelsize div addrunit);
	T2 := T2save; Store(T2);
      end;
      T1 := T1save; Load(T1);
      T3 := T3save; Load(T3);
      Uco1type(Uneq, Adt);
      Genexpr(stak^.tree);
      Popstak;
      Uco1int(Utjp, Lastuclabel);
      do_expr := false;

      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
      Freetemps(Lstamp);
    end {procedure Packunpack};

(************************************************************************)
(*									*)
(* NEWDISPOSE -- parses a call to New and Dispose, and caluculates	*)
(*   the correct size of the item to be allocated or disposed of	*)
(*									*)
(* 'New' allocates storage for a variable                               *)
(* in the heap. 'Dispose' de-allocates the storage occupied by          *)
(* such a variable.  In this implementation, this can be stack-based,	*)
(* in which case the storage of all variables allocated later than the	*)
(* specified one are also released, or a true dispose can be used.  In	*)
(* the former case, NEW and DISPOSE instructions are generated, but the *)
(* user can set a switch so that runtimes routines are called instead.	*)
(*									*)
(************************************************************************)
  procedure Newdispose;
    label
      777;

    var
      Lstrp, Lstrp1 : Strp;
      Zerorec : boolean;
      Lsize : integer;
      Lvalu : Valu;
      Lattr : Attr;
      Parcount : integer;

    begin				(* newdispose			     *)
      if Sy = Lparentsy then begin
	Insymbol;
      end else begin
	Warning(153);
      end;

#if 0
      Stdcallinit(Parcount);
      Getvariable(Fsys+[Commasy, Rparentsy]); (* parse the pointer	     *)
      if Fidp^.Key = Spnew then begin
	Formalcheck(Gattr);
	Loadaddress(Gattr);		(* pass the address of the pointer   *)
      end else begin
	Load(Gattr);
      end;				(* pass the pointer itself	     *)
      Par(Adt, Parcount);
#else
      if Fidp^.Key = Spnew then begin
	Getvariable(Fsys+[Commasy, Rparentsy]); (* parse the pointer	     *)
	Stdcallinit(Parcount);
	Formalcheck(Gattr);
      end else begin
	Stdcallinit(Parcount);
	Expression(Fsys+[Commasy, Rparentsy]); (* parse the pointer	     *)
	Load(Gattr);
	Par(Adt, Parcount);
      end;				(* pass the pointer itself	     *)
#endif

      Zerorec := false;

      Lstrp := nil;
      Lsize := 0;
      Lattr := Gattr;
      if Lattr.Atypep <> nil then begin
	with Lattr.Atypep^ do begin
	  if Form = SPointer then begin
	    if Eltype <> nil then begin
	      Lsize := Eltype^.Stsize;
	      Zerorec := Eltype^.Hasfiles or Eltype^.Hasholes;
	      if Eltype^.Form = Records then begin
		Lstrp := Eltype^.Recvar;
	      end else if Eltype^.Form = Arrays then begin
		Lstrp := Eltype;
	      end;
	    end;
	  end else begin
	    Error(458);
	  end;
	end {with};
      end;
      while Sy = Commasy do begin	(* parse flags to figure out total   *)
					(* size 			     *)
	Insymbol;
	Constant(Fsys+[Commasy], Lstrp1, Lvalu);
	if Lstrp = nil then begin
	  Error(408);
	end else if Strng(Lstrp) or (Lstrp1 = Realptr) or (Lstrp1 = Doubleptr) or (Lstrp1 = Extendedptr) then begin
	  Error(460);
	end else begin
	  (* Lstrp points to the current variant, Lstrp1 to the type of the  *)
	  (* expression just parsed					     *)
	  if Lstrp^.Form = Tagfwithid then begin
	    if not Comptypes(Lstrp^.Tagfieldp^.Idtype, Lstrp1) then begin
	      Error(458);
	    end;
	  end else if Lstrp^.Form = Tagfwithoutid then begin
	    if not Comptypes(Lstrp^.Tagfieldtype, Lstrp1) then begin
	      Error(458);
	    end;
	  end else begin
	    Error(358);
	  end;

	  (*******************************************************************)
	  (* find the size that corresponds to the variant that matches with *)
	  (* the value just parsed					     *)
	  (*******************************************************************)
	  Lstrp1 := Lstrp^.Fstvar;
	  (* Now Lstrp1 points to the list of possible values for the	     *)
	  (* variant							     *)
	  while Lstrp1 <> nil do begin
	    with Lstrp1^ do begin
	      if Varval = Lvalu.Ival then begin (* match found		     *)
		Lsize := Stsize;
		Lstrp := Subvar;
		goto 777;
	      end else begin
		Lstrp1 := Nxtvar;
	      end;
	    end {with};
	  end {while};
	  (* no match found; allocate the minimum			     *)
	  Lsize := Lstrp^.Elsevar^.Stsize;
	  Lstrp := nil;
777 : ;
	end;
      end {while};

      (***********************************************************************)
      (* round the number of storage units needed up to the next align unit  *)
      (***********************************************************************)
      Lsize := Roundup(Lsize, SpAlign) div Addrunit;
      Uco3intval(Uldc, Ldt, Intsize, Lsize);
      Par(Jdt, Parcount);
      if Fidp^.Key = Spnew then begin
	Uco3intval(Uldc, Ldt, Intsize, ord(Zerorec));
	Par(Ldt, Parcount);
	Support(Allocate);
	Store(Lattr);
	do_expr := false;
      end else begin
	Support(Free);
      end;
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
    end {procedure Newdispose};

  procedure sizeof_function;
    label
      777;

    var
      Lidp : Idp;
      Lstrp, Lstrp1 : Strp;
      Lsize : integer;
      Lvalu : Valu;
      Lattr : Attr;

    begin
      if Sy = Lparentsy then begin
	Insymbol;
      end else begin
	Warning(153);
      end;

      Lstrp := nil;
      Lsize := 0;

      Lidp := nil;
      if Sy = Identsy then begin
	Searchid([Types, Konst, Vars, Field, Proc, Func], Lidp);
      end;
      if (Lidp <> nil) and (Lidp^.Klass = Types) then begin
	Lstrp := Lidp^.Idtype;
	Insymbol;
      end else begin
        Expression(Fsys+[Commasy, Rparentsy]);
	Lstrp := Gattr.Atypep;
	if (Gattr.Kind = Expr)
	    or ((Gattr.Kind = Varbl) and Gattr.Indexed) then begin
	  Popstak;
	end;
      end;

      if Lstrp <> nil then begin
	Lsize := Lstrp^.Stsize;
	if Lstrp^.Form = Records then begin
	  Lstrp := Lstrp^.Recvar;
	end;
      end;

      while Sy = Commasy do begin	(* parse flags to figure out total   *)
					(* size 			     *)
	Insymbol;
	Constant(Fsys+[Commasy], Lstrp1, Lvalu);
	if Lstrp = nil then begin
	  Error(408);
	end else if Strng(Lstrp) or (Lstrp1 = Realptr) or (Lstrp1 = Doubleptr) or (Lstrp1 = Extendedptr) then begin
	  Error(460);
	end else begin
	  (* Lstrp points to the current variant, Lstrp1 to the type of the  *)
	  (* expression just parsed					     *)
	  if Lstrp^.Form = Tagfwithid then begin
	    if not Comptypes(Lstrp^.Tagfieldp^.Idtype, Lstrp1) then begin
	      Error(458);
	    end;
	  end else if Lstrp^.Form = Tagfwithoutid then begin
	    if not Comptypes(Lstrp^.Tagfieldtype, Lstrp1) then begin
	      Error(458);
	    end;
	  end else begin
	    Error(358);
	  end;

	  (*******************************************************************)
	  (* find the size that corresponds to the variant that matches with *)
	  (* the value just parsed					     *)
	  (*******************************************************************)
	  Lstrp1 := Lstrp^.Fstvar;
	  (* Now Lstrp1 points to the list of possible values for the	     *)
	  (* variant							     *)
	  while Lstrp1 <> nil do begin
	    with Lstrp1^ do begin
	      if Varval = Lvalu.Ival then begin (* match found		     *)
		Lsize := Stsize;
		Lstrp := Subvar;
		goto 777;
	      end else begin
		Lstrp1 := Nxtvar;
	      end;
	    end {with};
	  end {while};
	  (* no match found; allocate the minimum			     *)
	  Lsize := Lstrp^.Elsevar^.Stsize;
	  Lstrp := nil;
777 : ;
	end;
      end {while};

      with Gattr do begin
	Kind := Cnst;
	Atypep := Intptr;
	Asize := Intsize;
	Cval.Ival := Lsize div Addrunit;
	Adtype := Ldt;
      end {with};

      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
    end {sizeof_function};

  procedure firstlast (
	      fn: Stdprocfunc );
    var
      Lidp : Idp;
      Lstrp, Istrp : Strp;
      Lval, vmin, vmax : integer;
      Indexnumber : integer;
      i : integer;
      Ivalu : Valu;
    begin
      if Sy = Lparentsy then begin
	Insymbol;
      end else begin
	Warning(153);
      end;

      Lstrp := nil;
      Lval := 0;

      Lidp := nil;
      if Sy = Identsy then begin
	Searchid([Types, Konst, Vars, Field, Proc, Func], Lidp);
      end;
      if (Lidp <> nil) and (Lidp^.Klass = Types) then begin
	Lstrp := Lidp^.Idtype;
	Insymbol;
      end else begin
        Expression(Fsys+[Commasy, Rparentsy]);
	Lstrp := Gattr.Subkind;
	if Lstrp = nil then begin
	  Lstrp := Gattr.Atypep;
	end;
	if (Gattr.Kind = Expr) or ((Gattr.Kind = Varbl) and Gattr.Indexed) then begin
	  Popstak;
	end;
      end;

      if Lstrp <> nil then begin
	if (fn = Splbound) or (fn = Sphbound) then begin
	  Indexnumber := 1;
	  if Sy = Commasy then begin
	    Insymbol;
	    ConstantExpression(Fsys+[Rparentsy], Istrp, Ivalu);
	    if Istrp <> Intptr then Error(255)
	    else Indexnumber := Ivalu.ival;
	  end;
	  for i := Indexnumber downto 2 do begin
	    if Lstrp^.form = Arrays then begin
	      Lstrp := Lstrp^.Aeltype;
	    end else begin
	      Error(409);
	    end;
	  end {for};
	  if Lstrp^.form = Arrays then begin
	    Lstrp := Lstrp^.Inxtype;
	  end else begin
	    Error(409);
	  end;
	end;
	Getbounds(Lstrp, vmin, vmax);
	if (fn = Splbound) or (fn = Spfirst) then begin
	  Lval := vmin;
	end else begin
	  Lval := vmax;
	end;
      end;

      with Gattr do begin
	Kind := Cnst;
	Atypep := Lstrp;
	Adtype := Jdt;
	if Lstrp <> nil then begin
	  Adtype := Lstrp^.Stdtype;
	end;
	Asize := Intsize;
	Cval.Ival := Lval;
      end {with};

      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
    end {procedure firstlast};

  procedure break_continue (
	      l : integer);
    begin
      if l = 0 then begin
	Error(323);
      end else begin
	Uco1int(Uujp, l);
      end;
      do_expr := false;
    end {procedure break_continue};

  procedure Assert_statement;
    var
      falselabel : integer;
      Parcount : integer;
    begin
      if Sy = Lparentsy then begin
	Insymbol;
      end else begin
	Warning(153);
      end;
      Expression(Fsys+[Rparentsy, Commasy]);
      Load(Gattr);
      if Gattr.Atypep <> Boolptr then begin
	Error(359);
      end;
      if Sy <> Commasy then begin
	Exprprepass(stak^.tree);
	Genexpr(stak^.tree);
	Popstak;
	Uco0(Uchkt);
      end else begin
	Insymbol;
	Lastuclabel := Lastuclabel+1;	(* generate the jump to the else     *)
					(* part 			     *)
	falselabel := Lastuclabel;
	Jumpboolexpr(stak^.tree, false, falselabel, 0);
	Popstak;
	Stdcallinit(Parcount);
	Expression(Fsys+[Rparentsy]);
	if not Strng(Gattr.Atypep) then begin
	  Error(503);
	end;
	Loadaddress(Gattr);
	Par(Adt, Parcount);
	Support(Assertionfailure);
	Exprprepass(stak^.tree);
	Popstak;
	Ucolab(falselabel, 0, 0);
      end;
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(164);
      end;
      do_expr := false;
    end {procedure Assert_statement};

(*Callspecial*)
(****************************************************************)
(*								*)
(*	CALLSPECIAL -- parses call to standard procedure or	*)
(*	   that needs special handling, i.e. has a		*)
(*	   variable number of parameters or is done at compile	*)
(*	   time 						*)
(*								*)
(****************************************************************)
  begin 				(* Callspecial			     *)
    Fsys := Fsys+[Rparentsy];
    case Fidp^.Key of
    Spread, Spreadln : Readreadln;
    Spwrite, Spwriteln : Writewriteln;
    Sppack, Spunpack : Packunpack;
    Spnew, Spdispose : Newdispose;
    Spbreak : break_continue(loop_break_label);
    Spcontinue : begin
      break_continue(loop_continue_label);
      ContinueSeen := true;
    end;
    Spassert : Assert_statement;
    Spsizeof : sizeof_function;
    Spfirst, Splast, Splbound, Sphbound : firstlast(Fidp^.Key);
    end {case};
  end {procedure Callspecial};

(*Callinline*)
(****************************************************************)
(*								*)
(*	CALLINLINE  -- parses call to standard procedure or	*)
(*	   function that is handled by				*)
(*	   a U-code instruction rather than a procedure call	*)
(*								*)
(****************************************************************)
procedure Callinline /* ( Fsys : Setofsys; Fidp : Idp)	*/;
  var
    Lattr : Attr;
    Argdtype : Datatype;

  begin 				(* Callinline			     *)
    if Standrdonly then begin
      if Fidp^.Uinst in [Umin, Umax, Uand, Uior, Uxor, Unot, Ushl, Ushr] then
	begin
	Warning(212);
      end;
    end;
    if Sy = Lparentsy then begin
      Insymbol;
    end else begin
      Warning(153);
    end;
    Expression(Fsys+[Commasy, Rparentsy]);
    Load(Gattr);
    Argdtype := Gattr.Adtype;
    if not (Argdtype in Fidp^.Dtypes) then begin
      Error(503);
    end;
    if Fidp^.Uinst in [Umin, Umax, Uand, Uior, Uxor] then begin
					(* process additional arguments      *)
      while Sy = Commasy do begin
	Lattr := Gattr;
	Insymbol;
	Expression(Fsys+[Commasy, Rparentsy]);
	if not (Gattr.Adtype in Fidp^.Dtypes) then begin
	  Error(503);
	end;
	Matchtypes(Lattr);
	Loadboth(Lattr);
	Argdtype := Gattr.Adtype;
	Gattr.Kind := Expr;
	Uco1type(Fidp^.Uinst, Argdtype);
      end {while};
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
      return;
    end else if Fidp^.Uinst in [Ushl, Ushr] then begin (* process second     *)
					(* argument			     *)
      Lattr := Gattr;
      if Sy <> Commasy then begin
	Error(256);
      end else begin
	Insymbol;
	Expression(Fsys+[Rparentsy]);
	if not (Gattr.Adtype in [Jdt, Ldt]) then begin
	  Error(503);
	end;
	Loadboth(Lattr);
      end;
    end;
    with Gattr do begin 		(* change gattr to reflect result of *)
					(* operation			     *)
      Kind := Expr;
      (* for most functions, the resulttype is the type of its arguments, so *)
      (* Gattr doesn't need to get changed for others, it is explicitly      *)
      (* given: 							     *)
      if Fidp^.Resdtype <> nil then begin
	Atypep := Fidp^.Resdtype;
	Adtype := Atypep^.Stdtype;
      end else if (Fidp^.Uinst = Ucvt) or (Fidp^.Uinst = Urnd) then begin
	(* for round and trunc, it must be computed			     *)
	Atypep := Intptr;
	Adtype := Atypep^.Stdtype;
      end;
    end {with};
    case Fidp^.Uinst of
    Ucvt, Urnd : begin
	if (Fidp^.idname = 'chr') and runtimecheck then
	  Uco2typint(Uchkh, Argdtype, 255);
	if Gattr.Adtype <> Argdtype then begin
	  Uco2typtyp(Fidp^.Uinst, Gattr.Adtype, Argdtype);
	end;
      end {case Ucvt};
    Uinc, Udec : Uco2typint(Fidp^.Uinst, Argdtype, 1);
    Uabs, Usqr, Uodd, Unot, Ushl, Ushr : Uco1type(Fidp^.Uinst, Argdtype);
    end {case};
    if Sy = Rparentsy then begin
      Insymbol;
    end else begin
      Warning(152);
    end;
  end {procedure Callinline};

(*Callregular[Compparam]*)
(****************************************************************)
(*								*)
(*	CALLREGULAR -- parses a call to a nonspecial		*)
(*	   procedure or function				*)
(*								*)
(*	For each parameter:					*)
(*	   if the parameter is a procedure/function, checks to	*)
(*	      make sure it has a congruent parameter list and	*)
(*	      result type					*)
(*	   otherwise, checks to make sure that the type is	*)
(*	      compatible					*)
(*	   if formal parameter or large parameter (whose value	*)
(*	      is passed indirectly), loads the address of the	*)
(*	      parameter, else loads the parameter directly	*)
(*	If the procedure has been passed, loads its address	*)
(*	      and emits an ICUF, else emits a CUP		*)
(*	Changes Gattr to reflect the function result type	*)
(*								*)
(*	Contains procedures:					*)
(*								*)
(*	Comparam:  tests if two parameter lists are congruent	*)
(*	Loadprocedureparam:  loads procedure or function	*)
(*	Loadparam:  loads any other procedure type		*)
(*								*)
(****************************************************************)
procedure Callregular /* ( Fsys : Setofsys; Fidp: Idp)	*/;

  var
    Pcount : integer;
    Paramidp : Idp;
    Lastfilestrp : Strp;
    Lattr: Attr;
    Lkind : Idkind;
    Done : boolean;
    Lstamp : integer;
    schainused : boolean;
    lop : Uopcode;

  function Compparam (
	     Fidp1,
	     Fidp2 : Idp)
     : boolean;

    (*************************************************************************)
    (* checks to see if two parameter lists are congruent		     *)
    (*************************************************************************)

    var
      Ok : boolean;

    begin				(* compparam			     *)
      Ok := true;
      while Ok and (Fidp1 <> nil) and (Fidp2 <> nil) do begin
	with Fidp1^ do begin
	  if Comptypes(Idtype, Fidp2^.Idtype) then begin
	    if Klass = Fidp2^.Klass then begin
	      if Klass = Vars then begin
		if Vkind <> Fidp2^.Vkind then begin
		  Error(370);
		  Ok := false;
		end;
	      end else begin
		Ok := Compparam(Fparam, Fidp2^.Fparam);
	      end;
	    end else begin
	      Error(370);
	      Ok := false;
	    end;
	  end else begin
	    Error(370);
	    Ok := false;
	  end;
	  Fidp1 := Next;
	  Fidp2 := Fidp2^.Next;
	end {with};
      end {while};
      if Fidp1 <> Fidp2 then begin
	Error(554);
	Compparam := false;
      end else begin
	Compparam := Ok;
      end;
    end {function Compparam};


  procedure Loadprocedureparam (
	      Paramidp : Idp);

    (*************************************************************************)
    (* Loads procedural or functional parameter 			     *)
    (*************************************************************************)
    var
      Procedureidp, Paramlisthead : Idp;
      schainused : boolean;
      lop : Uopcode;

    begin
      if Sy <> Identsy then begin
	Error(209);
      end else begin
	Searchid([Proc, Func], Procedureidp);
	Procedureidp^.Referenced := true;
	Insymbol;
	with Procedureidp^ do begin
	  if Prockind <> Regular then begin
	    Error(510); 		(* can't pass standard procedures    *)
	  end else begin
	    if Pfkind = Actual then begin
	      Paramlisthead := Next;
	    end else begin
	      Paramlisthead := Fparam;
	    end;
	    (* now Paramlisthead points to the head of the list of	     *)
	    (* parameters for the actual procedure being passed check to see *)
	    (* that the two parameter lists are equivalent		     *)
	    if Compparam(Paramidp^.Fparam, Paramlisthead) then begin
	      if Paramidp^.Klass <> Klass then begin
		Error(503);		(* one is func, the other proc	     *)
	      end else if not Comptypes(Idtype, Paramidp^.Idtype) then begin
		Error(555);		(* different result types	     *)
	      end else begin
		(* generate code to load the procedure			     *)
		if Pfkind = Actual then begin
		  Passstaticlink(Pflev, false);
		  Par(Hdt, Pcount);
		  UcoProcpointer(Procedureidp);
      		  if Procedureidp^.Externproc and Procedureidp^.Forwdecl then
		    st_fixextsc(Procedureidp^.symndx, scUndefined);
		end else begin		(* pfkind = formal		     *)
		  schainused := Genstaticchain(Pfblock);
		  if schainused then begin
		    lop := Uisld;
		  end else begin
		    lop := Ulod;
		  end;
		  Uco5typaddr(lop, Hdt, Pfmty, Pfblock, Pfaddr, Wordsize);
		  Par(Hdt, Pcount);
		  schainused := Genstaticchain(Pfblock);
		  if schainused then begin
		    lop := Uisld;
		  end else begin
		    lop := Ulod;
		  end;
		  Uco5typaddr(lop, Fdt, Pfmty, Pfblock, Pfaddr+Wordsize, 
			      Wordsize);
		end;
	      end;
	    end;
	  end;
	end {with};
      end;
      Par(Fdt, Pcount);
    end {procedure Loadprocedureparam};

var
  Lastfileattr, Lastfileindex: attr;

  procedure Loadactualparam (
	      Paramidp : Idp;
	      Paramstrp : Strp);

    (*************************************************************************)
    (* loads a actual parameter 					     *)
    (*************************************************************************)

    var
      Lattr: attr;
    begin
      Expression(Fsys+[Commasy, Rparentsy]);
      if (Gattr.Atypep <> nil) and (Paramstrp <> nil) then begin
	(* A file not passed by reference is really the STDIO pointer. *)
	if Paramstrp^.Form = Files then begin
	  if  (Gattr.Atypep <> Paramstrp)
	  and not (    (Gattr.Atypep^.Form = Files)
		   and (   (Paramstrp = Anyfileptr)
			or (    (Paramstrp = Anytextptr)
			    and Gattr.Atypep^.Textfile))) then begin
	    Error(503);
	  end;
	  Lastfilestrp := Gattr.Atypep;
	  Gattr.Dplmt := Gattr.Dplmt + File_stdio_offset;
	  Gattr.Atypep := Addressptr;
	  Gattr.Adtype := Adt;
	  Gattr.Asize := Pointersize;
	  if Fidp = Closeptr then begin
	    if Gattr.Indexed then begin
#if 0
	      Lattr := Gattr;
	      LoadAddress (Lattr);
	      Getatemp (Lattr, Addressptr, Lstamp, false);
	      Gattr.Indirect := Aind;
	      Gattr.Indexmt := Lattr.Amty;
	      Gattr.Indexr := Lattr.Dplmt;
	      Store (Lattr);
#else
	      Getatemp (Lastfileindex, Addressptr, Lstamp, false);
	      Lattr := Lastfileindex;
	      Store (Lattr);
	      Lattr := Lastfileindex;
	      Load (Lattr);
#endif
	    end;
	    Lastfileattr := Gattr;
	  end;
	  Load (Gattr);
	  Par(Adt, Pcount);
	(* if a large set, record, or array, pass indirectly		     *)
	end else if ((Paramstrp^.Stdtype <> Mdt)
	    or ((Paramstrp^.Stsize <= Wordsize)
		and (Paramstrp^.Stsize <= Paramstrp^.Align)))
	 and (Paramstrp^.Stsize <= Parthreshold) then begin
					(* pass directly		     *)
	  (* check type of parameter					     *)
	  if not (Comptypes(Paramstrp, Gattr.Atypep) or
			   Stringpadpossible(Paramstrp, Gattr)) 
	   and not ((Paramstrp^.Stdtype in [Jdt, Ldt, Rdt, Qdt, Xdt])
		and (Gattr.Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt])) then begin
	    Error(503);
	  end;
	  (* load parameter						     *)
	  if Paramstrp^.Form = Subrange then begin
	    Loadandcheckbounds(Gattr, Paramstrp);
	    Par(Paramstrp^.Stdtype, Pcount);
	  end else if Paramstrp^.Stdtype = Sdt then begin
	    Setmatchtoassign(Gattr, Paramstrp, false);
	    Load(Gattr);
	    Partype(Paramstrp, Pcount);
	  end else begin
	    Load(Gattr);
	    if (Gattr.Adtype <> Paramstrp^.Stdtype) and 
	       (Paramstrp^.Stdtype <> Mdt) then begin
	      Matchtoassign(Gattr, Paramstrp);
	    end else if (Paramstrp^.Stdtype = Mdt) then 
	      {record or array being passed as actual parm by value}
	      Uco3int(Uilod, Ldt, Gattr.Atypep^.Stsize, 0);
	    Par(Paramstrp^.Stdtype, Pcount);
	  end;
	end else begin			(* pass indirectly		     *)
	  if Paramstrp = Anystringptr then begin
	    if not Strng(Gattr.Atypep) then begin
	      Error(503);
	    end;
	  end else if not (Comptypes(Paramstrp, Gattr.Atypep) or
			   Stringpadpossible(Paramstrp, Gattr)) then begin
	    Error(503);
	  end;
	  (* if we are going to pass a set expression indirectly, we must    *)
	  (* first store it in a temporary				     *)
	  if Paramstrp^.Form = Power then begin
	    Setmatchtoassign(Gattr, Paramstrp, false);
	    if Gattr.Kind <> Varbl then begin
	      Load(Gattr);
	      Getatemp(Lattr, Gattr.Atypep, Lstamp, false);
	      Store(Lattr);
	      Gattr := Lattr;
	    end;
	  end;
	  Loadaddress(Gattr);
	  (* if parameter is of type Anystring, then load its length	     *)
	  if Paramstrp = Anystringptr then begin
	    Par(Adt, Pcount);
	    Paramidp := Paramidp^.Next;
	    if Gattr.Kind = Cnst then begin
	      Uco3intval(Uldc, Jdt, Intsize, Gattr.Cval.Ival);
	    end else if Gattr.Atypep <> nil then begin
	      Uco3intval(Uldc, Jdt, Intsize,
		  Stringchars(Gattr.Atypep^.Stsize));
	    end;
	    Par(Jdt, Pcount);
	  end else begin
	    Partype(Gattr.Atypep, Pcount);
	  end;
	end;
      end;
    end {procedure Loadactualparam};

  procedure Loadformalparam (
	      Paramidp : Idp;
	      Paramstrp : Strp);

    (*************************************************************************)
    (* loads a formal parameter 					     *)
    (*************************************************************************)

    var
      Lidp : Idp;
      dummy : Indirtype;
      i: integer;

    begin
      if Sy <> Identsy then begin
	Error(209);
	Lidp := Uvarptr;
      end else begin
	Searchid([Vars, Field], Lidp);
	Insymbol;
      end;

      (***********************************************************************)
      (* passing a variable as a formal parameter counts as an assignment to *)
      (* it								     *)
      (***********************************************************************)
      Parseleft := true;
      Selector(Fsys+[Commasy, Rparentsy], Lidp, dummy);
      Parseleft := false;

      if Gattr.Kind <> Varbl then begin
	Error(463);
      end else begin
	Formalcheck(Gattr);
	Loadaddress(Gattr);
	Par(Adt, Pcount);
	(* check type							     *)
	if Paramstrp <> nil then begin
	  (* if was a subrange, compare with original type		     *)
	  if Gattr.Subkind <> nil then begin
	    if Gattr.Subkind <> Paramstrp then begin
	      Error(503);
	    end;
	  end else if Gattr.Atypep <> nil then begin
	    (* check for anyfile type					     *)
	    if (Paramstrp = Anyfileptr) or (Paramstrp = Anytextptr) then begin
	      if not (Gattr.Atypep^.Form = Files) then begin
		Error(503);
	      end else if (Paramstrp = Anytextptr)
	       and not (Gattr.Atypep^.Textfile) then begin
		Error(503);
	      end else begin
		Lastfilestrp := Gattr.Atypep;
	      end;
	    end else if Paramstrp = Anystringptr then begin
	      (* and anystring type					     *)
	      if not Strng(Gattr.Atypep) then begin
		Error(503);
	      end;
	      Paramidp := Paramidp^.Next;
	      if Gattr.Kind = Cnst then begin
		Uco3intval(Uldc, Jdt, Intsize, Gattr.Cval.Ival);
	      end else if Gattr.Atypep <> nil then begin
		Uco3intval(Uldc, Jdt, Intsize,
		    Stringchars(Gattr.Atypep^.Stsize));
	      end;
	      Par(Jdt, Pcount);
	    end else if Paramstrp = Anyptr then begin
	      (* AND anyptr type					     *)
	      if Gattr.Atypep^.Form <> SPointer then begin
		Error(503);
	      end;
	    end else if Gattr.Atypep <> Paramstrp then begin
	      (* all other types: must be exact match			     *)
	      Error(503);
	    end;
	  end;
	end;
      end;
    end {procedure Loadformalparam};

  procedure Loaddefaultparam (
	      Paramidp,
	      Defaultidp : Idp);
    var
      Lvalu : Valu;
      schainused : boolean;
    begin
      if (Paramidp^.Idtype = Anyfileptr)
       or (Paramidp^.Idtype = Anytextptr) then begin
	lastfilestrp := Defaultidp^.Idtype;
	with Defaultidp^ do begin
	  if Vmty in [Mmt, Pmt] then begin
	    schainused := Genstaticchain(Vblock);
	  end else begin
	    schainused := false;
	  end;
	  if schainused then begin
	    Uco5typaddr(Uisld, Adt, Vmty, Vblock, Vaddr, Pointersize);
	  end else begin
	    Uco5typaddr(Ulod, Adt, Vmty, Vblock, Vaddr, Pointersize);
	  end;
	  Par(Adt, Pcount);
	end {with};
      end else if Paramidp^.Idtype = Anystringptr then begin
	(* null string *)
	Lvalu.Ival := 1;
	new1(Lvalu.Chars);
	Lvalu.Chars^.ss[1] := ' ';
	Uco3val(Ulca, Mdt, Charsize, Lvalu);
	Par(Adt, Pcount);
	Uco3intval(Uldc, Jdt, Intsize, 0);
	Par(Jdt, Pcount);
      end else begin			(* Paramidp^.Idtype = Intptr	     *)
	Uco3intval(Uldc, Jdt, Intsize, Defaultidp^.Ival);
	Par(Jdt, Pcount);
      end;
    end {procedure Loaddefaultparam};

  procedure Finishresetrewrite;
    begin
	with Lastfilestrp^ do begin
	  if Textfile then begin
	    Uco3intval(Uldc, Ldt, Intsize, 0);
	  end else begin
	    Uco3intval(Uldc, Jdt, Intsize, Componentsize div Fpackunit);
	  end;
	  Par(Jdt, Pcount);
	end {with};
    end {procedure Finishresetrewrite};

  procedure Finishgetput;
    begin
	with Lastfilestrp^ do begin
	  Uco3intval(Uldc, Jdt, Intsize, Componentsize div Fpackunit);
	  Par(Jdt, Pcount);
	end {with};
    end {procedure Finishgetput};

  label
    exitloop;
  begin 				(* Callregular			     *)
    Lstamp := 0;
    Lastfilestrp := nil;
    Pcount := 0;
    with Fidp^ do begin
      (* give warning if non-standard proc				     *)
      if Standrdonly and Nonstandard then 
	Warning(212);
      if Externproc and Forwdecl then
	st_fixextsc(symndx, scUndefined);
      Uco1int(Umst, Pflev);		(* generate MST for the call	     *)
      Lkind := Pfkind;
      (* set Paramidp to the head of the parameter chain		     *)
      if Lkind = Actual then begin
	Paramidp := Next;
      end else begin			(* Lkind = Formal: passed procedure  *)
	Paramidp := Fparam;
      end;
    end {with};

    if Sy = Lparentsy then begin	(* parse and load parameters	     *)
      Insymbol;				(* skip '(' *)
      if Sy <> Rparentsy then begin
	while true do begin
	  if Paramidp = nil then begin
	    Error(554);
	  end else if Paramidp^.Klass in [Proc, Func] then begin
					(* procedural parameters	     *)
	    Loadprocedureparam(Paramidp);
	  end else if Paramidp^.Vkind = Actual then begin
					(* passed by value *)
	    Loadactualparam(Paramidp, Paramidp^.Idtype);
	  end else begin		(* passed by reference		     *)
	    Loadformalparam(Paramidp, Paramidp^.Idtype);
	  end;
	  if Paramidp <> nil then begin
	    if Paramidp^.Idtype = Anystringptr then begin
	      Paramidp := Paramidp^.Next^.Next;
	    end else begin
	      Paramidp := Paramidp^.Next;
	    end;
	  end;
	  Skipiferr([Commasy, Rparentsy], 256, Fsys);
	  if Sy <> Commasy then {break}goto exitloop;
	  Insymbol;
	end {while};
exitloop: ;
      end;
      if Sy = Rparentsy then begin
	Insymbol;
      end else begin
	Warning(152);
      end;
    end;

    (*************************************************************************)
    (* load any default parameters					     *)
    (*************************************************************************)
    repeat
      if Paramidp = nil then begin
	Done := true;
      end else if Paramidp^.Default = nil then begin
	Done := true;
      end else begin
	Loaddefaultparam(Paramidp, Paramidp^.Default);
	if Paramidp^.Idtype = Anystringptr then begin
	  Paramidp := Paramidp^.Next^.Next;
	end else begin
	  Paramidp := Paramidp^.Next;
	end;
	Done := false;
      end;
    until Done;

    (*************************************************************************)
    (* check to make sure enough parameters are being passed		     *)
    (*************************************************************************)
    if Paramidp <> nil then begin
      Error(554);
    end;
    (* if Reset or Rewrite, add special parameters			     *)
    if Lastfilestrp <> nil then 
      if (Fidp = Resetptr) or (Fidp = Rewriteptr) then begin
        Finishresetrewrite;
	Fidp^.parnumber := Fidp^.parnumber + 1;
      end else if ((Fidp = Getptr) and not Lastfilestrp^.Textfile)
		or (Fidp = Putptr) then begin
        Finishgetput;
	Fidp^.parnumber := Fidp^.parnumber + 1;
      end;

    (*************************************************************************)
    (* generate the Cup or Icuf 					     *)
    (*************************************************************************)
    with Fidp^ do begin
      if (not Externproc) and (Pfkind = Actual) then begin
        Passstaticlink(Pflev, true);
      end;
      Referenced := true;
      if (Fidp = Getptr) and Lastfilestrp^.Textfile then begin
	Support(Nextchar);
      end else if Lkind = Actual then begin
	Uco1idp(Ucup, Fidp);
      end else begin			(* Lkind = Formal call of a	     *)
					(* parameter procedure		     *)
	schainused := Genstaticchain(Pfblock);
	if schainused then begin
	  lop := Uisld;
	end else begin
	  lop := Ulod;
	end;
	Uco5typaddr(lop, Hdt, Pfmty, Pfblock, Pfaddr, Wordsize);
        Uco5typaddr(Upar, Adt, Rmt, 0, intRmtoffset, 32);
	schainused := Genstaticchain(Pfblock);
	if schainused then begin
	  lop := Uisld;
	end else begin
	  lop := Ulod;
	end;
	Uco5typaddr(lop, Fdt, Pfmty, Pfblock, Pfaddr+Wordsize, Wordsize);
	Uco1idp(Uicuf, Fidp);
      end;
    end {with};

    (* if Reset or Rewrite, adjust parnumber in Fidp back	     *)
    if (Fidp = Resetptr) or (Fidp = Rewriteptr) /*or (Fidp = Reviseptr)*/ then 
    begin
      if Lastfilestrp <> nil then 
	Fidp^.parnumber := Fidp^.parnumber - 1;
    end else if ((Fidp = Getptr) and not Lastfilestrp^.Textfile)
		or (Fidp = Putptr) then begin
      if Lastfilestrp <> nil then 
	Fidp^.parnumber := Fidp^.parnumber - 1;
    end else if (Fidp = Closeptr) then begin
      Exprprepass(stak^.tree);
      Popstak;
      do_expr := false;
      if Lastfileattr.Indexed then begin
	Load (Lastfileindex);
      end;
      Uco3intval(Uldc, Adt, Pointersize, 0);
      Store(Lastfileattr);
    end;

    (* modify Gattr to reflect the function result type 		     *)
    if (Fidp^.Klass = Func) then begin
      with Gattr do begin
	Atypep := Fidp^.Idtype;
	Kind := Expr;
	if Atypep <> nil then begin
	  Adtype := Atypep^.Stdtype;
	end;
      end {with};
    end;
    (* else procedure; GATTR does not need to be set			     *)
    if Lstamp > 0 then begin
      Freetemps(Lstamp);
    end;
  end {procedure Callregular};
