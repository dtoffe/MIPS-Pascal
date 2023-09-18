{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasmain.p,v 1030.7 88/02/18 14:55:04 bettina Exp $ }

#include "upasglob.h"
#include "cmplrs/uwri.h"
#include "cmplrs/uscan.h"
#include "cmplrs/uoptions.h"
#include "upaslex.h"
#include "upasinit.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upasbutil.h"
#include "upasstmt.h"
#include "upasdecl.h"
#include "upastree.h"
#include "upassym.h"
#include "upasexpr.h"
#include "upasmain.h"
#include "allocator.h"

var gleveltab: array[0..3] of integer := 
				[GLEVEL_0, GLEVEL_1, GLEVEL_2, GLEVEL_3];

(*Block,Remap*)
procedure Block /* ( Fprocp : Idp; Fsys, Leaveblocksys : Setofsys)  */;
  (* parses the block that forms the program or a procedure/function; Fprocp
     is nil if it is the imaginary outermost block *)
  label 11;
  var
    Lsy : Symbol;
    junk: integer;
    GMark: pointer;
#if 0
    Remapped : boolean;
#endif
    Forwardprocedures : Idp;
    bgnbno: integer; {number for the BGNB ucode}

#if 0
(************************************************************************)
(*									*)
(*	REMAP -- combines F and M memory into M memory			*)
(*									*)
(*	Initially all large objects are mapped into M memory		*)
(*	and simple objects into F memory.  This is done to make 	*)
(*	simple objects easier to address and to make sure that memory	*)
(*	is allocated in the parameter area only for the addresses of	*)
(*	large objects, not the objects themselves.  Remap combines	*)
(*	the two memory types by copyng the objects in F memory into	*)
(*	the front of M memory.						*)
(*									*)
(************************************************************************)

  procedure Remap (
	      Fidp : Idp);

    var
      Moffset : Addrrange;


    procedure RemapId (
		Varidp : Idp);
      begin
	with Varidp^ do begin
	  if Llink <> nil then begin
	    RemapId(Llink);
	  end;
	  if Rlink <> nil then begin
	    RemapId(Rlink);
	  end;
	  if Klass = Vars then begin
	    if Vmty <> Smt then begin
	      Vblock := Fidp^.Pfmemblock;
	    end;
	    if Vmty = Mmt then begin
	      Vaddr := Moffset+Vaddr;
	    end;
	  end else if (Klass in [Proc, Func]) then begin
	    if Pfkind = Formal then begin
	      Pfblock := Fidp^.Pfmemblock;
	    end;
	  end;
	end {with};
      end {procedure RemapId};

    begin				(* remap			     *)
      if Localsbackwards then begin
	Memcnt[Mmt] := Rounddown(Memcnt[Mmt], SpAlign);
      end else begin
	Memcnt[Mmt] := Roundup(Memcnt[Mmt], SpAlign);
      end;

#if 0
      if Fidp <> nil then begin
	with Fidp^ do begin
	  (* if a function, remap the result.				     *)
	  if Klass = Func then begin
	    if Resmemtype = Fmt then begin
	      Resmemtype := Mmt;
	    end;
	  end;
	end {with};
      end;
#endif

      (***********************************************************************)
      (* calculate the offset of M memory				     *)
      (***********************************************************************)
#if 0
      Moffset := Memcnt[Fmt];
#endif
      Moffset := 0;
#if 0
      Memcnt[Mmt] := Memcnt[Fmt]+Memcnt[Mmt];
#endif

      if Display[Level].Fname <> nil then begin
	RemapId(Display[Level].Fname);
      end;

#if 0
      Memcnt[Fmt] := 0;
#endif
    end {procedure Remap};
#endif


  procedure Checksyms(Fidp : Idp);
  (* prints out warnings if symbols have not been used, and	             *)
  (* checks for undefined labels					     *)

    procedure Checkiduse (
		Fidp : Idp);

      (***********************************************************************)
      (* prints warning if identifiers have not been referenced also prints  *)
      (* warning if variables which are not actual parameters or files are   *)
      (* not assigned to, except for reference parameters, which should have *)
      (* been EITHER referenced OR assigned to, but not necessarily both     *)
      (***********************************************************************)

      var
	Lassigned : boolean;

      begin				(* Checkiduse			     *)
	if Fidp <> nil then begin
	  with Fidp^ do begin
	    if (Klass in [Vars, Konst, Proc, Func, Labels, Types]) then begin
	      Lassigned := true;
	      if (Klass = Vars) and (Idtype <> nil) then begin
		if (Idtype^.Form <> Files) then begin
		  Lassigned := Assignedto;
		end;
		if Isparam then begin
		  if (Vkind = Formal) then begin
		    if Referenced or Lassigned then begin
		      Lassigned := true;
		      Referenced := true;
		    end;
		  end else begin
		    Lassigned := true;
		  end;
		end;
	      end;
	      if not Referenced and not Lassigned then begin
#if 0
		Warningwithid(368, Idname);
#endif
    		writeln(err, 'upas: Warning: ', cppfilename:Fnln(cppfilename), 
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess35[18]);
		if Lptfile or Logfile then 
    		  writeln(List, 'upas: Warning: ', cppfilename:Fnln(cppfilename),
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess35[18]);
	      end else if not Referenced then begin
#if 0
		Warningwithid(175, Idname);
#endif
    		writeln(err, 'upas: Warning: ', cppfilename:Fnln(cppfilename), 
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess15[25]);
		if Lptfile or Logfile then 
    		  writeln(List, 'upas: Warning: ', cppfilename:Fnln(cppfilename),
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess15[25]);
	      end else if not Lassigned then begin
#if 0
		Warningwithid(176, Idname);
#endif
    		writeln(err, 'upas: Warning: ', cppfilename:Fnln(cppfilename), 
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess15[26]);
		if Lptfile or Logfile then 
    		  writeln(List, 'upas: Warning: ', cppfilename:Fnln(cppfilename),
			', ', Currname:Idln(Currname), ': ', 
			Idname:Idln(Idname), ': ', Errmess15[26]);
	      end;
	    end;
	  end {with};
	end;
      end {procedure Checkiduse};

    begin				(* Checksyms			     *)
      if Fidp <> nil then begin
	with Fidp^ do begin
	  Checksyms(Llink);
	  if (Klass = Labels) and not Defined then begin
	    Error(214);
	  end;
	  if Idwarning then begin
	    Checkiduse(Fidp);
	  end;
	  Checksyms(Rlink);
	end {with};
      end;
    end {procedure Checksyms};


(*Inittemps,Zerovars*)
  procedure Inittemps;
    (* Initializes temporary table. This must be called AFTER the	     *)
    (* declarations are processed.					     *)
    begin
      Tempcount := 0;
      Treetempcount := 0;
    end {procedure Inittemps};

  procedure Zerovars (
	      Filelist : Idp);
    (* Zeroes out the first two words of files (to mark them as "closed"),   *)
    (* as well as all of any records or arrays that contain holes or files.  *)
    (* A list of such variables is kept for each procedure. The variables    *)
    (* are zeroed at procedure entry if in M memory, or at the beginning of  *)
    (* runtime, if files and in S memory, or at load time, if not files and  *)
    (* in S memory. (This is so that files will be marked as "closed" when   *)
    (* the program is restarted but not reloaded.)			     *)
    var
      Lfileptr : Idp;
      offset, size : cardinal;
      looplabel: integer;
      tstamp: integer;
      tempattr: Attr;
    begin
      Lfileptr := Filelist;
      while Lfileptr <> nil do begin
	with Lfileptr^ do begin
	  if Vmty = Mmt then begin
	    if Idtype^.Stsize <= Wordsize * 16 then 
	      begin
	      offset := 0;
	      size := min(Idtype^.Align, Intsize);
	      while size > Idtype^.Stsize do size := size div 2;
	      repeat
	        U.Opc := Uldc;
	        U.Dtype := Ldt;
	        U.length := size;
	        U.Constval.Ival := 0;
	        Ubittobyte(U); Uwrite(U);
	        Uco5typaddr(Ustr, Ldt, Mmt, Vblock, Vaddr+offset, size);
	        offset := offset + size;
	      until offset >= Idtype^.Stsize;
	      end
	    else begin {generate a loop}
	      U.Opc := Ulda;
	      U.Mtype := Mmt;
	      U.I1 := Vblock;
	      U.Offset := Vaddr;
	      U.Length := Roundup(Idtype^.Stsize, Wordsize);
	      U.Offset2 := Vaddr;
	      Ubittobyte(U); Uwrite(U);
	      tstamp := 0;
	      Getatemp(tempattr, Addressptr, tstamp, true);
	      Uco1attr(Ustr, tempattr);
	      {loop head label}
	      Lastuclabel := Lastuclabel + 1;
	      looplabel := Lastuclabel;
	      Ucolab(looplabel, 0, 0);
	      {loop body}
	      Uco1attr(Ulod, tempattr);
	      Genexpr(stak^.tree);
	      Popstak;
	      U.Opc := Uldc;
	      U.Dtype := Ldt;
	      U.length := Intsize;
	      U.Constval.Ival := 0;
	      Ubittobyte(U); Uwrite(U);
	      Uco3int(Uistr, Ldt, Wordsize, 0);
	      {increment}
	      Uco1attr(Ulod, tempattr);
	      Uco2typint(Uinc, Adt, 4);
	      Genexpr(stak^.tree);
	      Popstak;
	      Uco1attr(Ustr, tempattr);
	      {termination test}
	      Uco1attr(Ulod, tempattr);
	      Ucolda(Mmt, Vblock, Vaddr + Roundup(Idtype^.Stsize, Wordsize), 
		     Roundup(Idtype^.Stsize, Wordsize), Vaddr);
	      Uco1type(Uequ, Adt);
	      Genexpr(stak^.tree);
	      Popstak;
	      Uco1int(Ufjp, looplabel);
	      Freetemps(tstamp);
	      end;
	  end;
	end {with};
	Lfileptr := Lfileptr^.Next;
      end {while};
    end {procedure Zerovars};

(*Body,Checkiduse,Checksyms*)
  procedure Body (
	      Fsys : Setofsys);
    (* parses the body of a procedure or the main block 		     *)
    var
      Loopdone : boolean;
      saved_current_block : Idp;

(*Enterbody,Leavebody*)
(************************************************************************)
(*									*)
(*	ENTERBODY and LEAVEBODY 					*)
(*									*)
(*	Generates, for each procedure or for the main block		*)
(*									*)
(*	   Initial ENT, PAR, and LEX instructions			*)
(*	   Final PLOD, DEF, RET and END instructions			*)
(*	   Code to initialize standard files (main block only)		*)
(*									*)
(*	Also generates warnings, on exit, if there are unused		*)
(*	   labels, constants, types, or variables			*)
(*									*)
(************************************************************************)
    procedure GenStdfileinit;
      (* generates call to standard file initializing procedure 	     *)
      var
	Parcount : integer;
	iob_symndx : integer;

#if 0
      procedure Finit (
	    f: Idp;
	    n: cardinal );
        begin
	  U.opc := Ulda;
	  U.Mtype := Smt;
	  U.Dtype := Hdt;
	  U.I1 := iob_symndx;
	  U.Offset := n*iob_size;
	  U.Offset2 := n*iob_size;
	  U.Length := iob_size;
	  Ubittobyte(U); Uwrite(U);
	  U.opc := Ustr;
	  U.Mtype := Smt;
	  U.Dtype := Hdt;
	  U.I1 := f^.Vblock;
	  U.Offset := 0;
	  U.Length := pointersize;
	  U.Lexlev := 0;
	  Ubittobyte(U); Uwrite(U);
        end {Finit};
#endif

      begin
#if 0
	Stdcallinit(Parcount);
	with Inputptr^ do begin
	  Ucolda(Vmty, Vblock, Vaddr, Idtype^.Stsize, Vaddr);
	end {with};
	Par(Adt, Parcount);
	with Outputptr^ do begin
	  Ucolda(Vmty, Vblock, Vaddr, Idtype^.Stsize, Vaddr);
	end {with};
	Par(Adt, Parcount);
	with Sysoutptr^ do begin
	  Ucolda(Vmty, Vblock, Vaddr, Idtype^.Stsize, Vaddr);
	end {with};
	Par(Adt, Parcount);
	Uco3intval(Uldc, Ldt, Intsize, ord(Opninput));
	Par(Ldt, Parcount);
	Uco3intval(Uldc, Ldt, Intsize, ord(Opnoutput));
	Par(Ldt, Parcount);
	Uco1idp(Ucup, Stdfileinitidp);
	Genexpr(stak^.tree);
	Popstak;
#else
#if 0
	iob_symndx := st_extadd(Symaddextstr("_iob"), 0, stGlobal, scNil, 0); 
	iob_symndx := st_idn_index_fext(iob_symndx, 1);
	if opninput then begin
	  Finit(Inputptr, 0);
	end;
	if opnoutput then begin
	  Finit(Outputptr, 1);
	end;
	Finit(Sysoutptr, 2);
#endif
#endif
      end {procedure GenStdfileinit};

    procedure GenPdefs (
		Fidp : Idp);
      (* generates Pdefs for a procedure				     *)
      begin
	while Fidp <> nil do begin
	  with Fidp^ do begin
	    if Klass in [Proc, Func] then begin
	      Uco5typaddr(Updef, Hdt, Pmt, Pfblock, Pfaddr, Wordsize);
	      Uco5typaddr(Updef, Fdt, Pmt, Pfblock, Pfaddr+Wordsize, Wordsize);
	    end else if Vkind = Formal then begin
	      Uco5typaddr(Updef, Adt, Pmt, Vblock, Vaddr, Pointersize);
	    end else if Idtype = nil then begin
	      return
	    end else if ((Idtype^.Stdtype = Mdt)
			 and ((Idtype^.Stsize > Wordsize) or (Idtype^.Stsize > Idtype^.Align)))
		or (Idtype^.Stsize > Parthreshold) then begin
#if 0
	      Uco5typaddr(Updef, Adt, Pmt, Vblock, Vindaddr, Pointersize);
#endif
	      Uco5typaddr(Updef, Mdt, Pmt, Vblock, bitand(Vaddr, 16#ffffffe0), 
			  max(Wordsize, Idtype^.Stsize));
	    end else begin		(* vkind = actual		     *)
	      Uco1idp(Updef, Fidp);
	    end;
	    Fidp := Next;
	  end {with};
	end {while};
      end {procedure GenPdefs};

    procedure Enterbody;
      (* Generates the startup code for a body, i.e. ENT, PDEFs, SYMs; also  *)
      (* jumps to scalar table loading code for main block		     *)
      var
	I : integer;
	Lidp : Idp;

      begin
	saved_current_block := current_block;
	if Fprocp <> Progidp then begin	(* entering body of a procedure or   *)
					(* function			     *)
	  current_block := Fprocp;
	  if fileNumber <> mainfileNumber then
	    Error(469);
	  Ucoloc(Fprocp^.lineno, fileNumber);
	  Uco1idp(Uent, Fprocp);
	  Ucoid(Fprocp^.Idname);
	  if Progidp <> nil then
	    for I := Level-1 downto 2 do 
	      Uco2intint(Ulex, I, Display[I+1].Mblock)
	  else for I := Level-1 downto 2 do 
	      Uco2intint(Ulex, I, Display[I].Mblock);
	  GenPdefs(Fprocp^.Next);
	  if debugging_symbols then 
	    Uco1int(Ubgnb, bgnbno);
	  (* store static link passed					     *)
	  if (Level > 2) or (Level = 2) and (Progidp <> nil) then begin
	    Uco5typaddr(Ulod, Adt, Rmt, 0, intRmtoffset, 32);
	    Genexpr(stak^.tree);
	    Popstak;
	    Uco5typaddr(Ustr, Adt, Mmt, Fprocp^.Pfmemblock, static_link_loc, 32);
	  end;
	  if Fprocp^.Filelist <> nil then 
	    Zerovars(Fprocp^.Filelist);
#if 0
	  Lidp := Fprocp^.Next;
	  while Lidp <> nil do begin	(* generate Movs for large	     *)
					(* parameters			     *)
	    if Lidp^.Idtype <> nil then begin
	      with Lidp^, Idtype^ do begin
		if (Vkind = Actual)
		 and (((Stdtype = Mdt)
		       and ((Stsize > Wordsize) or (Stsize > Align)))
		      or (Stsize > Parthreshold)) then begin
		  Ucolda(Vmty, Vblock, Vaddr, Stsize, Vaddr);
		  Genexpr(stak^.tree);
		  Popstak;
		  Uco5typaddr(Ulod, Adt, Vindtype, Vblock, Vindaddr,
		      Pointersize);
		  Genexpr(stak^.tree);
		  Popstak;
		  Uco2intint(Umov, Align, Stsize);
		end;
	      end {with};
	    end {then};
	    Lidp := Lidp^.Next;
	  end {while};
#endif
	end else begin			(* entering the main program   *)
	  current_block := Progidp;
	  if fileNumber <> mainfileNumber then
	    Error(469);
	  Ucoloc(Progidp^.proglineno, fileNumber);
	  Uco1idp(Uent, Progidp);
	  Ucoid(Progidp^.Idname);
	  if debugging_symbols then 
	    Uco1int(Ubgnb, bgnbno);
	  GenStdfileinit;
	  if Progidp^.Progfilelist <> nil then begin
	    Zerovars(Progidp^.Progfilelist);
	  end;
	end;
      end {procedure Enterbody};


    procedure Leavebody;

      (***********************************************************************)
      (* finishes code for a body, i.e. PLOD,DEFs,RET,END;		     *)
      (***********************************************************************)
      var
	Lmty : Memtype;
	retregoffset: integer;

      begin				(* leavebody			     *)
#if 0
	for Lmty := Pmt to Mmt do begin
	  if not Localsbackwards or (Lmty <> Mmt) then begin
	    Memcnt[Lmty] := Roundup(Memcnt[Lmty], SpAlign);
	  end else begin
	    Memcnt[Lmty] := Rounddown(Memcnt[Lmty], SpAlign);
	  end;
	end {for};
#endif
	PmtMemcnt := Roundup(PmtMemcnt, SpAlign);
	MmtMemcnt := Rounddown(MmtMemcnt, SpAlign);
	if fileNumber = mainfileNumber then
	  Ucoloc(Linecnt, fileNumber);
	if Fprocp = Progidp then begin	(* i.e. leaving main body     *)
	  Uco3intval(Uldc, Jdt, Intsize, 0);
	  Genexpr(stak^.tree);
	  Popstak;
	  Uco5typaddr(Ustr, Jdt, Rmt, 0, intRmtoffset, Intsize);
	  Uco0(Uret);
#if 0
	  for Lmty := Mmt to Pmt do begin
	    if Lmty <> Smt then begin
	      if Memcnt[Lmty] <> 0 then begin
		Ucodef(Lmty, abs(Memcnt[Lmty]));
	      end;
	    end;
	  end {for};
#endif
	  Ucodef(Mmt, abs(MmtMemcnt));
	  if debugging_symbols then begin
	    Uco1int(Uendb, st_blockend(0));
	    end;
	  Uco1idp(Uend, Progidp);
	end else begin			(* fprocp <> nil <=> leaving a	     *)
					(* procedure or function	     *)
	  if Fprocp^.Klass = Func then begin
	    if Fprocp^.Idtype = nil then return;
	    Uco5typaddr(Ulod, Fprocp^.Idtype^.Stdtype, Fprocp^.Resmemtype,
		Fprocp^.Pfmemblock, Fprocp^.Resaddr, Fprocp^.Idtype^.Stsize);
	    Genexpr(stak^.tree);
	    Popstak;
	    if Fprocp^.Idtype^.Stdtype in [Qdt, Rdt] then
	      retregoffset := fpRmtoffset
	    else retregoffset := intRmtoffset;
	    Uco5typaddr(Ustr, Fprocp^.Idtype^.Stdtype, Rmt, 0, retregoffset,
		Fprocp^.Idtype^.Stsize);
	  end;
	  Uco0(Uret);
#if 0
	  for Lmty := Mmt to Pmt do begin
	    if Memcnt[Lmty] <> 0 then begin
	      Ucodef(Lmty, abs(Memcnt[Lmty]));
	    end;
	  end {for};
#endif
	  Ucodef(Mmt, abs(MmtMemcnt));
	  Ucodef(Pmt, abs(PmtMemcnt));
	  if debugging_symbols then
	    Uco1int(Uendb, st_blockend(0));
	  Uco1idp(Uend, Fprocp);
	end;
	current_block := saved_current_block;
      end {procedure Leavebody};


      (***********************************************************************)
      (* BODY -- processes all the statements in a block		     *)
      (***********************************************************************)

    begin				(* body 			     *)

      Enterbody;			(* start-up code		     *)
      Loopdone := false;
      repeat				(* parse all the statements	     *)
	repeat
	  Statement(Fsys+[Semicolonsy, Endsy], [Semicolonsy, Endsy]);
	until not (Sy in Statbegsys);
	Loopdone := Sy <> Semicolonsy;
	if not Loopdone then begin
	  Insymbol;
	end;
      until Loopdone;
      if Sy = Endsy then begin
	Insymbol;
      end else begin
	Error(163);
      end;
      if Progidp <> nil then
        Checksyms(Display[Level+1].Fname)	(* check for use *)
      else Checksyms(Display[Level].Fname);	(* check for use *)
      Leavebody;			(* end-up code			     *)
    end {procedure Body};

    (*************************************************************************)
    (* BLOCK -- parses the block that forms a program or a		     *)
    (* procedure/function Argument: FPROCP, which is NIL if the block is a   *)
    (* program; otherwise, it is an Identifier record that describes the     *)
    (* procedure/function Marks the heap. After it has processed the whole   *)
    (* block, reclaims all the storage allocated during the block, UNLESS an *)
    (* enumerated type is used in a read/write statement, in which case the  *)
    (* record describing that scalar must stay around until the end of the   *)
    (* program, when procedure TABLEGEN is generated. Processes label,	     *)
    (* const, and var declarations. Remaps storage, (see procedure Remap).   *)
    (* Processes procedure/function declarations. Calls Body to process the  *)
    (* statements in the block. 					     *)
    (*************************************************************************)

  begin 				(* block			     *)
#ifdef HEDRICKPASCAL
    Remapped := (Level = 1);		(* no need to remap level 1	     *)
#endif
    (* if not in the outermost block, start a new heap *)
    if Fprocp <> nil then begin
      GMark := alloc_mark(GHeap);
    end;

    if debugging_symbols and (Fprocp <> nil) then begin
      bgnbno := st_blockbegin(0, 0, scText);
      if bgnbno = 0 then
        bgnbno := st_textblock;
      {the correspondind blockend is called in Leavebody, to be before the
       call to st_procend}
      end;
    Forwardprocedures := nil;
    repeat (* outer loop is for recovering in case of error and continuing
	      the parse *)
      if not (Sy in Blockbegsys) then 
	goto 11;
      repeat
	case Sy of
	Labelsy : 
	  if Fprocp = nil then begin
	    Error(468);
	    Insymbol;
	    Skipiferr(Blockbegsys, 201, Fsys);
	  end else begin
	    Insymbol;
	    Labeldeclaration(Fsys);
	  end {case Labelsy};
	Constsy : begin
	    Insymbol;
	    Constantdeclaration(Fsys);
	  end {case Constsy};
	Typesy : begin
	    Insymbol;
	    Typedeclaration(Fsys);
	  end {case Typesy};
	Varsy : begin
	    Insymbol;
	    Variabledeclaration(Fprocp, Fsys);
	  end {case Varsy};
	Proceduresy, Functionsy : begin
#if 0
	    if not InIncludefile and not Remapped then begin
	      Remap(Fprocp);
	      Remapped := true;
	    end;
#endif
	    Lsy := Sy;
	    Insymbol;
	    Proceduredeclaration(Fsys, Forwardprocedures, Lsy = Proceduresy);
	  end {case Proceduresy};
	otherwise: ;
	end {case};
      until not (Sy in Blockbegsys-[Beginsy]);

      (*********************************************************************)
      (* check non-solved forward declarations				
      (*********************************************************************)
      while Forwardprocedures <> nil do begin
	with Forwardprocedures^ do begin
	  if Forwdecl then begin
	    Errorwithid(465, Idname);
	  end;
	  Forwardprocedures := Testfwdptr;
	end {with};
      end {while};

      if Fprocp <> nil then begin
        Skipiferr([Beginsy], 201, Fsys-[Programsy]);
	if verbose then begin
	  write(err, Fprocp^.Idname : Idln(Fprocp^.Idname), ' ');
	  flush(err);
	  Needsaneoln := true;
        end;
	Inittemps;
	if Sy = Beginsy then begin
	  Insymbol;
	end else begin
	  Error(201);
	end;
	Body(Fsys+[Casesy]);
        Skipiferr(Leaveblocksys, 166, Fsys);
      end else begin {not inside procedure or program}
#if 0
        Checksyms(Display[Level+1].Fname);	(* check for use *)
	Globalmemcnt := Memcnt;         (* save where LoadTableAddress can   *)
					(* get at it			     *)
#endif
      if Sy = Beginsy then begin
	Error(316);
	Insymbol;
      end;
      end;
    until Sy in (Leaveblocksys);

    (* if not in the outermost block, deallocate memory *)
11: if Fprocp <> nil then begin
      alloc_release(GHeap, GMark);
      stakbot^.prev := nil;
      stak := stakbot;
    end;
  end {procedure Block};

(*Progparams,Progrm,Pascal*)
(**********************************************************************)
(*								      *)
(*	PROGPARAMS						      *)
(*								      *)
(*	Global variables affected: Opninput, Opnoutput		      *)
(*								      *)
(*	Parses program paratmeters (file names), checking for	      *)
(*		duplications.					      *)
(*	If INPUT or OUTPUT are in the list, records the fact that     *)
(*		they need to be opened automatically.		      *)
(*	Returns a linked list of Programparameter records, which is   *)
(*		not used further currently			      *)
(*								      *)
(**********************************************************************)
procedure Setupstdfiles;
  var
    storclass : integer;
  begin
    (* initialize file buffers for INPUT and OUTPUT and add to file list     *)
    Inputptr^.Vaddr := 0;
    Outputptr^.Vaddr := 0;
    Sysoutptr^.Vaddr := 0;

    {-------------------------------------------------------------------------}
    { Put these into the symbol table					      }
    {-------------------------------------------------------------------------}
    Inputptr^.Vblock := st_extadd(Symaddextstr(Inputptr^.Idname), 0, stGlobal, 
				  scNil, indexNil); 
    Inputptr^.Vblock := st_idn_index_fext(Inputptr^.Vblock, 1);
    Outputptr^.Vblock := st_extadd(Symaddextstr(Outputptr^.Idname), 0, stGlobal,
				  scNil, indexNil); 
    Outputptr^.Vblock := st_idn_index_fext(Outputptr^.Vblock, 1);     
    Sysoutptr^.Vblock := st_extadd(Symaddextstr(Sysoutptr^.Idname), 0, stGlobal,
				  scNil, indexNil); 
    Sysoutptr^.Vblock := st_idn_index_fext(Sysoutptr^.Vblock, 1);     
    Argcptr^.Vblock := st_extadd(Symaddextstr('__Argc'), 0, stGlobal,
				  scNil, indexNil); 
    Argcptr^.Vblock := st_idn_index_fext(Argcptr^.Vblock, 1);     

#if 0
      Inputptr^.Vaddr := Assignnextmemoryloc(Smt, Textptr^.Stsize, Textptr^.Align);
      Outputptr^.Vaddr := Assignnextmemoryloc(Smt, Textptr^.Stsize, Textptr^.Align);
      Sysoutptr^.Vaddr := Assignnextmemoryloc(Smt, Textptr^.Stsize, Textptr^.Align);
#endif
  end {Setupstdfiles};

procedure Initstdfiles;
  begin
    if Progidp <> nil then
      Progidp^.Progfilelist := nil;
    Ucosym(Uesym, Inputptr^.Vblock,  0, Filesize div Addrunit);
    Ucosym(Uesym, Outputptr^.Vblock, 0, Filesize div Addrunit);
    Ucosym(Uesym, Sysoutptr^.Vblock, 0, Filesize div Addrunit);
  end {procedure Initstdfiles};

function Progparams
   : Parp;
  var
    Listhead, Listtail, Lparp : Parp;
    Errflag : boolean;

  begin
    Listhead := nil;
    Opninput := false;
    Opnoutput := false;
    repeat				(* loop picking up names and commas  *)
      Insymbol;
      if Sy <> Identsy then begin
	Error(209);
      end else begin
	if Id = 'input           ' then begin
	  Opninput := true;
	end else if Id = 'output          ' then begin
	  Opnoutput := true;
	end;
	Insymbol;
	(* check to make sure file has not already been declared	     *)
	Lparp := Listhead;
	Errflag := false;
	while Lparp <> nil do begin
	  if Lparp^.Fileid = Id then begin
	    Error(466);
	    Lparp := nil;
	    Errflag := true;
	  end else begin
	    Lparp := Lparp^.Nextparp;
	  end;
	end {while};
	if not Errflag then begin
	  new1(Lparp);			(* create and hang its descriptor    *)
	  with Lparp^ do begin
	    Fileid := Id;
	    Nextparp := nil;
	    if Listhead = nil then begin
	      Listhead := Lparp;
	      Listtail := Lparp;
	    end else begin
	      Listtail^.Nextparp := Lparp;
	      Listtail := Lparp;
	    end;
	  end {with};
	end;
	if Sy = Mulsy then begin
	  Insymbol;
	end;				(* for DEC-10 compatibility	     *)
      end;
    until Sy <> Commasy;
    if Sy <> Rparentsy then begin
      Warning(152);			(* parenthesis after parameters      *)
    end else begin
      Insymbol;
    end;
    Progparams := Listhead;
  end {function Progparams};

  (***************************************************************************)
  (* PROGRM -- compiles one Pascal program Initializes program descriptor    *)
  (* (Progidp^) Assigns memory for files INPUT and OUTPUT Calls Progparams   *)
  (* to get program parameters. Calls Block to compile the program.	     *)
  (***************************************************************************)

procedure Progrm;
  (* compiles one program or module					     *)

  var
    Lid: Identname;		(* external name for data area	     *)
    I, datandx : integer;
    junk, isym, iaux : integer;

  begin 				(* Progrm			     *)

    new2(Progidp, Progname);		(* build a program name descriptor   *)
    with Progidp^ do begin
      Klass := Progname;
      Proglev := 1;
#if 0
      Progmemblock := 1;
#endif
      Progparnumber := 0;
      Progparamptr := nil;
    end {with};

    (*************************************************************************)
    (* parse the program statement					     *)
    (*************************************************************************)
#if 0
    Ismodule := (Sy = Modulesy);
    if (Sy <> Programsy) and (Sy <> Modulesy) then begin
      Currname := 'MAIN BLOCK      ';
      Progidp^.Idname := '???             ';
      Errandskip(318, Blockbegsys);
    end else begin			(* Sy = Programsy or Modulesy	     *)
#endif
      Insymbol; 			(* program name 		     *)
      if Sy <> Identsy then begin
	Errandskip(209, Blockbegsys);
      end else begin
	Currname := Id;
	with Progidp^ do begin
	  Idname := "main";
	  Entname := "main";
	  iaux := st_auxadd(-1);
	  Progisym := st_symadd(Symaddstr(Entname), 0, stProc, scText, iaux);
	  symndx := st_extadd(Symaddextstr(Entname), 0, stProc, scText, 
		Progisym); 
	  symndx := st_idn_index_fext(symndx, 1);
	  Progmemblock := symndx;
	  junk := st_auxbtadd(btNil); {for type of function}
	  Display[2].Mblock := symndx;
	  Memblock := symndx;
	  Proglineno := Linecnt;
	end {with};

	Insymbol;
	if Sy = Lparentsy then begin
	  (* there should be an error message here for modules parse the     *)
	  (* program parameters 					     *)
	  Progidp^.Progparamptr := Progparams;
	end;
	Skipiferr([Semicolonsy], 156, Blockbegsys);
      end;
#if 0
    end;
#endif

    if Sy <> Eofsy then begin
      Insymbol;
    end;


    (*************************************************************************)
    (* allocate memory for INPUT and OUTPUT				     *)
    (*************************************************************************)
    Initstdfiles;

    (*************************************************************************)
    (* compile the program block					     *)
    (*************************************************************************)
    (* allocate the space for code generator in the stack frame *)
#if 0
    I := Assignnextmemoryloc(Mmt, Pointersize, Pointeralign);
    I := Assignnextmemoryloc(Mmt, Pointersize, Pointeralign);
#endif
    Block(Progidp, Blockbegsys+Statbegsys-[Casesy], [Periodsy, Eofsy]);

    if Sy = Eofsy then begin
      Errorwithid(267, '                ');
    end else begin
      Insymbol;
    end;

#if 0
    Ucooptn('TTYPES          ', Lastmarker);
#endif

  end {procedure Progrm};

  (***************************************************************************)
  (* MAIN BLOCK -- processes a file of Pascal code containing one or more    *)
  (* programs Initializes files. Outputs headers for listing. General	     *)
  (* initialization. Gets first symbol of the file. Calls initializing	     *)
  (* procedures to set up predeclared identifiers Calls Progrm to compile    *)
  (* the program Prints statistics.					     *)
  (***************************************************************************)
program Pascalcompiler(input);

var
  Cputime, i : integer;			(* to report elapsed time	     *)
  builtin_filename : filename;
  builtins, junk: integer;
  dataname: identname;
begin					(* Pascal main			     *)

  Initialize;
  Syminit;

  Processargs; (* process command line *)

  if verbose then begin
    write(err, Shortheader, ': ');
    Needsaneoln := true;
  end;

  Cputime := Getclock;			(* time coordinates		     *)
  if Lptfile or Logfile then begin	(* write header for list file	     *)
    write(List, Header, '     LISTING PRODUCED ON ');
    PrintDate(List);
    write(List, ' AT ');
    PrintTime(List);
    writeln(List);
    writeln(List);
  end;

  if Eof(input) then begin
    writeln(err);
    write(err, 'upas: Source file does not exist: ');
    i := 1;
    while Sourcename[i] <> ' ' do begin
      write(err, Sourcename[i]);
      i := i + 1;
      end {while};
    writeln(err);
    flush(err);
    Abort; {file does not exist}
    end;
  Newfile(input);			(* get first symbol of new file; may *)
					(* include options		     *)
#if 0
  with Commandline do begin
    for Sw := 1 to Switchctr do begin
      Setswitch(Switches[Sw], Switchvals[Sw]);
    end {for};
  end {with};
(* Lock the switches that should not be changed after the beginning of the
   program. *)
  Setswitch('!               ', 1);
#endif
  Resetpossible := false;		(* some options can't be reset       *)
					(* hereafter			     *)

  Level := 0;
  Top := 0;				(* clear symbol table at level 0     *)
  with Display[0] do begin
    Fname := nil;
    Occur := Blck;
    Mblock := 0;
  end {with};

(* enter standard names and types *)
  Filenameassign(builtin_filename, 'pascal-builtins.p');
  Addnullfilename(builtin_filename);
  builtins := st_filebegin(st_str, langPascal, 1, gleveltab[glevel]);
  Enterstdtypes;
  Enterstdnames;
  Enterundecl;
  Enterstdprocs;
  Initruntimes;
  Popbtmap;

  {if cpp is not used, then getnextline called from Newfile would not have
   called st_filebegin because there is no # in first line}
  Addnullfilename(cppfilename);
  fileNumber := st_filebegin(st_str, langPascal, 1, gleveltab[glevel]);
  if veryfirstfile then begin {cpp not used}
    mainfileNumber := fileNumber;
    if lsb_first then
      Uco1int(Ubgn, LITTLEENDIAN)
    else Uco1int(Ubgn, BIGENDIAN);
    Ucooptn(UCO_SOURCE, 1);(* source language is Pascal	     *)
    Ucofname(cppfilename);
    veryfirstfile := false;
    end;

  (* clear symbol table at level 1     *)
  with Display[1] do begin
    Fname := nil;
    Occur := Blck;
    Mblock := 1;
  end {with};

  Progidp := nil;	(* when nil, indicates before program statement *)

  (* create generic static block for compiler-generated static locations *)
  Dataname := '$dat';
  Display[0].Mblock := st_idn_index_fext(
	    st_symadd(Symaddstr(Dataname), 0, stStatic, scData, indexNil), 0);
  Ucosym(Ulsym, Display[0].Mblock, 3, 0);

  (* initialize addresses for the 3 io files *)
  Setupstdfiles;

  Top := 1;
  Level := 1;
  Skipiferr(Blockbegsys+[Programsy], 318, [Periodsy, Eofsy]);
  Block(nil, Blockbegsys+Statbegsys+[Programsy]-[Casesy], 
	[Periodsy, Eofsy, Programsy, Beginsy]);
  if Sy = Programsy then begin
    Top := 2;
    (* clear symbol table at level 2     *)
    with Display[2] do begin
      Fname := nil;
      Occur := Blck;
#if 0
      Mblock := 1;
#endif
    end {with};
    Progrm;
    end
  else if not (Sy in [Periodsy, Eofsy, Semicolonsy]) then
    Error(327)
  else Initstdfiles; (* generate esym's for standard i/o files *)

  SmtMemcnt := Roundup(SmtMemcnt, SpAlign);
  Uco2intint(Usdef, Display[0].Mblock, max(SmtMemcnt, wordsize));

  FinishLine;
  Uco1int(Ustp, 0);
  Popbtmap;
  st_endallfiles;
  uputclose; (* terminate the ucode output file *)
  if stdump then begin
    st_dump(0, -1);
  end;
  Addnullfilename(symname);
  st_writebinary(st_str, -1);

(* print final statistics *)
  Cputime := (Getclock-Cputime);

  if Lptfile or Logfile then begin
    writeln(List);
    if Errorcount = 1 then begin
      writeln(List, 'Only 1 error detected.');
    end else begin
      writeln(List, Errorcount : 1, ' errors detected.');
    end;
    writeln(List, Tlinecnt : 1, ' lines compiled in ', Cputime/1000 : 1 : 2,
	' seconds.');
  end;
  if Needsaneoln then begin
    writeln(err);
  end;
  if Errorcount > 0 then begin
    if Errorcount = 1 then begin
      writeln(err, '1 error detected.  ');
    end else begin
      writeln(err, Errorcount : 1, ' errors detected.  ');
    end;
  end;
  flush(err);
  if Errorcount > 0 then begin
    Abort;
  end;
end.
