{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasuco.p,v 1030.7 88/02/18 14:55:08 bettina Exp $ }

#include "stamp.h"
#include "upasglob.h"
#include "cmplrs/uwri.h"
#include "upasutil.h"
#include "upastree.h"
#include "upaslex.h"
#include "upassym.h"
#include "upasuco.h"
#include "allocator.h"




(*****************************************************************************)
(*									     *)
(*	UCODE WRITING MODULE						     *)
(*									     *)
(* U-code is a stack-based intermediate language.  It comes in two forms: a  *)
(* text representation, and a binary representation (B-code).  This module   *)
(* contains routines for writing both U-code and B-code.		     *)
(*									     *)
(* Each instruction, whether in U-code or B-code form, is passed in the      *)
(* form of a B-code record, called U. To find out where each value of	     *)
(* an instruction is in the record, you should look at the the operand	     *)
(* initialization code in INITUWRITE (this initializes the operand table,    *)
(* which describes the type and order of the operands for each U-code	     *)
(* instruction).  For example, the ISTR instruction has operands SDTYPE,     *)
(* SOFFSET, and SLENGTH, and the three operands for the instruction would    *)
(* be found in U.DTYPE, U.OFFSET, and U.LENGTH. 			     *)
(*									     *)
(*  Some exceptions:							     *)
(*     SPNAME0 and SPNAME1 are both stored in U.PNAME.	The 0 and 1 indicate *)
(*	 whether then name should appear before or after the Opcode.	     *)
(*	 Similarly, SVNAME0 and SVNAME1 are stored in U.VNAME.		     *)
(*     SLABEL0, SLABEL1, and SBLOCKNO  are all stored in U.I1.		     *)
(*     For SCOMMENT, the comment is stored as a string constant in	     *)
(*     U.CONSTVAL.							     *)
(*									     *)
(* Since a B-code record is variable in length, depending on the,	     *)
(* instruction it is alternately represented as an array of integers.  This  *)
(* representation is used when reading or writing to a file.  A routine is   *)
(* provided to calculate the length of each instruction.  Since instructions *)
(* which include a constant, such as LDC, may have different lengths,	     *)
(* depending on the constant, the length of the constant must be added to    *)
(* the length of the record being read or written for those instructions.    *)
(*****************************************************************************)
procedure Uco0 (* Fop : Uopcode *);
  (* chkf,chkt,chkn,ret,dsp,vmov					     *)
  begin
    U.Opc := Fop;
    U.Lexlev := 0;	{no overflow check}
    if (Fop = Uret) or (Fop = Uchkt) then begin
      Ubittobyte(U); Uwrite(U);
    end else begin
      Unarynode;
    end;
  end {procedure Uco0};

procedure Uco1type (* Fop : Uopcode; Fdty : Datatype *);
  (* abs, add, and, div, equ, geq, grt, ior, leq, les, lnot, min, max, mod,  *)
  (* mpy, mus, neg, neq, not, odd, sqr, sub, xor			     *)
  begin
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.Lexlev := 0;	{no overflow check}
    if Fop in [Uabs, Uneg, Ulnot, Unot, Uodd, Usqr] then begin
      Unarynode;
    end else begin
      Binarynode;
    end;
  end {procedure Uco1type};

procedure Uco1int (* Fop : Uopcode; Fint : integer *);
  (* fjp, mst, tjp, ujp, new, stp, bgn, bgnb, endb	     *)
  begin
    U.Opc := Fop;
    if Fop = Umst then begin
      U.Lexlev := Fint;
    end else begin
      U.I1 := Fint;
      if Fop = Ubgn then begin
	U.length := MS_STAMP;
	U.offset := LS_STAMP;
      end;
    end;
    if Fop <> Umst then begin
      Ubittobyte(U); Uwrite(U);
    end else begin
      Leafnode;
    end;
  end {procedure Uco1int};

procedure UcoProcpointer (* Fidp: Idp *);
  begin
  U.Opc := Uldc;
  U.Dtype := Fdt;
  U.length := Wordsize;
  U.Constval.ival := Fidp^.Pfmemblock;
  Leafnode;
  end {UcoProcpointer};

procedure Uco1idp (* Fop : Uopcode; Fidp : Idp *);
  (* cup, ent, icuf, ldp, pdef and lca, when it loads identifier *)
  (* names (specifically for names of declared scalars, for i/o routines;    *)

  var
    I : 1..Identlength;

  begin
    U.Opc := Fop;
    if (Fidp <> nil) then begin
      with U, Fidp^ do begin
	case Fop of
	Uend : begin
	    I1 := st_procend(symndx);
#if 0
	    if Klass = Progname then begin
	      Pname = Entname;
	    end else begin
	      Pname := Externalname;
	    end;
#endif
	  end {case Uend};
	Ucup, Uent, Uicuf : begin
	    Push := 0;
	    Dtype := Pdt;
	    if Klass = Func then begin
	      if Idtype <> nil then begin
		with Idtype^ do begin
		  if (Stsize <= Parthreshold) and (Stdtype <> Mdt) then begin
		    Push := 1;
		    Dtype := Stdtype;
		  end;
		end {with};
	      end;
	    end;
	    case Fop of
	    Uent : begin
		if Klass = Progname then begin
		  { Pname := Entname;					      }
		  Lexlev := Proglev;
		  I1 := { Progmemblock	}symndx;
		  Pop := Progparnumber;
		  Extrnal := 1;
		  st_pdadd(Progisym);
		end else begin
		  { Pname := Externalname;				      }
		  Lexlev := Pflev;
		  I1 := Pfmemblock;
		  Pop := Parnumber;
		  Extrnal := ord(Externproc);
		  st_pdadd(Internsymndx);
		end;
		if useframeptr then
		  SET_FRAMEPTR_ATTR(Extrnal);
	      end {case Uent};
	    Ucup : begin
		Lexlev := Pflev;
		I1 := symndx;
		{ Pname := Externalname;				      }
		Pop := Parnumber;
		Extrnal := 0;
	      end {case Ucup};
	    Uicuf : begin
		Pop := Parnumber;
		{ Extrnal := 1; }
	      end {case Uicuf};
	    end {case};
	  end {case Ucup};
	Updef : begin
	    Dtype := Idtype^.Stdtype;
	    Mtype := Vmty;
	    I1 := Vblock;
	    offset := bitand(Vaddr, 16#ffffffe0); 
	    length := max(Idtype^.Stsize, Wordsize);
	    lexlev := IN_MODE;
	  end {case Updef};
	Uldp : begin
	    Lexlev := Pflev;
	    I1 := Pfmemblock;
	    { Pname := Externalname;					      }
	  end {case Uldp};
	Ulca : begin
	    Dtype := Mdt;
	    length := Stringsize(Identlength);
	    I1 := 0;
	    new1(Constval.Chars);
	    for I := 1 to Identlength do begin
	      Constval.Chars^.ss[I] := Idname[I];
	    end {for};
	    Constval.Ival := Identlength;
	  end {case Ulca};
	end {case};
      end {with};
    end;
    if Fop in [Uend, Uent, Updef] then begin
      Ubittobyte(U); Uwrite(U);
    end else if Fop = Ucup then begin
      Unarynode;
    end else if Fop = Uicuf then begin
      Binarynode;
    end else begin
      Leafnode;
    end;				(* ldp, lca			     *)
  end {procedure Uco1idp};

procedure Ucoinit (* Fdty : Datatype; Fblock : integer;
	Foffset, Foffset2 : Addrrange;
	Flength : Sizerange; Fval : Valu *);
  begin
    U.Opc := Uinit;
    U.Dtype := Fdty;
    U.Mtype := Smt;
    U.I1 := Fblock;
    U.offset := Foffset;
    U.Offset2 := Foffset2;
    U.length := Flength;
    U.aryoff := 0;
    U.Initval := Fval;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucoinit};

procedure Uco2typtyp (* Fop : Uopcode; Fdty1, Fdty2 : Datatype *);
  (* cvt, cvt2, swp, rnd						     *)
  begin
    U.Opc := Fop;
    U.Dtype := Fdty1;
    U.Dtype2 := Fdty2;
    U.Lexlev := 0;	{no overflow check}
    if Fop = Uswp then begin
      Ubittobyte(U); Uwrite(U);
    end else begin
      Unarynode;
    end;
  end {procedure Uco2typtyp};

procedure Uco1attr (* Fop : Uopcode; Fattr : Attr *);
  (* generates the ucode instructions with addressing parameters, described  *)
  (* in an attr record: ldc, lca, ilod, isld, isst, istr, lda, lod, nstr,    *)
  (* str and ilda							     *)
  begin 				(* uco1attr			     *)
    with Fattr, U do begin
      Opc := Fop;
      case Fop of
      Uldc, Ulca : begin
	  Dtype := Adtype;
	  length := Asize;
	  Constval := Cval;
	  U.I1 := 0;
	end {case Uldc};
      Ulda, Uilda : begin
	  Mtype := Amty;
	  I1 := Ablock;
	  offset := Dplmt;
	  length := Asize;
	  Offset2 := Baseaddress;
	end {case Ulda};
      Uilod, Uistr : begin
	  Dtype := Adtype;
	  Mtype := Amty;
	  I1 := Dplmt;
	  length := Asize;
	  lexlev := 0;
	end {case Uilod};
      Ulod, Uisld, Uisst, Ustr : begin
	  Dtype := Adtype;
	  I1 := Ablock;
	  offset := Dplmt;
	  Mtype := Amty;
	  length := Asize;
	  lexlev := 0;
	end {case Ulod};
      end {case};
    end {with};
    if Fop in [Uistr, Uisst, Unstr, Ustr] then begin
      Ubittobyte(U); Uwrite(U);
    end else if Fop in [Uilod, Uisld, Uilda] then begin
      Unarynode;
    end else begin
      Leafnode;
    end;
  end {procedure Uco1attr};

procedure Uco2typint (* Fop : Uopcode; Fdty : Datatype; Fint : integer *);
  (* chkh, chkl, dec, dif, inc, iequ, igeq, igrt, ileq, iles, ineq, int,     *)
  (* ixa, sgs, uni 						     *)
  begin 				(* uco2typint			     *)
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.Lexlev := 0;	{no overflow check}
    if Fop in [Uixa, Uchkl, Uchkh, Uinc, Udec] then
      U.I1 := Fint
    else U.length := Fint;
    if Fop in [Uchkh, Uchkl, Udec, Uinc, Usgs] then begin
      Unarynode;
    end else begin
      Binarynode;
    end;
  end {procedure Uco2typint};

procedure Uco2intint (* Fop : Uopcode; Fint1, Fint2 : integer *);
  (* mov, clab, goob, lex *)
  begin
    U.Opc := Fop;
    with U do begin
      case Fop of
      Uclab, Usdef: begin
	  I1 := Fint1;
	  length := Fint2;
	end {case Uclab};
      Umov, Uiequ, Uigrt, Uigeq, Uileq, Uiles, Uineq : begin
	  Dtype := Mdt;
	  I1 := Fint1;
	  length := Fint2;
	  lexlev := 0;
	end {case Umov};
      Ugoob : begin
	  I1 := Fint1;
	  Lexlev := Fint2;
	end {case Ugoob};
      Ulex : begin
	  Lexlev := Fint1;
	  I1 := Fint2;
	end {case Ulex};
      end {case};
    end {with};
    if Fop in [Uiequ, Uigrt, Uigeq, Uileq, Uiles, Uineq] then begin
      Binarynode;
    end else begin
      Ubittobyte(U); Uwrite(U);
    end;
  end {procedure Uco2intint};

procedure Ucosym (* Fop : Uopcode; Fint1, Fint2, Fint3 : integer *);
  (* Ugsym, Ucsym, Ulsym, Uesym			     *)
  begin
    U.Opc := Fop;
    with U do begin
      I1 := Fint1;
      Lexlev := Fint2;
      length := Fint3;
      end {with};
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucosym};

procedure Ucolab (* Fname, flag1, flag2 : integer *);
  begin
    U.Opc := Ulab;
    U.I1 := Fname;
    U.Lexlev := flag1;
    U.length := flag2;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucolab};

procedure Ucooptn (* Fname : integer; Fint : integer *);
  begin
    U.Opc := Uoptn;
    U.I1 := Fname;
    U.length := Fint;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucooptn};

procedure Uco3int (* Fop : Uopcode; Fdty : Datatype; Fint1, Fint2 : integer *);
  (* adj, ilod, istr, inn size ALWAYS first (adj,ilod,istr)		     *)
  begin 				(* uco3 			     *)
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.length := Fint1;
    U.Lexlev := 0;
    if U.Opc = Uadj then begin
      U.offset := Fint2;
    end else begin
      U.I1 := Fint2;
    end;
    if Fop = Uistr then begin
      Ubittobyte(U); Uwrite(U);
    end else if Fop = Uinn then begin
      Binarynode;
    end else begin
      Unarynode;
    end;
  end {procedure Uco3int};

procedure Uco3intval (*Fop: Uopcode; Fdty: Datatype; Fint1, Fint2: integer*);
  (* ldc								     *)
  begin
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.length := Fint1;
    U.Constval.Ival := Fint2;
    Leafnode;
  end {procedure Uco3intval};

procedure Uco3val (*Fop: Uopcode; Fdty: Datatype; Fint: integer; Fval: Valu *);
  (* ldc, lca								     *)
  begin
    U.Opc := Fop;
    U.I1 := 0;
    U.Dtype := Fdty;
    U.length := Fint;
    U.Constval := Fval;
    Leafnode;
  end {procedure Uco3val};

procedure Uco4int (* Fop : Uopcode; Llev, Int, Off, Len : integer *);
  (* regs								     *)
  begin
    U.Opc := Fop;
    U.Lexlev := Llev;
    U.I1 := Int;
    U.offset := Off;
    U.length := Len;
    Ubittobyte(U); Uwrite(U);
  end {procedure Uco4int};

procedure Uco5typaddr (* Fop : Uopcode; Fdty : Datatype; Fmty : Memtype;
			 Fblock : integer; Foffset, Flen : Addrrange *);
  (* isld, isst, lod, par, str, pdef				     *)

  begin
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.I1 := Fblock;
    U.offset := Foffset;
    U.Mtype := Fmty;
    U.length := Flen;
    if Fop = Updef then
      U.lexlev := IN_MODE
    else U.lexlev := 0;
    if Fop in [Uisst, Ustr, Unstr, Updef] then begin
      Ubittobyte(U); Uwrite(U);
    end else if Fop = Upar then begin
      Binarynode;
    end else if Fop = Uisld then begin
      Unarynode;
    end else begin
      Leafnode;
    end;
  end {procedure Uco5typaddr};

procedure Uco6 (* Fop : Uopcode; Fdty : Datatype; Fmty : Memtype;
		  Fblock : integer; Foffset, Flen, Foffset2 : Addrrange *);
  (* rlod, rstr, pmov *)
  begin
    U.Opc := Fop;
    U.Dtype := Fdty;
    U.Mtype := Fmty;
    U.I1 := Fblock;
    U.offset := Foffset;
    U.Offset2 := Foffset2;
    U.length := Flen;
    if Fop = Upmov then begin
      Binarynode;
    end else begin
      Ubittobyte(U); Uwrite(U);
    end;
  end {procedure Uco6};

procedure Ucolda (* Fmty : Memtype; Fblock : integer;
		    Foffset, Flen, Foffset2 : Addrrange *);
  begin
    U.Opc := Ulda;
    U.I1 := Fblock;
    U.Mtype := Fmty;
    U.offset := Foffset;
    U.Offset2 := Foffset2;
    U.length := Flen;
    Leafnode;
  end {procedure Ucolda};

procedure Ucomem (* Fop: Uopcode; Fdty : Datatype; Fmty : Memtype;
		    Fblock : integer; Foffset, Flen : Addrrange *);
  {for vreg}
  begin
    U.Opc := Fop;
    U.lexlev := 1;
    U.I1 := Fblock;
    U.Dtype := Fdty;
    U.Mtype := Fmty;
    U.offset := Foffset;
    U.length := Flen;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucomem};

procedure Ucodef (* Fmty : Memtype; Fint : integer *);
  begin
    U.Opc := Udef;
    U.Mtype := Fmty;
    U.length := Fint;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucodef};

procedure Ucoloc (* Fline, Ffile: integer *);

  begin 				(* ucoloc			     *)
    U.Opc := Uloc;
    U.I1 := Ffile;
    U.length := Fline;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucoloc};

procedure Ucoxjp (* Fdty : Datatype; Ffirstlabel, Fotherslabel : integer;
		    Flowbound, Fhighbound : integer *);
  begin 				(* ucoxjp			     *)
    U.Opc := Uxjp;
    U.Dtype := Fdty;
    U.I1 := Ffirstlabel;
    U.Label2 := Fotherslabel;
    U.offset := Flowbound;
    U.length := Fhighbound;
    Ubittobyte(U); Uwrite(U);
  end {procedure Ucoxjp};

procedure Support (* Fsupport : Supports *);
  (* generates a call to a standard procedure cup			     *)
  begin
    with Runtimesupport do begin
      U.Opc := Ucup;
      U.Dtype := Dty[Fsupport];
      U.Lexlev := 1;
      { U.Pname := Idname[Fsupport];					      }
      U.I1 := Symndx[Fsupport];
      st_fixextsc(Symndx[Fsupport], scUndefined);
      U.Pop := Pop[Fsupport];
      U.Push := ord(U.Dtype <> Pdt);
      U.Extrnal := 0;
    end {with};
    Unarynode;
  end {procedure Support};

procedure Stdcallinit (* var Parcount : integer *);
  (* starts call to standard procedure					     *)
  begin
    Uco1int(Umst, 1);
    Parcount := 0;
  end {procedure Stdcallinit};

procedure Par (* Dtype : Datatype; var Parcount : integer *);
  (* calculates address and generates PAR instruction for procedure calls    *)
  var
    Lmty : Memtype;
    Asize : Addrrange;
    align : cardinal;
  begin
    align := Wordsize;
    case Dtype of
    Adt, Hdt : Asize := Pointersize;
    Fdt : Asize := Pointersize;
    Ldt, Jdt : Asize := Intsize;
    Rdt : Asize := Realsize;
    Qdt : begin Asize := Doublesize; align := 2*Wordsize; end;
    Xdt : begin Asize := Extendedsize; align := 2*Wordsize; end;
    Sdt : Asize := Setunitsize;
    Mdt : Asize := Wordsize;	{if > Wordsize, use PMOV}
    end {case};
    Lmty := Pmt;
    Parcount := Roundup(Parcount, Align);
    Uco5typaddr(Upar, Dtype, Lmty, 0, Parcount, Asize);
    Parcount := Parcount+Asize;
    if Parcount mod Wordsize <> 0 then begin
      Parcount := Roundup(Parcount, Wordsize);
    end;
  end {procedure Par};


procedure Partype (* Typep : Strp; var Parcount : integer *);
  (* calculates address and generates PAR instruction for procedure calls    *)
  begin
    Parcount := Roundup(Parcount, Typep^.Align);
    if (Typep^.Stsize <= DoubleWordsize) and 
       not (Typep^.form in [Arrays, Records]) then
      Uco5typaddr(Upar, Typep^.Stdtype, Pmt, 0, Parcount, 
		  max(Typep^.Stsize, Wordsize))
    else Uco6(Upmov, Mdt, Pmt, 0, Parcount, Typep^.Stsize, Typep^.Align);
    Parcount := Parcount + Typep^.Stsize;
    if Parcount mod VarAlign <> 0 then begin
      Parcount := Roundup(Parcount, VarAlign);
    end;
  end {procedure Partype};


function Genstaticchain (* (
	   blk : integer)
   : boolean *);
  (* if static chainning is needed, generate the code and return true;	     *)
  (* otherwise return false						     *)
  var
    lev : integer;
  begin
    lev := top;
    (* get to current procedure level in Display			     *)
    while (Display[lev].Occur <> Blck) and (lev >= 0) do begin
      lev := lev-1;
    end {while};
    {lev < 0 only if program has compile error}
    if (lev < 0) or (blk = Display[lev].Mblock) then begin
      Genstaticchain := false;
    end else begin			(* generate static chainning	     *)
      Genstaticchain := true;
      Uco5typaddr(Ulod, Adt, Mmt, Display[lev].Mblock, static_link_loc, 32);
      lev := lev-1;
      (* must be able to find						     *)
      while blk <> Display[lev].Mblock do begin
	Uco5typaddr(Uisld, Adt, Mmt, Display[lev].Mblock, static_link_loc, 32);
	lev := lev-1;
	if lev < 0 then return; {must have compile error}
      end {while};
    end;
  end {function Genstaticchain};


procedure Passstaticlink (* lv : integer; genpar: boolean *);
(* lv is the level of the called procedure *)
  var
    lev, 			{ for indexing the Display }
    level1 : integer;		{ for counting real level }
  begin
      lev := top;
      (* get to current procedure level in Display			     *)
      while Display[lev].Occur <> Blck do begin
	lev := lev-1;
      end {while};
      if progidp = nil then
	assert(level = lev)
      else assert(level = lev-1);
      if lv > level then begin (* the real level is the display index less 1 *)
	Ucolda(Mmt, Display[lev].Mblock, 0, 32, 0);
      end else begin
	level1 := level;
	Uco5typaddr(Ulod, Adt, Mmt, Display[lev].Mblock, static_link_loc, 32);
	while level1 > lv do begin
	  lev := lev - 1;
	  level1 := level1 - 1;
	  Uco5typaddr(Uisld, Adt, Mmt, Display[lev].Mblock, static_link_loc, 32);
	end {while};
      end;
      if genpar then
        Uco5typaddr(Upar, Hdt, Rmt, 0, intRmtoffset, 32);
  end {procedure Passstaticlink};
