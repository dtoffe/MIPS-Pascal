{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasstmt.p,v 1030.7 88/02/18 14:55:14 bettina Exp $ }

#include "upasglob.h"
#include "cmplrs/uwri.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upasbutil.h"
#include "upascase.h"
#include "upascall.h"
#include "upasexpr.h"
#include "upastree.h"
#include "upasstmt.h"


procedure Statement /* ( Fsys, Statends : Setofsys)  */;
  var
    Lidp : Idp;

(****************************************************************)
(*								*)
(*	ASSIGNMENT						*)
(*								*)
(*	parameter:						*)
(*	  FIDP: pointer to the identifier already parsed	*)
(*								*)
(*	Parses left side of assignement statement, putting	*)
(*	  address on stack if necessary 			*)
(*	Parses right side.  Checks for assignment compatibility.*)
(*	  Does any necessary conversions			*)
(*	Generates code to load right side and store into left	*)
(*	  side							*)
(*								*)
(****************************************************************)
  procedure Assignment (
	      Fidp : Idp);
    var
      Leftside : Attr;
      dummy : Indirtype;

    begin				(* assignment			     *)
      if Fidp^.Klass = Vars then begin
	if Fidp^.Loopvar then begin
	  Error(356);
	end;
      end;				(* assignment to LOOP variable	     *)
(* parse the left side of the statement *)
      Parseleft := true;
      Parseright := false;
      Selector(Fsys+[Becomessy], Fidp, dummy);
      Parseleft := false;
      Parseright := true;
      Leftside := Gattr;
(* if we are going to end up doing an indirect move of
 a record or array, the address must be BELOW the value
 to be assigned *)
      if Leftside.Atypep <> nil then begin
	if (Leftside.Atypep^.Stdtype = Mdt) then begin
	  Loadaddress(Leftside);
	end;
      end;
      if Sy <> Becomessy then begin
	Error(159);
      end else begin			(* get the value to be assigned      *)
	Insymbol;
	Expression(Fsys);
	if (Leftside.Atypep <> nil) and (Gattr.Atypep <> nil) then begin
	  (* check for assignment compatibility 			     *)
	  if not (Comptypes(Leftside.Atypep, Gattr.Atypep) or 
		  Stringpadpossible(Leftside.Atypep, Gattr)) and
	     (not (Leftside.Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) or
	      not (Gattr.Adtype in [Jdt, Ldt, Rdt, Qdt, Xdt]) or
	      (Leftside.Atypep^.Form = Scalar) and (Leftside.Atypep^.Scalkind = Declared) or
	      (Gattr.Atypep^.Form = Scalar) and (Gattr.Atypep^.Scalkind = Declared)) 
	   then begin
	    Error(260);
	  end else begin		(* assignment compatible. Generate   *)
					(* code 			     *)
	    case Leftside.Atypep^.Form of
	    Scalar : begin
		Load(Gattr);
		if Gattr.Adtype <> Leftside.Adtype then begin
		  Matchtoassign(Gattr, Leftside.Atypep);
		end;
		Store(Leftside);
	      end {case Scalar};
	    Power : begin		(* Sets 			     *)
		(* if not same size and offsets, convert		     *)
		if (Gattr.Atypep^.Softmin <> Leftside.Atypep^.Softmin)
		 or (Gattr.Atypep^.Softmax <> Leftside.Atypep^.Softmax) then
		  begin
		  Setmatchtoassign(Gattr, Leftside.Atypep, Leftside.Apacked);
		end;
		Load(Gattr);
		Store(Leftside);
	      end {case Power};
	    Subrange : begin
		Loadandcheckbounds(Gattr, Leftside.Atypep);
		Store(Leftside);
	      end {case Subrange};
	    SPointer, Arrays, Records : begin
		Load(Gattr);
		Store(Leftside);
	      end {case SPointer};
	    Files : Error(361);
	    end {case};
	  end;
	end;
      end;
    end {procedure Assignment};

  procedure Gotostatement;
    var
      Lidp : Idp;
      pcount: integer;

    begin				(* gotostatement		     *)
      if (Sy <> Intconstsy) and (Sy <> Identsy) then begin
	Error(255);
      end else begin
	if Standrdonly and ((Val.Ival < 0) or (Val.Ival > 9999)) then begin
	  Warning(212);
	end;
	Searchid([Labels], Lidp);	(* look up the label		     *)
	if Lidp <> nil then begin
	  with Lidp^ do begin
	    Referenced := true;
	    if Level = Scope then begin
	      (* target label is in current procedure			     *)
	      Uco1int(Uujp, Uclabel);
	    end else begin		(* label is in outwardly nested      *)
					(* procedure			     *)
#if 0	/* Jan-12-87 */
	      if Externallab = 0 then begin
		Lastuclabel := Lastuclabel+1;
	        Externallab := Lastuclabel;
	      end;
	      Passstaticlink(Scope+1, false);
	      Genexpr(stak^.tree);
	      Popstak;
	      Uco5typaddr(Ustr, Adt, Rmt, 0, intRmtoffset, Pointersize);
	      Uco2intint(Ugoob, symndx, Scope);
#endif
	      Externallab := true;
	      Stdcallinit(Pcount);
	      Uco3intval(Uldc, Ndt, Wordsize, symndx);
	      Par(Adt, Pcount);
	      Passstaticlink(Scope+1, false);
	      Par(Adt, Pcount);
	      Support(Nloc_goto);	(* call error routine		     *)
	      SET_GOTO_ATTR(stak^.tree^.u.Extrnal);
	      SET_RETURN_ATTR(stak^.tree^.u.Extrnal);
	      Genexpr(stak^.tree);
	      Popstak;
	    end;
	  end {with};
	end;
	Insymbol;
      end;
    end {procedure Gotostatement};

  procedure returnstatement;
    var retregoffset: integer;
    begin				(* returnstatement		     *)
      if current_block^.Klass = Progname then begin
	if Sy in statends then begin
	  Uco3intval(Uldc, Jdt, Intsize, 0);
	end else begin
	  Expression(Fsys);
	  if not Comptypes(Intptr, Gattr.Atypep) then begin
	    Error(268);
	  end else begin
	    Load(Gattr);
	    Matchtoassign(Gattr, Intptr);
	    Exprprepass(stak^.tree);
	  end;
	end;
	Genexpr(stak^.tree);
	Popstak;
	Uco5typaddr(Ustr, Jdt, Rmt, 0, intRmtoffset, Intsize);
      end else if current_block^.Klass = Func then begin
	if Sy in statends then begin
	  Uco5typaddr(Ulod, current_block^.Idtype^.Stdtype,
	      current_block^.Resmemtype, current_block^.Pfmemblock,
	      current_block^.Resaddr, current_block^.Idtype^.Stsize);
	end else begin
	  Expression(Fsys);
	  if not Comptypes(current_block^.Idtype, Gattr.Atypep) then begin
	    Error(268);
	  end else begin
	    Load(Gattr);
	    Matchtoassign(Gattr, current_block^.Idtype);
	    Exprprepass(stak^.tree);
	  end;
	  current_block^.Fassigned := true;
	end;
	Genexpr(stak^.tree);
	Popstak;
	if current_block^.Idtype <> nil then begin
	  if current_block^.Idtype^.Stdtype in [Qdt, Rdt] then
	    retregoffset := fpRmtoffset
	  else retregoffset := intRmtoffset;
	  Uco5typaddr(Ustr, current_block^.Idtype^.Stdtype, Rmt, 0, 
	      retregoffset, current_block^.Idtype^.Stsize);
        end;
      end;
      Uco0(Uret);
    end {procedure returnstatement};

  procedure Compoundstatement;

    var
      Loopdone : boolean;

      (***********************************************************************)
      (* processes a multiple statement of the form BEGIN statements END     *)
      (***********************************************************************)

    begin				(* compoundstatement		     *)
      Loopdone := false;
      repeat
	repeat
	  Statement(Fsys, statends);
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
    end {procedure Compoundstatement};

  procedure Ifstatement;

    var
      Elselabel, Outlabel : integer;

    begin				(* ifstatement			     *)
      Expression(Fsys+[Thensy]);
      Load(Gattr);
      if Gattr.Atypep <> Boolptr then begin
	Error(359);
      end;
      if Sy = Thensy then begin
	Insymbol;
      end else begin
	Warning(164);
      end;
      Lastuclabel := Lastuclabel+1;	(* generate the jump to the else     *)
					(* part 			     *)
      Elselabel := Lastuclabel;
      Jumpboolexpr(stak^.tree, true, Elselabel, 0);
      Popstak;
      Statement(Fsys+[Elsesy], statends+[Elsesy]); (* parse the then part    *)
      if Sy = Elsesy then begin
	(* generate the jump after the THEN part			     *)
	Lastuclabel := Lastuclabel+1;
	Outlabel := Lastuclabel;
	Uco1int(Uujp, Outlabel);
	Ucolab(Elselabel, 0, 0);	(* put label for the else part	     *)
	Insymbol;
	Statement(Fsys, statends);	(* parse the else part		     *)
	Ucolab(Outlabel, 0, 0);
      end else begin			(* sy <> elsesy; no else part	     *)
	Ucolab(Elselabel, 0, 0);
      end;
    end {procedure Ifstatement};

  procedure Repeatstatement;
    var
      loop_label, saved_loop_continue_label, saved_loop_break_label : integer;
      Loopdone : boolean;
      SavedContinueSeen: boolean;
    begin				(* repeatstatement		     *)
      saved_loop_continue_label := loop_continue_label;
      saved_loop_break_label := loop_break_label;
      Lastuclabel := Lastuclabel+1;	(* insert the label to close the     *)
					(* cycle			     *)
      loop_continue_label := Lastuclabel;
      Lastuclabel := Lastuclabel+1;
      loop_break_label := Lastuclabel;
      Lastuclabel := Lastuclabel+1;
      loop_label := Lastuclabel;
      SavedContinueSeen := ContinueSeen;
      ContinueSeen := false;
      Ucolab(loop_label, 0, 0);
      Loopdone := false;
      repeat
	repeat
	  Statement(Fsys+[Untilsy], statends+[Untilsy, Eofsy]);
	until not (Sy in Statbegsys);
	Loopdone := Sy <> Semicolonsy;
	if not Loopdone then begin
	  Insymbol;
	end;
      until Loopdone;
      if Sy = Untilsy then begin
        (* emit label only if we saw a 'continue' statement *)
        if ContinueSeen then
	  Ucolab(loop_continue_label, 0, 0);
        ContinueSeen := SavedContinueSeen;

	if mainfileNumber = fileNumber then {if at a different file, no LOC}
	  Ucoloc(Linecnt, fileNumber);
	Insymbol;
	Expression(Fsys);
	Load(Gattr);
	if Gattr.Atypep <> Boolptr then begin
	  Error(359);
	end;
	(* close the cycle						     *)
	Jumpboolexpr(stak^.tree, true, loop_label, 0);
	Popstak;
      end else begin
	Error(202);
      end;
      Ucolab(loop_break_label, 0, 0);
      loop_continue_label := saved_loop_continue_label;
      loop_break_label := saved_loop_break_label;
    end {procedure Repeatstatement};

  procedure Whilestatement;
    var
      loop_label, saved_loop_continue_label, saved_loop_break_label : integer;
      whilecond, whilecond2 : pttreerec;
      SavedContinueSeen: boolean;
    begin				(* whilestatement		     *)
      saved_loop_continue_label := loop_continue_label;
      saved_loop_break_label := loop_break_label;
      Lastuclabel := Lastuclabel+1;
      loop_continue_label := Lastuclabel;
      Lastuclabel := Lastuclabel+1;
      loop_break_label := Lastuclabel;
      SavedContinueSeen := ContinueSeen;
      ContinueSeen := false;
      Expression(Fsys+[Dosy]);		(* parse the conditional expression  *)
      Load(Gattr);
      if Gattr.Atypep <> Boolptr then begin
	Error(359);
      end;
      if Sy = Dosy then begin
	Insymbol;
      end else begin
	Warning(161);
      end;
      whilecond := stak^.tree; Popstak;
      whilecond2 := Duplicatetree(whilecond);
      Jumpboolexpr(whilecond, true, loop_break_label, 0);
      Lastuclabel := Lastuclabel+1;	(* insert the label for loop header  *)
      Ucolab(Lastuclabel, 0, 0);
      Lastuclabel := Lastuclabel+1;	(* insert the label for loop header  *)
      loop_label := Lastuclabel;
      Ucolab(loop_label, 0, 0);
      Statement(Fsys, statends);	(* parse the body		     *)

      (* emit label only if we saw a 'continue' statement *)
      if ContinueSeen then
	Ucolab(loop_continue_label, 0, 0);
      ContinueSeen := SavedContinueSeen;

      Jumpboolexpr(whilecond2, false, loop_label, 0);
      Lastuclabel := Lastuclabel+1;	(* this dummy label to allow for     *)
					(* forward code motion		     *)
      Ucolab(Lastuclabel, 0, 0);
      Ucolab(loop_break_label, 0, 0);	(* exit label			     *)
      loop_continue_label := saved_loop_continue_label;
      loop_break_label := saved_loop_break_label;
    end {procedure Whilestatement};

  procedure Forstatement;
    var
      Controlattr, Savedcontrolattr, T1attr, SavedT1attr, T2attr,
	  SavedT2attr : Attr;
      Linstr : Uopcode;
      Cmax, Cmin, T1Val, T2Val : integer;
      Emitcheck, Incloop : boolean;
      Lstamp : integer;
      loop_label, saved_loop_continue_label, saved_loop_break_label : integer;
      SavedContinueSeen: boolean;
      SavedLoopvar: boolean;
      control_changed: boolean;	{true if temp is used instead of the contrl var}
      {for saving the information of the actual control variable}
      control_addr: addrrange;
      control_mtyp: memtype;
      controltemp_attr: Attr;

    procedure Getval (
	    var Tempattr,
		Savedtempattr : Attr;
	    var Constval : integer;
		Ssys,
		TFsys : Setofsys;
		Errno : integer);
      (* gets initial or final value of loop and stores in temporary if not  *)
      (* a constant							     *)
      begin
	Tempattr.Atypep := nil;
	Tempattr.Kind := Expr;
	if not (Sy in Ssys) then begin
	  Errandskip(Errno, Fsys+Fsys);
	end else begin
	  Insymbol;
	  Expression(Fsys+TFsys);
	  if Gattr.Atypep <> nil then begin
	    if not (Gattr.Adtype in [ /* Bdt, Cdt,  */Jdt, Ldt]) then begin
	      Error(315);
	    end else if Controlattr.Atypep <> nil then begin
	      if not Comptypes(Controlattr.Atypep, Gattr.Atypep) then begin
		Error(556);
	      end else if Gattr.Kind = Cnst then begin
		(* convert to type of Controlattr			     *)
		Gattr.Adtype := Controlattr.Adtype;
		Gattr.Atypep := Controlattr.Atypep;
		Tempattr := Gattr;
		(* for compile-time checks, return integer value	     *)
		case Gattr.Adtype of
		/* Bdt, Cdt,						     */
		Jdt, Ldt : Constval := Gattr.Cval.Ival;
		end {case};
#if 0	/* The "error" it checks for is legal Pascal. */
		if Emitcheck then begin
		  if (Constval < Cmin) or (Constval > Cmax) then begin
		    Error(367);
		  end;
		end;
#endif
	      end else begin
		Load(Gattr);
		Matchtoassign(Gattr, Controlattr.Atypep);
		Exprprepass(stak^.tree);
		Genexpr(stak^.tree);
		Popstak;
		Getatemp(Tempattr, Lidp^.Loopvar_idtype, Lstamp, true);
		Uco1attr(Ustr, Tempattr);
	      end;
	    end;
	  end;
	end;
	Savedtempattr := Tempattr;
      end {procedure Getval};

    begin				(* forstatement 		     *)
      (* parse the control variable, and construct an ATTR describing it     *)
      Lstamp := 0;
      Emitcheck := false;
      SavedContinueSeen := ContinueSeen;
      ContinueSeen := false;
      Lidp := nil;
      if Sy <> Identsy then begin
	Errandskip(209, Fsys+[Becomessy, Tosy, Downtosy, Dosy]);
	Controlattr.Atypep := nil;
      end else begin
	Searchid([Vars], Lidp);
	with Lidp^ do begin
	  if Loopvar then Error(356);	(* assignment to LOOP variable	     *)
	  SavedLoopvar := Loopvar;
	  Assignedto := true;
	  Referenced := true;
	  Loopvar := true;
	  (* Loopvar remains true during body of loop, so we can detect if   *)
	  (* user tries to give the loop variable a new value *)
	  Controlattr.Atypep := Idtype;
	  Controlattr.Kind := Varbl;
	  if Idtype <> nil then begin
	    Controlattr.Adtype := Idtype^.Stdtype;
	    Controlattr.Asize := Idtype^.Stsize;
	  end else begin
	    Controlattr.Adtype := Zdt;
	    Controlattr.Asize := Intsize;
	  end;
	  if Vkind = Actual then begin
	    with Controlattr do begin
	      Indirect := Notind;
	      Indexed := false;
	      Ablock := Vblock;
	      Apacked := false;
	      Dplmt := Vaddr;
	      Amty := Vmty;
	      Aclass := Klass;
	      Getbounds(Atypep, Cmin, Cmax);
	      if Runtimecheck and (Atypep <> nil) then begin
		Emitcheck := true;
	      end;
	      if (Asize < Intsize)
		and (   (Cmax =  16#ffff)
		     or (Cmin = 0)
		     or (Cmax =  16#7fff)
		     or (Cmin = -16#8000)
		     or (Cmax =  16#ff)
		     or (Cmax =  16#7f)
		     or (Cmin = -16#80)) then begin
		control_changed := true;
		{save original information of control variable in symbol table}
      		control_addr := vaddr;
      		control_mtyp := vmty;
		{get temporary and update controlattr}
		Getatemp(controltemp_attr, Intptr, Lstamp, true);
		Dplmt := controltemp_attr.Dplmt;
		Asize := Intsize;
		{change information of control variable in symbol table}
		Vmty := Mmt;
		Vaddr := Dplmt;
		Loopvar_idtype := Intptr;
	      end else begin
		control_changed := false;
	        Loopvar_idtype := Idtype;
	      end;
#if 0
	      if Asize < Intsize then begin
		if not lsb_first then begin
		  Dplmt := Dplmt - (Intsize - Asize);
		end;
		Asize := Intsize;
	      end;
#endif
	    end {with};
	  end else begin
	    Error(364);
	    Controlattr.Atypep := nil;
	  end;
	end {with};
	if not (Controlattr.Adtype in [ /* Bdt, Cdt,  */Jdt, Ldt]) then begin
	  Error(365);
	  Controlattr.Atypep := nil;
	end;
	Insymbol;
      end;

      (***********************************************************************)
      (* Save a copy in Savedcontrolattr, so that we can load it multiple    *)
      (* times (after loading an Attr, its state changes)		     *)
      (***********************************************************************)
      Savedcontrolattr := Controlattr;

      (***********************************************************************)
      (* Get the initial value, and store it in a temporary		     *)
      (***********************************************************************)
      Getval(T1attr, SavedT1attr, T1Val, [Becomessy], [Tosy, Downtosy, Dosy],
	  159);

      (***********************************************************************)
      (* Get the final value, and store it in a temporary.		     *)
      (***********************************************************************)
      Incloop := (Sy = Tosy);
      Getval(T2attr, SavedT2attr, T2Val, [Tosy, Downtosy], [Dosy], 251);

      (***********************************************************************)
      (* Emit the initial test to see if the loop will be executed.	     *)
      (***********************************************************************)
      saved_loop_continue_label := loop_continue_label;
      saved_loop_break_label := loop_break_label;
      Lastuclabel := Lastuclabel+1;
      loop_continue_label := Lastuclabel;
      Lastuclabel := Lastuclabel+1;
      loop_break_label := Lastuclabel;

      if (T1attr.Kind = Cnst) and (T2attr.Kind = Cnst) then begin
					(* compile time test		     *)
	if (Incloop and (T1Val > T2Val)) or (not Incloop
	 and (T1Val < T2Val)) then begin
	  Uco1int(Uujp, loop_break_label);
	end;
      end else begin			(* run time test		     *)
	Load(T1attr);
	Load(T2attr);
	if Incloop then begin
	  Linstr := Ugrt;
	end else begin
	  Linstr := Ules;
	end;
	Uco1type(Linstr, Controlattr.Adtype);
	Genexpr(stak^.tree);
	Popstak;
	Uco1int(Utjp, loop_break_label);
      end;

      (***********************************************************************)
      (* Store initial value in loop variable				     *)
      (***********************************************************************)
      T1attr := SavedT1attr;
      if Emitcheck and (T1attr.Kind <> Cnst) then begin
	Load(T1attr);
	Uco2typint(Uchkl, T1attr.Adtype, Cmin);
	Uco2typint(Uchkh, T1attr.Adtype, Cmax);
      end else begin
	Load(T1attr);
      end;
      Matchtoassign(T1attr, Controlattr.Atypep);
      Controlattr := Savedcontrolattr;
      Store(Controlattr);

      (***********************************************************************)
      (* Check to see if final value is within permissible range for the     *)
      (* loop variable and increment by 1				     *)
      (***********************************************************************)
      if (SavedT2attr.Kind = Cnst) then begin (* range checked earlier	     *)
	if Incloop then begin
	  if SavedT2attr.Cval.Ival = Tgtmaxint then begin
	    SavedT2attr.Cval.Ival := Tgtminint;
	  end else begin
	    SavedT2attr.Cval.Ival := SavedT2attr.Cval.Ival+1;
	  end;
	end else if SavedT2attr.Cval.Ival = Tgtminint then begin
	  SavedT2attr.Cval.Ival := Tgtmaxint;
	end else begin
	  SavedT2attr.Cval.Ival := SavedT2attr.Cval.Ival-1;
	end;
#if 0	/* Jul-2-87 */
	if Savedcontrolattr.Asize < Wordsize then begin
	  SavedT2attr.Cval.Ival := bitand(SavedT2attr.Cval.Ival,
					lshift(1, Savedcontrolattr.Asize)-1);
	  if Savedcontrolattr.Adtype = Jdt then begin
	    SavedT2attr.Cval.Ival := bitxor(SavedT2attr.Cval.Ival,
					lshift(1, Savedcontrolattr.Asize-1))
				   - lshift(1, Savedcontrolattr.Asize-1);
	  end;
	end;
#endif
	SavedT2attr.Adtype := Ldt;
      end else begin
	T2attr := SavedT2attr;
	if Emitcheck then begin
	  Load(T2attr);
	  Uco2typint(Uchkl, T2attr.Adtype, Cmin);
	  Uco2typint(Uchkh, T2attr.Adtype, Cmax);
	end else begin
	  Load(T2attr);
	end;
	if T2attr.Adtype <> Ldt then begin
	  Uco2typtyp(Ucvt, Ldt, T2attr.Adtype);
	end;
	if Incloop then begin
	  Linstr := Uinc;
	end else begin
	  Linstr := Udec;
	end;
	Uco2typint(Linstr, Ldt, 1);
	if Savedcontrolattr.Adtype <> Ldt then begin
	  Uco2typtyp(Ucvt, Savedcontrolattr.Adtype, Ldt);
	end;
	SavedT2attr.Adtype := Savedcontrolattr.Adtype;
	T2attr := SavedT2attr;
	Store(T2attr);
      end;

      (***********************************************************************)
      (* Emit the label for the head of the loop			     *)
      (***********************************************************************)
      Lastuclabel := Lastuclabel+1;
      loop_label := Lastuclabel;
      Ucolab(loop_label, 0, 0);
      if control_changed then begin {insert the extra assignment}
        Controlattr := Savedcontrolattr;
        Load(Controlattr);
	Genexpr(stak^.tree);
	Popstak;
	Uco5typaddr(Ustr, Lidp^.idtype^.stdtype, control_mtyp, Memblock,
		    control_addr, Lidp^.idtype^.stsize);
      end;

      (***********************************************************************)
      (* Compile the body of the loop					     *)
      (***********************************************************************)
      if Sy = Dosy then begin
	Insymbol;
      end else begin
	Error(161);
      end;
      Statement(Fsys, statends);

      (***********************************************************************)
      (* increment the loop variable					     *)
      (***********************************************************************)
      (* emit label only if we saw a 'continue' statement *)
      if ContinueSeen then
	Ucolab(loop_continue_label, 0, 0);
      ContinueSeen := SavedContinueSeen;

      Controlattr := Savedcontrolattr;
      Load(Controlattr);
      if Controlattr.Adtype <> Ldt then begin
	Uco2typtyp(Ucvt, Ldt, Controlattr.Adtype);
      end;
      if Incloop then begin
	Linstr := Uinc;
      end else begin
	Linstr := Udec;
      end;
      Uco2typint(Linstr, Ldt, 1);
      Store(Controlattr);

      (***********************************************************************)
      (* test for end of loop						     *)
      (***********************************************************************)
      Controlattr := Savedcontrolattr;
      Load(Controlattr);
      T2attr := SavedT2attr;
      Load(T2attr);
      Uco1type(Uequ, Controlattr.Adtype);
      Genexpr(stak^.tree);
      Popstak;
      Uco1int(Ufjp, loop_label);

      Lastuclabel := Lastuclabel+1;	(* this dummy label to allow for     *)
					(* forward code motion (by Fred      *)
					(* Chow)			     *)
      Ucolab(Lastuclabel, 0, 0);

      Ucolab(loop_break_label, 0, 0);
      if Lidp <> nil then begin
	Lidp^.Loopvar := SavedLoopvar;
      end;
      if Lstamp > 0 then begin
	Freetemps(Lstamp);
      end;
      loop_continue_label := saved_loop_continue_label;
      loop_break_label := saved_loop_break_label;

      if control_changed then begin
	Lidp^.vaddr := control_addr;
	Lidp^.vmty := control_mtyp;
      end;
    end {procedure Forstatement};

(*************************************************************************)
(* WITHSTATEMENT For each record in the statement, saves the address in  *)
(* a temporary if code is generated to compute the address (as in "WITH  *)
(* Arr1[I].Ptr^"), then pushes a description of the address (closely     *)
(* resembles the Attr of the record) onto the display, so that fields of *)
(* the record will be part of future symbol table lookups Note that the  *)
(* global variable TOP (of display) is affected, but LEVEL is not        *)
(*************************************************************************)

  procedure Withstatement;
    var
      Lidp : Idp;
      I : integer;
      Lattr : Attr;
      Loopdone : boolean;
      Lstamp : integer;
      Oldtop : integer;
      indirkind : Indirtype;

    begin				(* withstatement		     *)

      Lstamp := 0;
      Loopdone := false;
      Oldtop := Top;
      repeat				(* until Sy <> commasy		     *)
	(* get address of next record first, parse the record and put a      *)
	(* description in GATTR 					     *)
	if Sy = Identsy then begin
	  Searchid([Vars, Field], Lidp);
	  Insymbol;
	end else begin
	  Error(209);
	  Lidp := Uvarptr;
	end;
	Parseleft := true;
	Selector(Fsys+[Commasy, Dosy], Lidp, indirkind);
	Parseleft := false;
	if Gattr.Atypep <> nil then begin
	  if Gattr.Atypep^.Form <> Records then begin
	    Error(308);
	  end else if Top >= Displimit then begin
	    Error(317);
	  end else begin
	    (* push a desription of the record onto the display 	     *)
	    Top := Top+1;
	    with Display[Top], Gattr do begin
	      Fname := Atypep^.Recfirstfield;
	      Occur := Crec;
	      if Indirect <> Notind then begin
		Loadaddress(Gattr);
	      end;
	      (* if code has been emitted to get the final address of the    *)
	      (* record, save the address in a temporary		     *)
	      if Indexed then begin
		Loadaddress(Gattr);
		if indirkind = Aind then begin
		  Getatemp(Lattr, Addressptr, Lstamp, true);
		end else begin
		  Getatemp(Lattr, Heapptr, Lstamp, true);
		end;
		Store(Lattr);
		Cblock := Lattr.Ablock;
		Mblock := Lattr.Ablock;
		Cindirect := indirkind;
		Cindexed := false;
		Cindexmt := Lattr.Amty;
		Cindexr := Lattr.Dplmt;
		Cdspl := 0;
		CMmtMemcnt := MmtMemcnt;
	      end else begin
		Mblock := Ablock;
		Cblock := Ablock;
		Cmty := Amty;
		Cindirect := Notind;
		Cindexed := false;
		Cdspl := Dplmt;
	      end;
	    end {with};
	  end;
	end;
	Loopdone := Sy <> Commasy;
	if not Loopdone then begin
	  Insymbol;
	end;
      until Loopdone;

      (***********************************************************************)
      (* compile the body of the with statement 			     *)
      (***********************************************************************)
      if Sy = Dosy then begin
	Insymbol;
      end else begin
	Error(161);
      end;
      Statement(Fsys, statends);

      (***********************************************************************)
      (* restore the display to its previous state			     *)
      (***********************************************************************)
      Top := Oldtop;
      if Lstamp > 0 then begin
	Freetemps(Lstamp);
      end;
    end {procedure Withstatement};

(**********************************************************************)
(*								      *)
(*	STATEMENT -- process a statement and its label, if any	      *)
(*								      *)
(**********************************************************************)
  label
    exitloop;

  begin 				(* statement			     *)
    (* process the label, if any	     *)
    while (Sy = Intconstsy) or ((Sy = Identsy) and not Standrdonly) do begin
      if Sy = Intconstsy then begin
        Searchid([Labels], Lidp);
      end else begin
        Searchid([Types, Konst, Vars, Field, Proc, Func, Labels], Lidp);
	if (Lidp = nil) or (Lidp^.Klass <> Labels) then goto exitloop;
      end;
      if Lidp <> nil then begin
	with Lidp^ do begin
	  if Defined then begin
	    Error(211); 		(* duplicate label		     *)
	  end else begin
	    Defined := true;
	    if Externallab then begin
#if 0	/* Jan-12-87 */
	      Uco1int(Uujp, Uclabel);
	      Ucolab(Externallab, GOOB_TARGET, symndx);
	      Ucolab(Uclabel, 0, 0);
#endif
	      Ucolab(Uclabel, EXTERN_LAB_ATTR, symndx);
#if 1	/* avoid umerge screwup */
	    end else if glevel = 0 then begin
	      Ucolab(Uclabel, 0, 0);
#endif
	    end else begin
	      Ucolab(Uclabel, 0, symndx);
	    end;
	  end;
	  if Scope <> Level then begin
	    Error(352); 		(* label not declared on this level  *)
	  end;
	end {with};
      end;
      Insymbol;
      if Sy = Colonsy then begin
	Insymbol;
      end else begin
	Error(151);
      end;
    end {while};
exitloop:

    if not (Sy in Fsys+[Identsy]) then begin
      Errandskip(166, Fsys);
    end;
    if Sy in Statbegsys+[Identsy] then begin
      if Sy <> Beginsy then begin	(* generate LOC statement	     *)
	if mainfileNumber = fileNumber then {if at a different file, no LOC}
	  Ucoloc(Linecnt, fileNumber);
      end;
      if stak <> stakbot then begin
	if errorcount = 0 then begin
	  while (stak <> stakbot) and (stak <> nil) do begin
	    Popstak;
	  end {while};
	  Error(470);
	end else begin
	  stak := stakbot;
	end;
      end;
      case Sy of
      Identsy : begin			(* procedure call or assignment      *)
	  Searchid([Vars, Field, Func, Proc], Lidp);
	  Insymbol;
	  if Lidp^.Klass = Proc then begin
	    do_expr := true;
	    if Lidp^.Prockind = Special then begin
	      Callspecial(Fsys, Lidp);
	    end else if Lidp^.Prockind = Inline then begin
	      Callinline(Fsys, Lidp);
	    end else begin
	      Callregular(Fsys, Lidp);
	    end;
	    if do_expr then begin
	      Exprprepass(stak^.tree);	(* do not need to call genexpr	     *)
					(* because it is a procedure, not    *)
					(* function			     *)
	      Popstak;
	    end;
	  end else begin
	    Assignment(Lidp);
	  end;
	end {case Identsy};
      Beginsy : begin
	  Insymbol;
	  Compoundstatement;
	end {case Beginsy};
      Gotosy : begin
	  Insymbol;
	  Gotostatement;
	end {case Gotosy};
      Returnsy : begin
	  Insymbol;
	  returnstatement;
	end {case Returnsy};
      Ifsy : begin
	  Insymbol;
	  Ifstatement;
	end {case Ifsy};
      Casesy : begin
	  Insymbol;
	  Casestatement(Fsys, statends);
	end {case Casesy};
      Whilesy : begin
	  Insymbol;
	  Whilestatement;
	end {case Whilesy};
      Repeatsy : begin
	  Insymbol;
	  Repeatstatement;
	end {case Repeatsy};
      Forsy : begin
	  Insymbol;
	  Forstatement;
	end {case Forsy};
      Withsy : begin
	  Insymbol;
	  Withstatement;
	end {case Withsy}
      end {case};
    end;

    Skipiferr(statends, 506, Fsys);
  end {procedure Statement};
