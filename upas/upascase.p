{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upascase.p,v 1030.7 88/02/18 14:55:11 bettina Exp $ }

#include "upasglob.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upasexpr.h"
#include "upasutil.h"
#include "upasbutil.h"
#include "upasstmt.h"
#include "upastree.h"
#include "upasfold.h"
#include "upascase.h"
#include "allocator.h"

(*****************************************************************************)
(* CASESTATEMENT Procedure to parse and emit code for a case statement. Uses *)
(* a combination of branch trees (FJP,TJP) and branch tables (XJP), to	     *)
(* conserve space in sparse case lists. Called procedures and functions:     *)
(* CASEINIT Sets up initial variable vals. CASESELECTOR Parses case	     *)
(* selector, emits code to put value in temp. CASELISTELEMENT Parses a case  *)
(* list element, constructs caseinfo records to describe the labels and      *)
(* emits code for the case. OTHERWISESTMT Parses and emits code for an	     *)
(* otherwise clause. ARRANGECASETREE Calculates the 'optimal' tradeoff       *)
(* between branch trees and branch tables. The casptrs array is constructed  *)
(* to represent each node in the tree. EMITCASETREE Emits all decision	     *)
(* making ucode to be executed at run time. EMITBTABLES Emits the ujp tables *)
(* (if necessary) for any branch tables which may be used.		     *)
(*****************************************************************************)
procedure Casestatement /* ( Fsys, Statends : Setofsys)  */;
  const
    Caselements = 256;			(* max number of case clauses	     *)
    Unusedlab = -1;			(* Value never used for a ucode      *)
					(* label			     *)
  type
    Casectrange = 1..Caselements;	(* Subscript range for the casptrs   *)
					(* array			     *)
    Cip = ^Caseinfo;
    Ctype = (Single, Subr, Btable);	(* types of branch tree node. note:  *)
					(* the order of these is	     *)
					(* significant. see the 	     *)
					(* arrangecasetree function.	     *)



(*..................................................................)
(.								   .)
(.			  CASEINFO				   .)
(.								   .)
(.	     Describes one or more CaseListElements.  A 	   .)
(.	     CaseListElement may be a single value (SINGLE)	   .)
(.	     or a subrange specification (SUBR).		   .)
(.								   .)
(.	     As branch tables are layed out during		   .)
(.	     the optimization phase, a CASEINFO is constructed	   .)
(.	     for each branch table (BTABLE), and the		   .)
(.	     CASEINFOs for constituent CaseList Elements	   .)
(.	     are chained through the Next field.		   .)
(.								   .)
(..................................................................*)


    Caseinfo =
      record
	Next : Cip;			(* when caseinfo is in linked list,  *)
					(* this is the fwd ptr		     *)
	Codelabel,			(* label for code to process this    *)
					(* case 			     *)
	Treelabel,			(* label for subtree rooted at this  *)
					(* node 			     *)
	Ltlabel : integer;		(* label where low bound of this     *)
					(* node is checked.		     *)
	Cmode : Ctype;			(* tells what kind of tree node this *)
					(* is				     *)
	Lowval, Hival : integer;	(* inclusive bounds for range	     *)
					(* spanned by this node in the tree  *)
      end {record};


    Reltype = (Goesabove, Goesbelow, Mrgsabove, Mrgsbelow, Overlaps, Nothere);
					(* possible results of a relation    *)
					(* test between two caseinfo entries *)

  var
    Casptrs : array[Casectrange] of Cip; (* Starts with a single element     *)
					(* which represents all cases in a   *)
					(* single branchtable. Arrangecase   *)
					(* iterates until an 'optimal' tree  *)
					(* is represented, with each node in *)
					(* each element of this array.	     *)
    Casecount : Casectrange;		(* number of elements in casptrs     *)
					(* array			     *)
    Labelcount : integer;		(* number of labels which have been  *)
					(* parsed			     *)
    Lstrp : Strp;			(* type for selector		     *)
    Lattr : Attr;			(* expression for temp		     *)
    Lval : Valu;			(* value for case labels	     *)
    Highest : integer;			(* highest label encountered	     *)
    /* Atsize : integer;						     */
					(* size in bits of label fields      *)
    Typeok : boolean;			(* true when selector is properly    *)
					(* typed to match labels	     *)
    Loopdone : boolean; 		(* TRUE if caselist-element is not   *)
					(* followed by a semicolon. Means    *)
					(* that no case list elements may    *)
					(* follow.			     *)
    Outlabel : integer; 		(* all done label		     *)
    Entrylabel : integer;		(* ucodelabel at which decision      *)
					(* testing begins		     *)
    Listanchor : Cip;			(* anchor for list of case labels    *)
    Otherwiselabel : integer;		(* label on otherwise code	     *)
    Curpage, Curline : integer; 	(* page and line number of case      *)
					(* stmnt			     *)
    Lstamp : integer; 			(* stamp for temporaries *)
    (* CASEMERGE Merges caseinfos for two adjacent list labels which	     *)
    (* together form a subrange. Either or both of the supplied arguments    *)
    (* may be for a subrange. The returned answer will always represent a    *)
    (* subrange. PARAMETERS: A,B (CIP) pointers to CASEINFO for items to be  *)
    (* merged. B always represents the label with higher value. RESULT: The  *)
    (* resulting subrange is represented in the caseinfo which had been used *)
    (* for A. The CASEINFO for B is unchained and is effectively lost.	     *)

  procedure Casemerge (
	      A,
	      B : Cip);
    var
      Newlow, Newhi : integer;		(* these are the range delimiters    *)
					(* for the result		     *)

    begin				(* start of casemerge		     *)
      Newlow := A^.Lowval;		(* set range of result		     *)
      Newhi := B^.Hival;
      with A^ do begin			(* put folded entry in a. unchain b  *)
					(* fold and unchain		     *)
	Cmode := Subr;			(* result is a subrange 	     *)
	Lowval := Newlow;		(* set new bottom of subrange	     *)
	Hival := Newhi; 		(* set new top of subrange	     *)
	Next := B^.Next;		(* unchain b			     *)
      end {with};
    end {procedure Casemerge};


    (*************************************************************************)
    (* CRELATE Function determines the relationship of the label values for  *)
    (* two supplied CASEINFOS. The CASEINFOS may be for either single valued *)
    (* or subrange valued labels. If the result is MRGSABOVE or MRGSBELOW,   *)
    (* the two supplied CASEINFOS have label ranges with adjacent values and *)
    (* are thus mergeable into a single subrange. GOESABOVE and GOESBELOW    *)
    (* indicate the relationship between non-overlapping, non-mergeable      *)
    (* label groups. OVERLAPS is indicated for equal label values, or for    *)
    (* label values which overlap in any way. NOTHERE is returned if either  *)
    (* of the supplied caseinfo pointers is nil. PARAMETERS: A,B (CIP)	     *)
    (* pointers to the two CASEINFOS which are to be compared. OPERATION: 1) *)
    (* If either pointer is nil, the result is NOTHERE. 2) To save repeated  *)
    (* indirections, the local variables Alow, Ahi, Blow, and Bhi are set to *)
    (* the label ranges of A and B. 3) The ranges are tested for overlap. If *)
    (* there is no overlap, then the relationship is computed and returned.  *)
    (*************************************************************************)

  function Crelate (
	     A,
	     B : Cip)
     : Reltype;

    var
      Ans : Reltype;			(* answer is developed here	     *)
      Alow, Ahi : integer;		(* label range of a		     *)
      Blow, Bhi : integer;		(* label range of b		     *)
    begin				(* begin crelate		     *)
      if (A = nil) or (B = nil) then begin (* if either argument is nil      *)
	Ans := Nothere;			(* return nothere		     *)
      end else begin			(* neither supplied ptr is nil	     *)
					(* neither argument is nil	     *)
	with A^ do begin		(* set range of a		     *)
	  Alow := Lowval;		(* low bound of a		     *)
	  Ahi := Hival; 		(* high bound of a		     *)
	end {with};			(* end set range of a		     *)
	with B^ do begin		(* set range of b		     *)
	  Blow := Lowval;		(* low bound of b		     *)
	  Bhi := Hival; 		(* high bound of b		     *)
	end {with};			(* end set range of b		     *)
	if Blow <= Ahi then begin	(* b is not cleanly above a	     *)
	  if Bhi >= Alow then Ans := Overlaps
	  else				(* a is cleanly above b 	     *)
	  if (Alow-Bhi) = 1 then Ans := Mrgsabove (* a goes just above b     *)
	  else Ans := Goesabove;	(* a goes well above b		     *)
	end else			(* b is cleanly above a 	     *)
	if (Blow-Ahi) = 1 then Ans := Mrgsbelow (* a goes just below b	     *)
	else Ans := Goesbelow;		(* a goes well below b		     *)
      end;				(* end neither argument is nil	     *)
      Crelate := Ans;			(* set up to return the answer	     *)
    end {function Crelate};

    (*************************************************************************)
    (* CASEINSERT PARAMETERS: A (CIP) ptr to caseinfo to be inserted in the  *)
    (* list. B (CIP) ptr to caseinfo after which a is inserted. If B is nil, *)
    (* then A is chained from LISTANCHOR. RESULT: A is inserted in list      *)
    (* after B. 							     *)
    (*************************************************************************)

  procedure Caseinsert (
	      A,
	      B : Cip);

    begin				(* caseinsert			     *)
      if B <> nil then begin		(* if not chaining at head of list   *)
					(* chain-not at head of list	     *)
	A^.Next := B^.Next;		(* hang rest of chain from a	     *)
	B^.Next := A;			(* hang a from b		     *)
      end else begin			(* goes at head of list chain at     *)
					(* head of list 		     *)
	A^.Next := Listanchor;		(* hang rest of lit from a	     *)
	Listanchor := A;		(* put a at head of list	     *)
      end;
    end {procedure Caseinsert};

    (*************************************************************************)
    (* CLABCHAIN Inserts new case label in chain. Loops through existing     *)
    (* chain of case labels to insert the new one in sorted order. The	     *)
    (* CRELATE procedure is used to determine the relationship of the new    *)
    (* case label and those which are already in the list. Where possible,   *)
    (* adjacent labels are merged to form subranges. PARAMETERS: NEWLABP     *)
    (* (CIP) CASEINFO ptr. for new label. CDLAB (integer) code label for new *)
    (* label. OPERATION: 1) Loop using CRELATE to find the position for the  *)
    (* new label in the linked list. 2) Use CASEINSERT to add the CASEINFO   *)
    (* to the list. 3) If CRELATE has indicated that it is possible, use     *)
    (* CASEMERGE to combine the new label with existing labels into a	     *)
    (* subrange. It is possible that a new label will combine with those     *)
    (* above and below it.						     *)
    (*************************************************************************)

  procedure Clabchain (
	      Newlabp : Cip;
	      Cdlab : integer);

    var
      Prev, Current : Cip;		(* chain pointers		     *)
      Nextcase : Cip;			(* ^ following item on upward merge  *)
      Newrelcurrent : Reltype;		(* relationship of new to item in    *)
					(* list 			     *)

    begin				(* clabchain			     *)
      Current := Listanchor;		(* start at head of the list	     *)
      Prev := nil;			(* prev ptr lags behind current      *)

      Newrelcurrent := Crelate(Newlabp, Current); (* how relates to first in *)
					(* list 			     *)
      while Newrelcurrent = Goesabove do begin (* find where this goes in    *)
					(* list 			     *)
	Prev := Current;		(* follow the chain		     *)
	Current := Current^.Next;
	Newrelcurrent := Crelate(Newlabp, Current);
      end {while};			(* find where this goes in list      *)
      case Newrelcurrent of		(* see where this goes in list	     *)

      Goesbelow : Caseinsert(Newlabp, Prev); (* insert after prev	     *)

      Mrgsbelow : begin 		(* new one goes immediately below    *)
					(* current			     *)
	  Caseinsert(Newlabp, Prev);	(* insert after prev		     *)
	  if Current^.Codelabel = Cdlab then begin (* if these are labels on *)
					(* the same code		     *)
	    Casemerge(Newlabp, Current); (* merge to form subrange	     *)
	  end;
	end {case Mrgsbelow};		(* new one goes immediately below    *)
					(* current			     *)
      Mrgsabove : begin 		(* new one merges above current      *)
	  Caseinsert(Newlabp, Current); (* insert after current 	     *)
	  if Current^.Codelabel = Cdlab then begin (* if these are labels on *)
					(* the same code		     *)
	    Casemerge(Current, Newlabp); (* merge as subrange		     *)
	  end else Current := Newlabp;	(* keep ptrs straight for following  *)
					(* code 			     *)
	  Nextcase := Current^.Next;


(*..................................................................)
(.								   .)
(.	    Check how this relates to the one above.		   .)
(.								   .)
(..................................................................*)

	  case Crelate(Current, Nextcase) of
	  Goesbelow :
	      ; 			(* all set			     *)
	  Nothere : Highest := Current^.Hival; (* this is new highest	     *)
	  Overlaps : Error(261);	(* handle the overlap		     *)
	  Mrgsbelow : begin
	      if Nextcase^.Codelabel = Cdlab then begin (* these are	     *)
					(* mergeable			     *)
		Casemerge(Current, Nextcase); (* do the upward merge	     *)
	      end;
	    end {case Mrgsbelow}
	  end {case};
	end {case Mrgsabove};		(* new one merges above current      *)

      Overlaps : Error(261);

      Nothere : begin			(* this goes at end of list	     *)
	  Highest := Newlabp^.Hival;	(* set highest label to date	     *)
	  Caseinsert(Newlabp, Prev);
	end {case Nothere}
      end {case};			(* end see where this goes in list   *)
    end {procedure Clabchain};


    (*************************************************************************)
    (* CASELABEL Parses one caselabel up to a comma or colon, and checks for *)
    (* a valid terminator. A CASEINFO is constructed, inserted in the linked *)
    (* list, and if there is a match on CODELABELS, is checked for merging   *)
    (* with others to form a subrange. PARAMETERS: CDLAB (integer) the ucode *)
    (* label for the code currently being emitted. Knowing this allows the   *)
    (* routine to locate elements in the linked list which are potentially   *)
    (* foldable. OPERATION: Parses the case label as a constant, and builds  *)
    (* a caseinfo for it. The existing linked list is searched, with the     *)
    (* CRELATE routine used to check the relationship between the new label, *)
    (* and the others on the list. The new one is inserted in sorted order,  *)
    (* and if possible, CASEMERGE is used to fold it with others to form a   *)
    (* subrange. ROUTINES CALLED: NEW Allocate a CASEINFO CRELATE Compare    *)
    (* label values CASEINSERT Insert new CASEINFO in list CASEMERGE Merge   *)
    (* CASEINFOS into subrange						     *)
    (*************************************************************************)

  procedure Caselabel (
	      Cdlab : integer);

    var
      Newlabp : Cip;			(* ^ newly allocate caseinfo	     *)
      Lstrp1 : Strp;			(* type of label value		     *)
      Labval : integer; 		(* value for this label 	     *)

    begin				(* caselabel			     *)
      Labelcount := Labelcount+1;	(* another label parsed 	     *)
      ConstantExpression(Fsys+[Commasy, Colonsy, Rangesy], Lstrp1, Lval);
					(* parse the label as a constant     *)
      if (Lstrp <> nil) then begin	(* if selector exists		     *)
	if Comptypes(Lstrp, Lstrp1) then begin (* types are compatible	     *)
	  new1(Newlabp); 		(* allocate a new caseinfo	     *)
	  with Newlabp^ do begin	(* fill in new caseinfo 	     *)
	    Next := nil;		(* initialize the chain ptr	     *)
	    Codelabel := Cdlab; 	(* ucode label to execute this case  *)
	    Treelabel := Unusedlab;	(* no tree rooted here yet	     *)
	    Ltlabel := Unusedlab;	(* no label to do low bounds	     *)
					(* checking yet 		     *)
	    Cmode := Single;		(* assume there is no subrange	     *)
	    Labval := Lval.Ival;
	    Lowval := Labval;
	    Hival := Labval;
	    if Sy = Rangesy then begin	(* handle explicite subrange	     *)
	      Insymbol; 		(* skip the two dots		     *)
	      ConstantExpression(Fsys+[Commasy, Colonsy], Lstrp1, Lval);
					(* parse upper bound		     *)
	      if Comptypes(Lstrp, Lstrp1) then begin (* types are compatible *)
		Labval := Lval.Ival;
		if Labval >= Lowval then begin (* legal subrange	     *)
		  Hival := Labval;	(* set upper bound of subrange	     *)
		  Cmode := Subr;	(* indicate that this is a subrange  *)
		end else Error(451);	(* bounds are backwards 	     *)
	      end else Error(505);	(* incompatible types		     *)
	    end;
	  end {with};			(* end fill in new caseinfo	     *)
	  Clabchain(Newlabp, Cdlab);	(* chain it in link list and fold if *)
					(* necessary			     *)
	  if not (Sy in [Commasy, Colonsy]) then Error(151);
					(* comma or semicolon missing after  *)
					(* case lab			     *)
	end else Error(505);		(* types are compatible 	     *)
      end;
    end {procedure Caselabel};

    (*************************************************************************)
    (* CASELISTELEMENT Parses one caselist element. Adds to sorted linked    *)
    (* list of CASEINFOS which is hung from LISTANCHOR. PROCEDURES CALLED:   *)
    (* CASELABEL Parse a case label UC02INTINT Emit a ucode label STATEMENT  *)
    (* Parse the body of this case UCO1INT Emit a ujp ucode OPERATION: Loops *)
    (* through all case labels using the cASELABEL procedure to parse each   *)
    (* one. Emits the CODELABEL into ucode, then calls STATEMENT to handle   *)
    (* the body. A final unconditional jump is emited to branch around other *)
    (* cases and testing code.						     *)
    (*************************************************************************)

  procedure Caselistelement;

    var
      Nextcdlab : integer;		(* codelabel			     *)
      Loopdone : boolean;

    begin				(* caselistelement		     *)
      Nextcdlab := Getlabel;		(* allocate a label for the code     *)
      Loopdone := false;		(* loop not finished yet	     *)
      repeat				(* go through all labels on this     *)
					(* element			     *)
	Caselabel(Nextcdlab);		(* parse the next label 	     *)
	Loopdone := Sy <> Commasy;	(* if followed by comma, try for     *)
					(* another			     *)
	if not Loopdone then Insymbol;	(* skip the comma		     *)
      until Loopdone;			(* go through all labels on this     *)
					(* element			     *)

      (***********************************************************************)
      (* ..................................................................) *)
      (* (. .) (. EMIT THE LABEL FOR THIS CASE CODE .) (. .)		     *)
      (* (..................................................................
									     *)
      (***********************************************************************)

      Ucolab(Nextcdlab, 0, 0);

      (***********************************************************************)
      (* ..................................................................) *)
      (* (. .) (. PARSE THE COLON AND THE CODE BODY .) (. .)		     *)
      (* (..................................................................
									     *)
      (***********************************************************************)

      if Sy = Colonsy then Insymbol
      else Error(151);			(* colon missing in case list	     *)
					(* element			     *)
      Statement(Fsys+[Otherwisesy], Statends+[Otherwisesy]);
					(* parse the body		     *)
      Uco1int(Uujp, Outlabel);		(* emit branch around other cases    *)
    end {procedure Caselistelement};

    (*************************************************************************)
    (* CASESELECTOR Parses the selector expression for a case statement, and *)
    (* saves its value in a temporary variable. OPERATION: 1) Use EXPRESSION *)
    (* procedure to parse the selector. 2) Make sure the type is legal in a  *)
    (* case stmt. 3) Emit ucode to load it on runtime stack. 4) If it's char *)
    (* or boolean coerce it to an integer. 5) Allocate a temporary and emit  *)
    (* code to store the selector. This saves it while the code for the      *)
    (* individual cases is compiled.					     *)
    (*************************************************************************)


  procedure Caseselector;

    var
      Tmin, Tmax : integer;		(* returned by getbounds for	     *)
      exitlab : integer;

    begin				(* caseselector 		     *)
      Expression(Fsys+[Ofsy, Commasy, Colonsy]); (* evaluate the selector    *)
					(* expression			     *)
      Lstrp := Gattr.Atypep;		(* save the type		     *)
      if Lstrp <> nil then begin	(* if expr was evaluated	     *)
	if (Lstrp^.Form <> Scalar) or (Lstrp = Realptr) or (Lstrp = Doubleptr)
	 or (Lstrp = Extendedptr) then begin (* not valid type		     *)
	  Error(315);			(* bad type			     *)
	  Lstrp := nil; 		(* make sure never used 	     *)
	end;				(* not valid type		     *)
	Load(Gattr);			(* put selector on stack	     *)
	Getatemp(Lattr, Gattr.Atypep, Lstamp, true);
	Lattr.Adtype := Gattr.Adtype;	(* remember the type		     *)
	if not (Lattr.Adtype in [Jdt, Ldt]) then begin
	  Error(169);		(* wrong data type		     *)
	end;
#if 0
	Lattr.Kind := Varbl;
	Lattr.Ablock := 0;
	Lattr.Amty := Tmt;
	Lattr.Dplmt := 0;
	Lattr.Indexed := false;
	Lattr.Indirect := Notind;
	Lattr.Aclass := Vars;
#endif
	if Isboolexpr(stak^.tree) then begin
	  Lastuclabel := Lastuclabel+1;
	  exitlab := Lastuclabel;
	  Strboolexpr(stak^.tree, false, nil, Lattr, exitlab,
	      Startwithor(stak^.tree), exitlab);
	  Ucolab(exitlab, 0, 0);
	end else begin
	  Exprprepass(stak^.tree);
	  Genexpr(stak^.tree);
	  Uco1attr(Ustr, Lattr);	(* save in temporary *)
	end;
	Popstak;
      end;				(* if expr was evaluated	     *)

    end {procedure Caseselector};

    (*************************************************************************)
    (* CASEINIT Initialize for case statement parsing OPERATION: Initializes *)
    (* assorted variables for subsequent use.				     *)
    (*************************************************************************)

  procedure Caseinit;
    begin
      Lstrp := nil;			(* no type for selector yet	     *)
      Listanchor := nil;		(* no list of labels yet	     *)
      Labelcount := 0;			(* no labels yet		     *)
      Typeok := false;			(* don't yet know datatype to use    *)
					(* for our tests		     *)
      Lstamp := 0;			(* no temporaries yet		     *)
      Curpage := Pagecnt;		(* remember current location	     *)
      Curline := Linecnt;
    end {procedure Caseinit};

    (*************************************************************************)
    (* ARRANGEINIT Initialize for optimization phase of case statement	     *)
    (* parsing ARRANGEINIT prepares an initial entry in the casptrs array.   *)
    (* This entry represents all case labels as being handled in a single    *)
    (* branch table. The ARRANGECASETREE procedure then attempts to split up *)
    (* this branch table. OPERATION: 1) If there is only a single case label *)
    (* (unlikely) then it is stored directly in CASPTRS[1]. This will cause  *)
    (* ARRANGECASETREE to nop. 2) Otherwise, a new CASEINFO is allocated to  *)
    (* represent the branch table. It is stored as the only entry in	     *)
    (* CASPTRS. 3) The new CASEINFO is filled in to represent the branch     *)
    (* table.								     *)
    (*************************************************************************)

  procedure Arrangeinit;

    begin
      Casecount := 1;			(* array has one entry		     *)
      if Listanchor^.Next <> nil then begin (* there are multiple labels set *)
					(* up tree for multiple labels	     *)
	new1(Casptrs[1]);		(* allocate caseinfo for initial     *)
					(* tree 			     *)
	with Casptrs[1]^ do begin	(* fill in tree caseinfo	     *)
	  Next := Listanchor;		(* whole list in this tree for now   *)
	  Codelabel := Unusedlab;	(* dont know where or if table	     *)
					(* exists			     *)
	  Treelabel := Unusedlab;	(* no tree yet			     *)
	  Ltlabel := Unusedlab; 	(* no low test yet		     *)
	  Cmode := Btable;		(* this is a branch table	     *)
	  Lowval := Listanchor^.Lowval; (* lowest of all cases		     *)
	  Hival := Highest;		(* highest of all cases 	     *)
	end {with};			(* fill in tree caseinfo	     *)
      end else begin			(* exactly one caselistelement	     *)
	Casptrs[1] := Listanchor;	(* make it the tree		     *)
      end;
    end {procedure Arrangeinit};

    (*************************************************************************)
    (* ARRANGECASETREE Iterates through the label entries which have been    *)
    (* parsed and makes reasonable space time tradeoffs between the use of   *)
    (* branch trees and branch tables in the object code. The resulting      *)
    (* (possibly degenerate tree) has each node represented by an entry in   *)
    (* the CASPTRS array. OPERATION: 1) All calculations below are repeated  *)
    (* until tree stabilizes 2) For each branch table in the tree, traverse  *)
    (* its entries to see if a split is desirable. 3) When splitting, the    *)
    (* original table is truncated to the split point, and a new entry is    *)
    (* inserted in the array. Normally the new entry will be tested on the   *)
    (* next time through the loop, so further splits may result. 4) The      *)
    (* incremental time cost of adding entries to the branch table slowly    *)
    (* decreases with increasing size of the tree. For this reason, some     *)
    (* splits which at first seems undesirable may later prove profitable.   *)
    (* Looping continues until the tree stabilizes or is completely split.   *)
    (*************************************************************************)

  procedure Arrangecasetree;

    const
      Spacetime = 1.0;			(* tunable parameter indicates	     *)
					(* relative weight to give space vs. *)
					(* execution time. Higher numbers    *)
					(* cause less space, longer times.   *)
					(* express in (approx) ratio of      *)
					(* undesirability emiting an	     *)
					(* instruction vs. executing an      *)
					(* instruction. 		     *)
      Ln2t2 = 1.38628;			(* 2*ln2			     *)


    var
      Timesaved : real; 		(* time saved by not adding a node   *)
      Labinv : real;			(* inverse of number of labels	     *)
      Openspace : integer;		(* unused label vals between 2	     *)
					(* entries			     *)
      Cindex : integer; 		(* array loop index		     *)
      Lowsplit, Upprsplit : Cip;	(* span a possible split	     *)
      Bumptr : integer;
      Lsplitlow, Lsplithigh : integer;	(* case label span for lower part of *)
					(* split			     *)
      Usplitlow, Usplithigh : integer;	(* case label span for upper part of *)
					(* split			     *)
      Ltype, Utype : Ctype;		(* if we split, these will be modes  *)
					(* of the lower and upper results    *)
      Split : boolean;			(* true when tree is to be split     *)
					(* here 			     *)
      Nochange : boolean;		(* true when tree has stabilized     *)
      Firstintable : boolean;		(* true when parsing first list      *)
					(* entry for a table.		     *)

    begin				(* arrangecasetree		     *)
      Arrangeinit;			(* set up everything as one btable   *)
      if Labelcount <> 0 then Labinv := 1.0/Labelcount (* approximates extra *)
					(* time lost when adding a subrange  *)
					(* type entry to the branch tree     *)
      else Labinv := 1.0;		(* in case something is fouled up    *)
      repeat				(* now keep trying to split it	     *)
	Nochange := true;		(* assume tree has stabilized	     *)
	Cindex := 1;			(* start at beginning of array	     *)
	repeat				(* do one iteration through array    *)
	  if Casptrs[Cindex]^.Cmode = Btable then begin (* go through btable *)
					(* looking for split		     *)
	    with Casptrs[Cindex]^ do begin (* use mother entry for btable    *)
					(* set up to look for a split	     *)
	      Lsplitlow := Lowval;	(* low bound of lower section	     *)
	      Usplithigh := Hival;	(* high bound of upper section	     *)
	      Lowsplit := Next; 	(* first chain entry		     *)
	    end {with}; 		(* set up to look for a split	     *)
	    Upprsplit := Lowsplit^.Next; (* possible pint for split	     *)
	    Firstintable := true;	(* assume split at first entry	     *)
	    repeat			(* loop looking for place to split   *)
	      with Lowsplit^ do begin	(* set up to check this split	     *)
		if Firstintable then Ltype := Cmode (* type of lower section *)
		else Ltype := Btable;
		if Upprsplit^.Next = nil then Utype := Upprsplit^.Cmode
		else Utype := Btable;	(* type of upper section	     *)
		Lsplithigh := Hival;	(* high bound of lower section	     *)
		Usplitlow := Upprsplit^.Lowval; (* low bound of upper	     *)
					(* section			     *)
	      end {with};		(* set up to check this split	     *)

	      (***************************************************************)
	      (* DECIDE WHETHER TO SPLIT THE TABLE HERE 		     *)
	      (***************************************************************)

	      Timesaved := Ln2t2/Casecount; (* time saved if we don't add a  *)
					(* node 			     *)
	      Openspace := Usplitlow-Lsplithigh; (* number of unused table   *)
					(* entries between these labels      *)
	      case (3*ord(Ltype))+ord(Utype) of
	      0 : Split := (Spacetime*(Openspace-3)) > Timesaved;
	      1, 			(* split two singles		     *)
	      3 : Split := (Spacetime*((Usplithigh-Lsplitlow)-7)) > (Labinv+
		      Timesaved);
	      2, 			(* split single from subrange	     *)
	      6 : Split := (Spacetime*(Openspace-4)) > Timesaved;
	      4 			(* split single and table?	     *)
	       : Split := (Spacetime*((Usplithigh-Lsplitlow)-9)) > (Labinv+
		      Timesaved);
	      5 			(* split two subranges? 	     *)
	       : Split := (Spacetime*((Usplitlow-Lsplitlow)-6)) > (Labinv+
		      Timesaved);
	      7 			(* subrange from table		     *)
	       : Split := (Spacetime*((Usplithigh-Lsplithigh)-6)) > (Labinv+
		      Timesaved);
	      8 			(* table from subrange		     *)
	       : Split := (Spacetime*(Openspace-5)) > Timesaved
					(* split two branch tables?	     *)
	      end {case};

	      if Split then begin	(* if tradeoff is to split	     *)
		if Casecount < Caselements then begin (* and we've still got *)
					(* room split here		     *)
		  Casecount := Casecount+1;
		  for Bumptr := Casecount downto Cindex+2 do begin
					(* free a slot in the array	     *)
		    Casptrs[Bumptr] := Casptrs[Bumptr-1];
		  end {for};
		  if Utype = Btable then begin (* allocate new mother entry  *)
					(* for upper			     *)
		    new1(Casptrs[Cindex+1]);
		    with Casptrs[Cindex+1]^ do begin (* fill in the new      *)
					(* entry			     *)
		      Next := Upprsplit; (* hang rest of chain		     *)
		      Codelabel := Unusedlab; (* no code yet		     *)
		      Treelabel := Unusedlab;
		      Ltlabel := Unusedlab;
		      Cmode := Btable;
		      Lowval := Usplitlow; (* new low bound on tree	     *)
		      Hival := Usplithigh; (* new high bound		     *)
		    end {with};
		  end else begin	(* new upper is not a table	     *)
		    Casptrs[Cindex+1] := Upprsplit; (* put in single element *)
		  end;			(* for upper side of split	     *)
		  Lowsplit^.Next := nil; (* end of lower list		     *)
		  if Ltype = Btable then Casptrs[Cindex]^.Hival := Lsplithigh
					(* high bound on lower branch table  *)
		  else Casptrs[Cindex] := Lowsplit; (* put individual entry  *)
					(* right in table		     *)
		end else Error(322);
	      end;
	      Firstintable := false;	(* no longer at first spot	     *)
	      Lowsplit := Upprsplit;	(* follow the chain		     *)
	      Upprsplit := Upprsplit^.Next;
	    until Split or (Upprsplit = nil); (* look for place to split     *)
	    Nochange := Nochange and not (Split);
	  end;				(* go through btable looking for     *)
					(* split			     *)
	  Cindex := Cindex+1;		(* next array entry		     *)
	until Cindex > Casecount;	(* do one iteration through array    *)
      until Nochange;			(* now keep trying to split it	     *)
    end {procedure Arrangecasetree};

    (*************************************************************************)
    (* EMIT Emits ucode for comparison of selector Parameters: A (Uopcode)   *)
    (* the ucode op code for the test. B (integer) value against which to    *)
    (* test. Operation: 1) Makes local copy of selector expression so	     *)
    (* original is still considered in temporary. 2) Loads the selector. 3)  *)
    (* Now that all of the labels have been parsed, the selector may have to *)
    (* be re-typed. If necessary, do it. Retype the temporary, and if there  *)
    (* are more cases to follow, do a non-destructive store to remember it.  *)
    (* 4) If first time through, compute atsize. This is the size in bits of *)
    (* constants to be loaded for comparison with the selector. 5) Emit a    *)
    (* ldc for parameter B (the comparand) followed by A (the test	     *)
    (* instruction).							     *)
    (*************************************************************************)

  procedure Emit (
	      A : Uopcode;
	      B : integer);

    var
      Fattr : Attr;			(* loaded copy of selector	     *)
      Loctype : Strp;			(* local type ptr		     *)
      Locdt : Datatype; 		(* datatype of selector 	     *)
      Tmin, Tmax : integer;		(* bounds of subrange		     *)

    begin				(* emit 			     *)
      Fattr := Lattr;			(* copy the selector expression      *)
      Load(Fattr);			(* load the selector		     *)
      /* if not Typeok then (* if first time through *) with Fattr do begin  */
      /* (* must retype the selector *) Locdt := Adtype; (* assume no type   */
      /* change *) if Adtype in [Bdt, Cdt] then begin (* selector bool or    */
      /* char *) Getbounds(Atypep, Tmin, Tmax); if Tmin < 0 then Locdt :=    */
      /* Jdt else Locdt := Ldt; end {then}; (* selector bool or char *) if   */
      /* Casptrs[1]^.Lowval < 0 then (* isn't pos data type *) if Locdt =    */
      /* Ldt then Locdt := Jdt; (* small integers short *) (* integer *)     */
      /* Loctype := Intptr; Atsize := Intsize; if Locdt <> Adtype then begin */
      /* (* we are retyping *) Uco2typtyp(Ucvt, Locdt, Adtype); (* do the    */
      /* ucode cvt *) if Casecount > 1 then begin (* we're going to need it  */
      /* *) (* again *) { Freetemp(Lattr); (* free up the old selector *) }  */
      /* Getatemp(Lattr, Loctype, Lstamp, true); (* allocate a new temp *)   */
      /* Lattr.Adtype := Locdt; (* remember the type *) Uco1attr(Unstr,      */
      /* Lattr) (* save a retyped copy *) end {then}; (* we're going to need */
      /* it again *) end {then}; (* we are retyping *) Typeok := true end    */
      /* {with} else Locdt := Lattr.Adtype; (* get the right data type *)    */
      Uco3intval(Uldc, Fattr.Adtype, Intsize, B); (* set up the constant for *)
					(* tree compare 		     *)
      Uco1type(A, Fattr.Adtype);	(* emit the ucode compare	     *)
      Genexpr(stak^.tree);
      Popstak;
    end {procedure Emit};

    (*************************************************************************)
    (* XEMIT Procdedure to emit xjp ucodes Parameters: A,B value range of    *)
    (* brtable C brtable label OPERATION: Makes local copy of the selector   *)
    (* expression (so original will not be marked as kind=expr) and loads it *)
    (* on the stack. The typeok switch is checked to see if necessary type   *)
    (* conversion has been done. If so, nothing else need be done. If not,   *)
    (* then this is the special case where there is no tree and only a	     *)
    (* branch table. The type is converted, but no store or switch setting   *)
    (* is needed since the selector will never be loaded again. Compare this *)
    (* logic with that in emit. 					     *)
    (*************************************************************************)

  procedure Xemit (
	      A,
	      B : integer;
	      C : integer);

	  var
	    Fattr : Attr;		(* loaded copy of selector	     *)
    begin				(* xemit			     *)
       Fattr := Lattr; 			(* copy selector expression *) 
       Load(Fattr); 			(* put on stack *)
       Genexpr(stak^.tree);
       Popstak;
      /* if not Typeok then (* if first time through *) with     */
      /* Fattr do begin (* must retype the selector *) Locdt := Adtype; (*   */
      /* assume no type change *) if Adtype in [Bdt, Cdt] then begin (*      */
      /* selector bool or char *) Getbounds(Atypep, Tmin, Tmax); if Tmin < 0 */
      /* then Locdt := Jdt else Locdt := Ldt; end {then}; (* selector bool   */
      /* or char *) if Casptrs[1]^.Lowval < 0 then (* isn't pos data type *) */
      /* if Locdt = Ldt then Locdt := Jdt; (* small integers *) if Locdt <>  */
      /* Adtype then Uco2typtyp(Ucvt, Locdt, Adtype) (* do the ucode cvt *)  */
      /* end {with} else Locdt := Fattr.Adtype; (* get the right data type   */
      /* *)								     */
      Ucoxjp(Lattr.Adtype, C, Otherwiselabel, A, B); (* emit the xjp	     *)
    end {procedure Xemit};

    (*************************************************************************)
    (* EMITCASETREE Recursive procedure to emit code for run time branch     *)
    (* tree. PARAMETERS: LOWCASE (CASECTRANGE) index into casptrs for lower  *)
    (* bound of subtree being traversed. HICASE (CASECTRANGE) same for hi    *)
    (* bound. TERMINOLOGY: In refering to the shape of the tree, the	     *)
    (* following conventions apply: the tree is pictured as having its	     *)
    (* leaves at the 'bottom'. Thus a reference to going down the tree means *)
    (* closer to the leaves. The tree consists of case label groupings. The  *)
    (* higher valued case labels are considered to lie to the 'right' of     *)
    (* lower labels. Each subtree contains one or more nodes (entries in     *)
    (* casptrs). The 'root' is the one such group with label values close to *)
    (* the median of those in the subtree. The 'left subtree' is the         *)
    (* (possibly empty) tree containing lower valued labels, and the 'right  *)
    (* subtree' is the (possibly empty) tree containing labels higher than   *)
    (* those in the root. DATA STRUCTURES: At compile time, the tree is      *)
    (* represented by the array castprs. Each entry in the array points to a *)
    (* caseinfo which describes a leaf of the branch tree. These are of      *)
    (* three possible types: single label values (single), subranges of      *)
    (* labels (subr), and branch tables (btable). In the case of branch      *)
    (* tables, a linked list of caseinfos describes the table entries. The   *)
    (* purpose of this procedure is to emit code to do a binary search	     *)
    (* through the values in the casptrs array. The logical tree is thus     *)
    (* traversed by manipulating indicies into the array. As described	     *)
    (* above, any subtree is considered to consist of a left subtree, a      *)
    (* root, and a right subtree. Assume the casptrs indicies spanning the   *)
    (* original subtree are s1 and s2, l1 and l2 for left, r1 and r2 for     *)
    (* right, and root for the root, then the following relationships always *)
    (* hold: l1<=l2, r1<=r2, root=l2+1, root=r1-1 s1=l1, s2=r2 these are the *)
    (* basis of the recursion through the tree. OPERATION: 1) Determine size *)
    (* of this subtree, and of left subtree. 2) If there is exactly one node *)
    (* in this tree, we are completing a 'rightward' descent. Various        *)
    (* special cases are used to save ucode according to the type of this    *)
    (* leaf. There are actually two classes of right descent. This may be    *)
    (* the rightmost leaf in the entire tree. In this case, if the selector  *)
    (* lies above the current node, we execute the otherwise clause. If this *)
    (* is not the rightmost leaf, then the selector lying above this leaf    *)
    (* implies that the only possible hit is on the root of the parent	     *)
    (* (complicated, but that's the way it is). We again save code in some   *)
    (* cases by directly checking the low bound of this parent. 3) There may *)
    (* be exactly two nodes in this tree. In this case the left subtree is   *)
    (* null. We can save some ucode in this case too by directly checking    *)
    (* the low bound on our own root instead of jumping to a non-existant    *)
    (* left subtree. 4) The usual case is more than two nodes in this	     *)
    (* subtree. Recursion proceeds down the right side of the tree in line,  *)
    (* with jumps emited to the left subtrees. Note that the tree actually   *)
    (* consists of the high bounds on the label ranges. Except for the	     *)
    (* special cases noted in (2) and (3) above, all tests are against	     *)
    (* hival. Necessary lowbounds tests are handled by the emitlowtests      *)
    (* procedure, and will follow the ucode for the tree. 5) Following	     *)
    (* recursion down right side of tree, recurse through left subtree.      *)
    (*************************************************************************)

  procedure Emitcasetree (
	      Lowcase,
	      Hicase : Casectrange);

    type
      Treemode = (Empty, Unary, Multi); (* size of a tree		     *)
      Leftrange = 0..Caselements;	(* size range of left subtree	     *)

    var
      Root : Casectrange;		(* center (root) of current tree     *)
      Lefttree : Leftrange;		(* center of left subtree	     *)
      Lefthi : Leftrange;		(* hi end of lefttree		     *)
      Scopeoftree : Treemode;		(* size of supplied tree	     *)
      Scopeoflefttree : Treemode;	(* size of tree to left of root      *)
      Quitlabel : integer;		(* when falling through the right    *)
					(* bottom of a left subtree, this is *)
					(* used to develop the label where   *)
					(* the low test of the parent is to  *)
					(* be done (?!?!?!)		     *)
    begin				(* emitcasetree 		     *)
      Root := Lowcase+((Hicase-Lowcase) div 2); (* center of our tree	     *)
      Lefthi := Root-1; 		(* hi end of left subtree	     *)
      Lefttree := Lowcase+((Lefthi-Lowcase) div 2); (* root of left subtree  *)
      if Hicase = Lowcase then begin	(* set size of current tree	     *)
	Scopeoftree := Unary;
      end else Scopeoftree := Multi;	(* tree has more than one node	     *)
      if Lefthi < Lowcase then begin	(* set size of left subtree	     *)
	Scopeoflefttree := Empty;
      end else if Lefthi = Lowcase then Scopeoflefttree := Unary
      else Scopeoflefttree := Multi;
      (* recurse down the right side of the tree			     *)

      (***********************************************************************)
      (* THIS SUBTREE CONTAINS MORE THAN ONE NODE			     *)
      (***********************************************************************)

      if Scopeoftree = Multi then begin (* this is not unary element subtree *)
					(* multi-element tree		     *)
	(* Normally, we branch out of line on a lessthan or equal compare.   *)
	(* However, some ucode may be saved in the case where the left	     *)
	(* subtree is empty note: this path can only be taken when size of   *)
	(* current tree is 2						     *)
	if Scopeoflefttree = Empty then begin (* special case for unary tree *)
					(* on left			     *)
	  with Casptrs[Root]^ do begin	(* put this here to beat with bug    *)
	    if Cmode = Single then begin (* left tree is null, current root  *)
					(* is single			     *)
	      Emit(Uequ, Lowval);	(* save time and do exact test for   *)
					(* root value			     *)
	      Uco1int(Utjp, Codelabel); (* branch directly to code for root  *)
	    end else begin		(* left tree is null, current is not *)
					(* single			     *)
	      Emit(Uleq, Hival);	(* check if <= current root hi end   *)
	      Ltlabel := Getlabel;	(* assign label for low test. this   *)
					(* will later be emitted as an	     *)
					(* explicite test for subrange, or   *)
					(* be handled by the xjp for btable  *)
	      Uco1int(Utjp, Ltlabel);	(* emit truejump to that test	     *)
	    end;
	  end {with};
	end else begin
	  with Casptrs[Root]^ do begin	(* test and branch to non-empty left *)
					(* subtree			     *)
	    Emit(Uleq, Hival);		(* see if is in left side of current *)
					(* tree 			     *)
	    Casptrs[Lefttree]^.Treelabel := Getlabel; (* assign label for    *)
					(* root of left subtree 	     *)
	    Uco1int(Utjp, Casptrs[Lefttree]^.Treelabel); (* emit jump to     *)
					(* left subtree 		     *)
	  end {with};
	end;				(* end test and branch to non-empty  *)
					(* left subtree 		     *)
	Emitcasetree(Root+1, Hicase);	(* recurse to gen right subtree      *)
      end

(**********************************************************************)
(*								      *)
(*	       THIS SUBTREE CONTAINS EXACTLY ONE NODE		      *)
(*								      *)
(**********************************************************************)

      else begin			(* this is a unary tree 	     *)
	with Casptrs[Root]^ do begin	(* work with the current tree	     *)
	  if Cmode = Single then begin	(* this is not a range type node     *)
	    Emit(Uequ, Lowval); 	(* see if in the range		     *)
	    Uco1int(Utjp, Casptrs[Root]^.Codelabel); (* jump to execute the  *)
					(* code 			     *)
	    if Root = Casecount then begin (* rightmost subtree 	     *)

	      Uco1int(Uujp, Otherwiselabel); (* this value is higher than    *)
					(* highest			     *)
	    end else begin		(* falling through right bottom of a *)
					(* left subtree 		     *)
	      with Casptrs[Root+1]^ do begin (* with parent root right of    *)
					(* this subtree check if in root of  *)
					(* parent			     *)
		case Cmode of		(* what type is parent root?	     *)
		Single : begin		(* parent root is single	     *)
		    Emit(Uequ, Lowval); (* matches parent root? 	     *)
		    Uco1int(Utjp, Codelabel); (* execute it if so	     *)
		    Uco1int(Uujp, Otherwiselabel); (* if not, no match	     *)
		  end {case Single};	(* parent root is single	     *)
		Subr : begin		(* parent root is subrange	     *)
		    Emit(Ugeq, Lowval); (* we know from earlier tests that   *)
					(* it's not above the parent, now    *)
					(* test if it's in the parent        *)
		    Uco1int(Utjp, Codelabel); (* execute it if so	     *)
		    Uco1int(Uujp, Otherwiselabel); (* no others possible     *)
		  end {case Subr};	(* parent root is subrange	     *)
		Btable : begin		(* parent root is branch table	     *)
		    Xemit(Lowval, Hival, Codelabel);
		  end {case Btable}
		end {case};
	      end {with};
	    end;
	  end else begin		(* this is a range type node	     *)
	    if Root = Casecount then begin (* rightmost subtree 	     *)
	      Quitlabel := Otherwiselabel; (* noplace higher than this	     *)
	    end else begin		(* this is a nested subtree handle   *)
					(* nested subtree		     *)
	      Quitlabel := Getlabel;	(* label will be used for low test   *)
					(* of parent tree root		     *)
	      Casptrs[Root+1]^.Ltlabel := Quitlabel;
	    end;			(* handle nested subtree	     *)
	    if Cmode = Subr then begin	(* subrange at right bottom of tree  *)
	      Emit(Uleq, Hival);
	      Uco1int(Ufjp, Quitlabel);
	      Emit(Ugeq, Lowval);
	      Uco1int(Utjp, Codelabel);
	      Uco1int(Uujp, Otherwiselabel);
	    end else begin		(* branch table at right bottom of   *)
					(* tree 			     *)
	      if Root = Casecount then begin (* rightmost subtree	     *)
		Xemit(Lowval, Hival, Codelabel); (* but xjp right in the     *)
					(* tree to save a ujp		     *)
	      end else begin		(* branch table at bottom of nested  *)
					(* tree 			     *)
		Emit(Uleq, Hival);	(* check above range		     *)
		Uco1int(Ufjp, Quitlabel);
		Xemit(Lowval, Hival, Codelabel); (* xjp handles low test     *)
	      end;
	    end;
	  end;
	end {with};
      end;				(* end of unary tree		     *)

      (***********************************************************************)
      (* RECURSE TO EMIT SUBTREES ON LEFT				     *)
      (***********************************************************************)

      if Scopeoflefttree <> Empty then begin (* if necessary, recurse to     *)
					(* emit code for left tree	     *)
	Ucolab(Casptrs[Lefttree]^.Treelabel, 0, 0); (* emit label for tests  *)
					(* which make up left subtree	     *)
	Emitcasetree(Lowcase, Root-1);
      end;
    end {procedure Emitcasetree};

    (*************************************************************************)
    (* EMITBTABLES Procedure to all ujp branch tables OPERATION: 1) Loops    *)
    (* through all entries in the casptrs array to see which are for branch  *)
    (* tables. 2) Each branch table is represented by a linked list. This    *)
    (* list is traversed and the necessary ujps are emitted into the branch  *)
    (* table.								     *)
    (*************************************************************************)

  procedure Emitbtables;

    var
      Cindex : Casectrange;		(* runs through array entries	     *)
      Clist : Cip;			(* traverses linked list for btable  *)
      Cmin : integer;			(* value for entry to be emitted     *)
					(* next 			     *)
      I : integer;			(* loop var for small loops	     *)

    begin				(* emitbtables			     *)
      for Cindex := 1 to Casecount do begin (* loop through all array	     *)
					(* entries			     *)
	if Casptrs[Cindex]^.Cmode = Btable then begin (* this is a branch    *)
					(* table. emit it		     *)
	  with Casptrs[Cindex]^ do begin (* mother entry for whole btable    *)
					(* set up for this btable	     *)
	    Codelabel := Getlabel;	(* assign label for the btable	     *)
	    Cmin := Lowval;		(* set starting value for this table *)
	    Clist := Next;		(* pick up first entry in table      *)
	    Uco2intint(Uclab, Codelabel, Hival-Lowval+1); (* emit the label  *)
					(* for the table		     *)
	  end {with};			(* end set up for this btable	     *)
	  while Clist <> nil do begin	(* loop through entries for this     *)
					(* table			     *)
	    with Clist^ do begin	(* use current link list entry emit  *)
					(* ujps for this list entry	     *)
	      while Lowval > Cmin do begin (* emit for missing labels	     *)
		Uco1int(Uujp, Otherwiselabel);
		Cmin := Cmin+1;
	      end {while};		(* emit for missing labels	     *)
	      for I := Lowval to Hival do begin (* cover whole subrange      *)
		Uco1int(Uujp, Codelabel); (* branch table ujp		     *)
	      end {for};
	      Cmin := Cmin+1+Hival-Lowval; (* allow for emitted entries      *)
	      Clist := Next;		(* follow the chain		     *)
	    end {with};
	  end {while};
	end;
      end {for};
    end {procedure Emitbtables};

    (*************************************************************************)
    (* EMITLOWTESTS When the branch tree is emitted, out of line branches    *)
    (* are used to check the low bounds for certain cases. This routine      *)
    (* emits the code necessary to check those lower bounds.		     *)
    (*************************************************************************)

  procedure Emitlowtests;

    var
      I : integer;			(* loop counter 		     *)

    begin				(* emitlowtests 		     *)
      for I := 1 to Casecount do begin	(* loop through all cases	     *)
	with Casptrs[I]^ do begin	(* using this tree node 	     *)
	  if Ltlabel <> Unusedlab then begin (* needs a low test	     *)
	    Ucolab(Ltlabel, 0, 0);	(* emit the label on this test	     *)
	    case Cmode of
	    Single : begin		(* single			     *)
		Emit(Uequ, Lowval);
		Uco1int(Utjp, Codelabel);
		Uco1int(Uujp, Otherwiselabel);
	      end {case Single};	(* single			     *)
	    Subr : begin		(* subrange			     *)
		Emit(Ugeq, Lowval);
		Uco1int(Utjp, Codelabel);
		Uco1int(Uujp, Otherwiselabel);
	      end {case Subr};
	    Btable : Xemit(Lowval, Hival, Codelabel);
	    end {case};
	  end;
	end {with};
      end {for};
    end {procedure Emitlowtests};

    (*************************************************************************)
    (* OTHERWISESTMT Handle otherwise clause, or default it OPERATION: 1) If *)
    (* otherwise clause is present, assign and emit a label, then parse the  *)
    (* body. 2) If not, assign the label and emit a cup to the standard      *)
    (* procedure which handles the error.				     *)
    (*************************************************************************)

  procedure Otherwisestmt;

    var
      Pcount,i : integer; 		(* parameter count		     *)
      cppfileattr: attr;

    begin				(* otherwisestmt		     *)
      Otherwiselabel := Getlabel;	(* allocate label for clause	     *)
      Ucolab(Otherwiselabel, 0, 0);	(* emit the label		     *)
      if Sy = Otherwisesy then begin	(* otherwise is present 	     *)
	Insymbol;			(* skip the word otherwise	     *)
	if Sy = Colonsy then Insymbol
	else Error(151);
	Statement(Fsys, Statends);	(* parse the body		     *)
	if Sy = Semicolonsy then Insymbol; (* allow sloppy semicolon before  *)
					(* end				     *)
      end else begin			(* otherwise not present no	     *)
					(* otherwise clause		     *)
	Stdcallinit(Pcount);		(* prepare to call std proc.	     *)
	Uco3intval(Uldc, Ldt, Intsize, Curpage);
	Par(Ldt, Pcount);
	Uco3intval(Uldc, Ldt, Intsize, Curline);
	Par(Ldt, Pcount);

	with cppfileattr do begin
	  Cval.ival := Fnln(cppfilename);
	  Adtype := Mdt;
	  Asize := Cval.ival * bytesize;
	  new1(Cval.chars);
	  for i := 1 to Cval.ival do
	    Cval.chars^.ss[i] := cppfilename[i];
	  end;

	Uco1attr(Ulca, cppfileattr);
	Par(Ldt, Pcount);
	Uco3intval(Uldc, Ldt, Intsize, cppfileattr.Cval.ival);
	Par(Ldt, Pcount);
	Support(Caseerror);		(* call error routine		     *)
	Genexpr(stak^.tree);
	Popstak;
      end;				(* no otherwise clause		     *)
      Uco1int(Uujp, Outlabel);		(* branch around testing code	     *)
    end {procedure Otherwisestmt};

    (*************************************************************************)
    (* CODE FOR PROCESSING CASESTATEMENT				     *)
    (*************************************************************************)

  begin 				(* casestatement		     *)
    Caseinit;				(* initialize our variables	     *)
    Outlabel := Getlabel;		(* label for case complete	     *)
    Caseselector;			(* emit code to put selector value   *)
					(* in a temp			     *)
    if Sy = Ofsy then begin		(* make sure word 'of' follows       *)
					(* selector			     *)
      Insymbol;
    end else Error(160);		(* missing 'of'                      *)
    Entrylabel := Getlabel;		(* get a label for start of test     *)
					(* code 			     *)
    Uco1int(Uujp, Entrylabel);		(* emit jump around individual cases *)
					(* to the testing code		     *)

(*..................................................................)
(.								   .)
(.    LOOP THROUGH ALL OF THE CASE LIST ELEMENTS SETTING UP	   .)
(.    CASEINFO TO DESCRIBE THEIR LABELS AND EMITTING THE CODE	   .)
(.    FOR THEIR CLAUSES 					   .)
(.								   .)
(..................................................................*)


    Loopdone := false;
    repeat				(* loop through all of the case list *)
					(* elements			     *)
      Caselistelement;			(* parse one list element	     *)
      if Sy = Semicolonsy then Insymbol (* skip terminating semicolon	     *)
      else begin			(* no semicolon 		     *)
	Loopdone := true;		(* can't parse another list element  *)
      end;				(* since there is no separating      *)
					(* semicolon			     *)
    until (Sy in Fsys+Statends+[Otherwisesy]) or Loopdone;


(*..................................................................)
(.								   .)
(.     ALL CASELIST-ELEMENTS, AND POSSIBLE TRAILING SEMICOLON	   .)
(.     HAVE BEEN PARSED.  THIS IS FOLLOWED BY AN OPTIONAL OTHERWISE.)
(.     PSEUDO CASE LABEL, A POSSIBLE SLOPPY ;, AND AN END.	   .)
(.								   .)
(..................................................................*)


    Otherwisestmt;			(* handle (possibly missing)	     *)
					(* otherwise			     *)
    if Sy = Endsy then Insymbol 	(* parse the end		     *)
    else Error(163);			(* if not, a mistake has been made   *)
    if Listanchor <> nil then begin	(* there are tests to emit	     *)
      Arrangecasetree;			(* calculate 'optimal' space time    *)
					(* tradeoff between branch trees and *)
					(* branch tables		     *)
      Emitbtables;			(* emit the ujp tables used by any   *)
					(* xjps which may have been emitted  *)
      Ucolab(Entrylabel, 0, 0); 	(* label for decision code	     *)
      Emitcasetree(1, Casecount);	(* emit the ucode to decide which    *)
					(* case has actually been hit	     *)
      Emitlowtests;			(* branch tree may ruequire code to  *)
					(* check low bounds of some cases.   *)
					(* Emit it			     *)
    end;				(* there are tests to emit	     *)
    if Lstamp <> 0 then Freetemps(Lstamp); (* free all temporaries *)     
    Ucolab(Outlabel, 0, 0);		(* emit the all done label	     *)
  end {procedure Casestatement};
