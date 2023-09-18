{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upastree.p,v 1030.7 88/02/18 14:55:24 bettina Exp $ }

#include "upasglob.h"
#include "cmplrs/uwri.h"
#include "upasutil.h"
#include "upaslex.h"
#include "upasuco.h"
#include "upastree.h"
#include "upasfold.h"
#include "allocator.h"

procedure Pushstak (*
	    i : pttreerec *);
  (* push an item on the simulated Ucode stack				     *)
  var
    ptr : ptstakrec;
  begin
    if stak^.prev = nil then begin
      new1(ptr);
      ptr^.next := stak;
      ptr^.prev := nil;
      stak^.prev := ptr;
    end;
    stak := stak^.prev;
    stak^.tree := i;
  end {procedure Pushstak};

#if 0	/* use Macro */
procedure Popstak (* : pttreerec *);
  begin
    if errorcount = 0 then begin
      stak := stak^.next;
    end;
  end {function Popstak};
#endif

procedure Swapstak;
  var
    temp : pttreerec;
  begin
    if errorcount = 0 then begin
      temp := stak^.tree;
      stak^.tree := stak^.next^.tree;
      stak^.next^.tree := temp;
    end;
  end {procedure Swapstak};

function Gettreenode (* : pttreerec *);
  (* get a new tree node						     *)
  var
    tnode : pttreerec;
  begin
    new1(tnode);
    (* clear fields in node						     *)
    with tnode^ do begin
      l := nil;
      r := nil;
      isbool := false;
    end {with};
    Gettreenode := tnode;
  end {function Gettreenode};


(* the 3 tree-building routine *)
procedure Leafnode;
  var
    curtree : pttreerec;
  begin
    curtree := Gettreenode;
    curtree^.U := U;
    Pushstak(curtree);
  end {procedure Leafnode};

procedure Unarynode;
  var
    curtree : pttreerec;
  begin
    if errorcount = 0 then begin
      if (U.Opc in [Ucvt, Ucvtl, Unot, Ulnot, Usqr, Uneg, Uabs, Uodd, Uinc, Udec])
	  and is_constant(stak^.tree)
	  and fold(U, stak^.tree, nil) then begin
	;
      end else if (U.Opc in [Ucvt, Uneg, Uabs])
	  and is_float_constant(stak^.tree)
	  and float_fold(U, stak^.tree, nil) then begin
	;
      end else begin
        curtree := Gettreenode;
        curtree^.U := U;
        curtree^.l := stak^.tree;
        stak^.tree := curtree;
      end;
    end;
  end {procedure Unarynode};

procedure Binarynode;
  var
    curtree : pttreerec;
    ltree : pttreerec;
    rtree : pttreerec;
  begin
    if errorcount = 0 then begin
      rtree := stak^.tree; Popstak;
      ltree := stak^.tree;
      if (U.Opc in [Uadd, Usub, Umpy, Udiv, Umod, Uand, Uior, Uxor, Ushl,
	  Ushr, Ugeq, Ugrt, Uleq, Ules, Uequ, Uneg, Umin, Umax])
	  and is_constant(ltree) and is_constant(rtree)
	  and fold(U, ltree, rtree) then begin
	stak^.tree := ltree;
      end else begin
	curtree := Gettreenode;
	curtree^.U := U;
	curtree^.r := rtree;
	curtree^.l := ltree;
	stak^.tree := curtree;
      end;
    end;
  end {procedure Binarynode};

function Duplicatetree (* (root: pttreerec): pttreerec *);
(* duplicate the tree and return the resulting root; used in while statement *)
  var tnode: pttreerec;
  begin
  if errorcount = 0 then begin
    tnode := Gettreenode;
    tnode^ := root^;
    if root^.l <> nil then begin
      tnode^.l := Duplicatetree(root^.l);
      if root^.r <> nil then 
        tnode^.r := Duplicatetree(root^.r);
      end;
    end;
  Duplicatetree := tnode;
  end {procedure Duplicatetree};

procedure Getatreetemp (
	    dty : Datatype;
	var tempnum : integer);
(* reserves a temporary location for an intermediate result	     *)
(* corresponding to the type dty; returns the index of the temporary *)
(* in the Treetemps table.					     *)
  label
    12;
  var
    i, tempsize, tempalign : integer;
  begin
    if dty = Qdt then begin
      tempsize := Doublesize;
      tempalign := Doublealign;
    end else begin
      tempsize := Wordsize;
      tempalign := Wordalign;
    end;
    for i := 1 to Treetempcount do begin
      with Treetemps[i] do begin
	if free and (size = tempsize) and (align = tempalign) and (dtype = dty) then begin
	  tempnum := i;
	  goto 12;
	end;
      end {with};
    end {for};
    (* no free temps; create a new one					     *)
    if Treetempcount = Maxtemps then begin
      Error(171);			(* Compiler error		     *)
    end else begin
      Treetempcount := Treetempcount+1;
    end;
    with Treetemps[Treetempcount] do begin
      size := tempsize;
      align := tempalign;
      dtype := dty;
      offset := Assignnextmemoryloc(Mmt, tempsize, tempalign);
      Ucomem(Uvreg, dty, Mmt, Memblock, offset, tempsize);
    end {with};
    tempnum := Treetempcount;
12 :
    Treetemps[tempnum].free := false;
  end {procedure Getatreetemp};

function Isboolexpr (* (
	   root : pttreerec)
   : boolean *);
(* see if the tree pointed to by root needs to be processed by short-circuits *)
  begin
    if errorcount = 0 then begin
      with root^ do begin
	if not isbool then begin
	  Isboolexpr := false;
	end else if U.Opc in [Uand, Uior] then begin
	  Isboolexpr := true;
	end else begin			(* it is an lnot		     *)
	  Isboolexpr := Isboolexpr(l);
	end;
      end {with};
    end;
  end {function Isboolexpr};

function Startwithor (* (
	   root : pttreerec)
   : boolean *);
(* for a boolean expression, check if the first non-not is an OR *)
  var
    toggled : boolean;
  begin
    if errorcount = 0 then begin
      toggled := false;
      while root^.U.Opc = Ulnot do begin
	toggled := not toggled;
	root := root^.l;
      end {while};
      if toggled then begin
	Startwithor := root^.U.Opc = Uand;
      end else begin
	Startwithor := root^.U.Opc = Uior;
      end;
    end;
  end {function Startwithor};

procedure Exprprepass (*
	    root : pttreerec *);
  var
    Lattr : Attr;
    exitlab : integer;
  begin
    if errorcount = 0 then begin
      with root^ do begin
	if U.Opc in [Ucup, Uicuf] then begin
	  Exprprepass(l);		(* prepass the parameter list	     *)
	  Genexpr(l);
	  if U.Opc = Uicuf then begin
	    Genexpr(r);
	  end;
	  Ubittobyte(U); Uwrite(U);
	  (* if function, store into temporary				     *)
	  if U.dtype <> Pdt then begin
	    (* get a temporary						     *)
	    Getatreetemp(U.dtype, tmp);
	    {load T memory}
	    U.Opc := Ulod;
	    U.Mtype := Rmt;
	    U.I1 := 0;
	    if U.dtype in [Qdt, Rdt] then
	      U.offset := fpRmtoffset
	    else U.offset := intRmtoffset;
	    U.Length := Treetemps[tmp].size;
	    U.Lexlev := 0;
	    Ubittobyte(U); Uwrite(U);
	    (* fabricate the str instruction				     *)
	    U.Opc := Ustr;
	    U.Mtype := Mmt;
	    U.I1 := Memblock;
	    U.offset := Treetemps[tmp].offset;
	    U.Length := Treetemps[tmp].size;
	    U.Lexlev := 0;
	    Ubittobyte(U); Uwrite(U); 
	    {this U to be used again}
	    U.offset := Treetemps[tmp].offset;
	    U.Length := Treetemps[tmp].size;
	  end;
	end else if isbool and Isboolexpr(root) then begin
	  (* get a temporary						     *)
	  Getatreetemp(Jdt, tmp);
	  (* fabricate the attr record					     *)
	  with Lattr do begin
	    Amty := Mmt;
	    Dplmt := Treetemps[tmp].offset;
	    Asize := Treetemps[tmp].size;
	    Adtype := Jdt;
	    Ablock := Memblock;
	  end {with};
	  Lastuclabel := Lastuclabel+1;
	  exitlab := Lastuclabel;
	  Strboolexpr(root, false, nil, Lattr, exitlab, Startwithor(root),
	      exitlab);
	  Ucolab(exitlab, 0, 0);
	  (* fabricate the str instruction to indicate to Genexpr that tree  *)
	  (* has been evaluated 					     *)
	  U.Opc := Ustr;
	  U.Mtype := Mmt;
	  U.I1 := Memblock;
	  U.offset := Treetemps[tmp].offset;
	  U.Length := Treetemps[tmp].size;
	  U.Lexlev := 0;
	end else if l <> nil then begin
	  Exprprepass(l);
	  if r <> nil then begin
	    Exprprepass(r);
	  end;
	end;
      end {with};
    end;
  end {procedure Exprprepass};

procedure Genexpr (*
	    root : pttreerec *);
(* the final pass to generate the actual expression code;
   if it is a STR, the expression has been saved in a temporary in the pre-pass
   phase - change it to LOD and free the temp *)
  begin
    if errorcount = 0 then begin
      with root^ do begin
	if U.Opc = Ustr then begin
	  U.Opc := Ulod;
	  Treetemps[tmp].free := true;
	end else if l <> nil then begin
	  Genexpr(l);
	  if r <> nil then begin
	    Genexpr(r);
	  end;
	end;
      end {with};
      if (root^.U.Opc = Upar) and (root^.U.mtype = Rmt) then 
	root^.U.Opc := Ustr;
      with root^ do begin
        Ubittobyte(U); Uwrite(U);
	end;
      if (root^.U.Opc in [Ucup, Uicuf]) and (root^.U.dtype <> Pdt) then begin
	{load T memory}
	U.Opc := Ulod;
	U.Mtype := Rmt;
	U.Dtype := root^.U.dtype;
	U.I1 := 0;
	if root^.U.dtype in [Qdt, Rdt] then 
	  U.offset := fpRmtoffset
	else U.offset := intRmtoffset;
	if root^.U.dtype = Qdt then
	  U.Length := Doublesize
	else U.Length := Wordsize;
	U.Lexlev := 0;
	Ubittobyte(U); Uwrite(U);
	end;
    end;
  end {procedure Genexpr};

procedure Jumpboolexpr (*
	    root : pttreerec;
	    isfjp : boolean;
	    exitlab,
	    altlab : integer *);
(* root points to a boolean expression; this generates a fjp to the exitlab if
   isfjp is true, a tjp to the exitlab otherwise;  if altlab is not 0, it is
   the jump target of the otherwise case *)
  var
    otherlab : integer;
  begin
    if errorcount = 0 then begin
      with root^ do begin
	if not isbool then begin
	  if root^.U.Opc in [Ucup, Uicuf] then begin
	    Exprprepass(root^.l);
	  end else begin
	    Exprprepass(root);
	  end;
	  Genexpr(root);
	  if isfjp then begin
	    Uco1int(Ufjp, exitlab);
	  end else begin
	    Uco1int(Utjp, exitlab);
	  end;
	end else if U.Opc = Ulnot then begin
	  Jumpboolexpr(l, not isfjp, exitlab, altlab);
	end else if (U.Opc = Uand) and isfjp or (U.Opc = Uior)
	 and not isfjp then begin
	  (* AND, OR							     *)
	  Jumpboolexpr(l, isfjp, exitlab, 0);
	  Jumpboolexpr(r, isfjp, exitlab, altlab);
	end else begin
	  if altlab = 0 then begin
	    Lastuclabel := Lastuclabel+1;
	    otherlab := Lastuclabel;
	  end else begin
	    otherlab := altlab;
	  end;
	  Jumpboolexpr(l, not isfjp, otherlab, 0);
	  Jumpboolexpr(r, isfjp, exitlab, otherlab);
	  if altlab = 0 then begin
	    Ucolab(otherlab, 0, 0);
	  end;
	end;
      end {with};
    end;
  end {procedure Jumpboolexpr};

procedure Strboolexpr (*
	    root : pttreerec;
	    notted : boolean;
	    lhstree : pttreerec;	/* for isst only */
	var Fattr : Attr;
	    exitlab : integer;
	    exitwhentrue : boolean;
	    altlab : integer *);
(* root points to a boolean expression; this generates the code to store the
   value of the boolean expression into the lhs pointed to by lhstree; if
   notted is true, the logical not of the boolean is stored into the temp
   instead; exitlab gives the label to jump to if the value of the left
   subtree is known to be true or false according to whether exitwhentrue
   is true or false; if altlab is not 0, it is the other jump target;
   Fattr is the Attr of the lhs store target; if lhstree is nil, it is a STR,
   else it is a ISST *)
  var
    otherlab : integer;
    U1 : Bcrec;
  begin
    if errorcount = 0 then begin
      with root^ do begin
	if not isbool then begin
	  if root^.U.Opc in [Ucup, Uicuf] then begin
	    Exprprepass(root^.l);
	  end else begin
	    Exprprepass(root);
	  end;
	  if lhstree <> nil then begin
	    Genexpr(lhstree);
	  end;
	  Genexpr(root);
	  if notted then begin
	    U1.Opc := Ulnot;
	    U1.dtype := Jdt;
	    U1.lexlev := 0;
	    Ubittobyte(U1); Uwrite(U1);
	  end;
	  if lhstree = nil then begin
	    Uco1attr(Ustr, Fattr);
	  end else begin
	    Uco1attr(Uisst, Fattr);
	  end;
	end else if U.Opc = Ulnot then begin
	  Strboolexpr(l, not notted, lhstree, Fattr, exitlab, exitwhentrue,
	      altlab);
	end else begin			(* AND, OR			     *)
	  if notted then begin
	    if U.Opc = Uand then begin
	      U.Opc := Uior;
	    end else begin
	      U.Opc := Uand;
	    end;
	  end;
	  (* create the record for the LOD				     *)
	  U1.Opc := Ulod;
	  U1.dtype := Fattr.Adtype;
	  U1.Mtype := Fattr.Amty;
	  U1.I1 := Fattr.Ablock;
	  U1.offset := Fattr.Dplmt;
	  U1.Length := Fattr.Asize;
	  U1.Lexlev := 0;
	  if (U.Opc = Uand) and not exitwhentrue or (U.Opc = Uior)
	   and exitwhentrue then begin
	    Strboolexpr(l, notted, lhstree, Fattr, exitlab, exitwhentrue, 0);
	    Ubittobyte(U1); Uwrite(U1); (* write the LOD		     *)
	    if U.Opc = Uand then begin
	      Uco1int(Ufjp, exitlab);
	    end else begin
	      Uco1int(Utjp, exitlab);
	    end;
	    Strboolexpr(r, notted, lhstree, Fattr, exitlab, exitwhentrue,
		altlab);
	  end else begin
	    if altlab = 0 then begin
	      Lastuclabel := Lastuclabel+1;
	      otherlab := Lastuclabel;
	    end else begin
	      otherlab := altlab;
	    end;
	    Strboolexpr(l, notted, lhstree, Fattr, otherlab,
		not exitwhentrue, 0);
	    Ubittobyte(U1); Uwrite(U1); (* write the LOD		     *)
	    if U.Opc = Uand then begin
	      Uco1int(Ufjp, otherlab);
	    end else begin
	      Uco1int(Utjp, otherlab);
	    end;
	    Strboolexpr(r, notted, lhstree, Fattr, exitlab, exitwhentrue,
		otherlab);
	    if altlab = 0 then begin
	      Ucolab(otherlab, 0, 0);
	    end;
	  end;
	end;
      end {with};
    end;
  end {procedure Strboolexpr};
