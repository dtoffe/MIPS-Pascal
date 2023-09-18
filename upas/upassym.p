{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upassym.p,v 1030.7 88/02/18 14:55:26 bettina Exp $ }


{-----------------------------------------------------------------------------}
{									      }
{Change History:						              }
{									      }
{#0001	larry	12/20/86	check for not going past end of a name        }
{							     		      }
{-----------------------------------------------------------------------------}

#include "upasglob.h"
#include "upassym.h"
#include "allocator.h"
type
  { record for remembering pointer types with corresponding aux entries that
    are to be updated after Resolvepointers is called }
  ptpointerrec = ^pointerrec;
  pointerrec = record
		ifd,
		iaux: integer; {gives the entry that needs an RNDXR}
		ptrtype: Strp; {point to the structure record of pointer type}
		next: ptpointerrec;
		end;
var
  headpointers: ptpointerrec; {head of list of pointerrec}
  auxnums: array[btNil..btMax] of integer;

procedure Syminit;
  begin
#if 0
    new1(maptop);
    maptop^.next := nil; maptop^.prev := nil;
    mapbottom := maptop;
#endif
    st_cuinit;
    headpointers := nil;
  end {procedure Syminit};

procedure st_feinit;
  (* called from st_filebegin *)
  var
    bt : integer;
  begin
#if 0
    if maptop^.prev = nil then begin
      new1(maptop^.prev);
      maptop^.prev^.next := maptop;
      maptop := maptop^.prev;
      maptop^.prev := nil;
      end
    else maptop := maptop^.prev;
    with maptop^ do begin
      cppname := cppfilename;
    end {with};
#endif
    if not debugging_symbols then return;
    auxnums[btAdr] :=st_auxbtadd(btAdr);
    auxnums[btChar] :=st_auxbtadd(btChar);
    auxnums[btInt] :=st_auxbtadd(btInt);
    auxnums[btUInt] :=st_auxbtadd(btUInt);
    auxnums[btFloat] :=st_auxbtadd(btFloat); 
    auxnums[btDouble] :=st_auxbtadd(btDouble);
  end {procedure st_feinit};

procedure Popbtmap;
  (* called when calling st_fileend to pop the typemap stack *)
  begin
#if 0
  maptop := maptop^.next;
#endif
  end {Popbtmap};

procedure Addnullfilename (*
	var s : Filename *);
  var
    i : integer;
  begin
    i := 1;
    while (i <= filenamelen) and (s[i] <> ' ') do begin  	{#0001}
      st_str[i] := s[i];
      i := i+1;
    end {while};
    st_str[i] := chr(0);
  end {procedure Addnullfilename};

procedure Addnullident(var s: Identname);
  var
    i : integer;
  begin
    i := 1;
    while (i <= Identlength) and (s[i] <> ' ') do begin	{#0001}
      st_str[i] := s[i];
      i := i+1;
    end {while};
    st_str[i] := chr(0);
  end {procedure Addnullident};


function Symaddstr (* (
	   idname : Identname): integer *);
  begin
    Addnullident(idname);
    Symaddstr := st_stradd(st_str);
  end {Symaddstr};

function Symaddextstr (* (
	   idname : Identname): integer *);
  begin
    Addnullident(idname);
    Symaddextstr := st_extstradd(st_str);
  end {Symaddextstr};

function Typetoaux (* (
       typeptr: Strp; replicate, auxneeded, needpack, noneedsamefile: boolean):
     integer *);
  {if needpack is true, create entry for packed version and use PackTypendx and
   packifd fields}
  {if replicate is true, must create a new aux entry and must not set typendx
   field; in that case, ifd field is set to -2 if it is -1, not touched 
   otherwise}
  {if auxneeded is false, do not need to create aux table entry (only for
   records and enumerated types), in which case, ifd field is set to -2; 
   if not record or enumerated type, this auxneeded flag is not checked; 
   auxneeded is true only when called from Typedeclaration for record and 
   enumerated types}
  var iaux, baseiaux, isym, sc: integer;
      junk: integer;
      Lidp: Idp;
      aptr: ptpointerrec;
      sametypecount: integer;  {count the number of case labels for a given 
				variant}

  procedure Processvariant(tagp: Strp);
    var
      sc: integer;
      junk: integer;
      varp, varp1: Strp;
      Lidp: Idp;
      variant_isym: integer;
      tagtypeptr: strp;
      iaux: integer;
      tagpacked: boolean;	{if the tag field is packed}
    begin
    if tagp^.Form = Tagfwithid then 
      with tagp^.Tagfieldp^ do begin {the tag field}
	{Klass must be Field}
        tagtypeptr := Idtype;
	tagpacked := Inpacked and 
	   (((tagtypeptr^.form = Scalar) and (tagtypeptr^.scalkind = Declared)) 
	    or (tagtypeptr^.form = Subrange) or (tagtypeptr^.form = Power));
	sc := scInfo;
	symndx := st_symadd(Symaddstr(Idname), Fldaddr,
		    stMember, sc, Typetoaux(Idtype, false, true, tagpacked, false));
	variant_isym := symndx;
	end {with}
    else begin
      tagtypeptr := tagp^.Tagfieldtype;
      tagpacked := false;
      variant_isym := st_symadd(0, 0, stTypedef,
			  scInfo, Typetoaux(tagtypeptr, false, true, false, false));
      end;
    junk := st_blockbegin(0, variant_isym, scVariant);
    {loop for each variant}
    varp := tagp^.Fstvar;
    while varp <> nil do
      begin
      sametypecount := 0;
      varp1 := varp;
      repeat
	sametypecount := sametypecount + 1;
	varp1 := varp1^.Nxtvar;
      until (varp1 = nil) or (varp1^.Varfirstfield <> varp^.Varfirstfield);
      
      iaux := st_auxadd(sametypecount);
      varp1 := varp;
      repeat
	if tagpacked then
          junk := st_auxrndxadd(tagtypeptr^.packifd, tagtypeptr^.packtypendx)
        else junk := st_auxrndxadd(tagtypeptr^.ifd, tagtypeptr^.typendx);
        junk := st_auxadd(varp1^.varval);
        junk := st_auxadd(varp1^.varval);
	varp1 := varp1^.Nxtvar;
      until (varp1 = nil) or (varp1^.Varfirstfield <> varp^.Varfirstfield);

      junk := st_blockbegin(0, iaux, scInfo);
      Lidp := varp^.Varfirstfield;
      while Lidp <> nil do begin
#if 0
	if Lidp^.Inpacked then
	  sc := scBits
	else 
#endif
	sc := scInfo;
	Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), Lidp^.Fldaddr,
	    stMember, sc, Typetoaux(Lidp^.Idtype, false, true, Lidp^.Inpacked, false));
	Lidp := Lidp^.next;
        end {while}; 
      if varp^.Subvar <> nil then 
	Processvariant(varp^.Subvar);
      junk := st_blockend(iaux);
      varp := varp1;
      end {while};
    junk := st_blockend(variant_isym);
    end {Processvariant};

  begin
#ifdef duplicateauxes
    replicate := true;
#endif
    if Errorcount <> 0 then
      return
    else if not debugging_symbols then
      Typetoaux := indexNil
    else if (typeptr^.Form = Scalar) and (typeptr^.Scalkind = Standrd) then 
      begin
      typeptr^.ifd := st_currentifd;
      if replicate then
	Typetoaux := st_auxbtadd(typeptr^.bt)
      else begin
	typeptr^.typendx := auxnums[typeptr^.bt];
        Typetoaux := typeptr^.typendx;
	end;
      end
    else {enter type in symbol table file}
      case typeptr^.Form of
      Scalar: 
	begin {Scalkind must be Declared} 
	if typeptr^.ifd = -1 then 
	  begin
	  typeptr^.scalaridn := st_blockbegin(0, typeptr^.Dimension+1, scInfo);
	  Lidp := typeptr^.Fconst;
	  while Lidp <> nil do begin
	    Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), Lidp^.ival,
				  stMember, scInfo, indexNil);
	    Lidp := Lidp^.next;
	    end {while};
	  junk := st_blockend(typeptr^.Dimension+1);
	  typeptr^.ifd := -2; {to indicate sym entry created but not aux entry}
	  typeptr^.packifd := -2;
	  end;
	if not auxneeded then return;
	if needpack then begin
	  if replicate or 
	   not noneedsamefile and (typeptr^.packifd <> st_currentifd) then begin
	    iaux := st_auxbtadd(btEnum);
	    if not replicate then begin {if replicate, no need set fields}
	      typeptr^.packifd := st_currentifd;
	      typeptr^.PackTypendx := iaux;
	      end;
	    if typeptr^.packsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.packsize);
	    junk := st_auxrndxadd_idn(typeptr^.scalaridn);
	    end
	  else iaux := typeptr^.PackTypendx;
	  end
	else begin
	  if replicate or 
	     not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	    iaux := st_auxbtadd(btEnum);
	    if not replicate then begin {if replicate, no need set fields}
	      typeptr^.ifd := st_currentifd;
	      typeptr^.typendx := iaux;
	      end;
	    if typeptr^.stsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.stsize);
	    junk := st_auxrndxadd_idn(typeptr^.scalaridn);
	    end
	  else iaux := typeptr^.typendx;
	  end;
	Typetoaux := iaux;
	end;
      Subrange: begin
	if needpack then begin
	  if replicate or 
	   not noneedsamefile and (typeptr^.packifd <> st_currentifd) then begin
	    {take care of the host type}
	    baseiaux := Typetoaux(typeptr^.Hosttype, false, true, false, true);

	    iaux := st_auxbtadd(btRange);
	    if not replicate then begin
	      typeptr^.packifd := st_currentifd;
	      typeptr^.packtypendx := iaux;
	      end;
	    if typeptr^.packsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.packsize);
	    junk := st_auxrndxadd(typeptr^.Hosttype^.ifd, baseiaux);
	    junk := st_auxadd(typeptr^.Vmin);
	    junk := st_auxadd(typeptr^.Vmax);
	    end
	  else iaux := typeptr^.packtypendx;
	  end
	else begin
	  if replicate or 
	     not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	    {take care of the host type}
	    baseiaux := Typetoaux(typeptr^.Hosttype, false, true, false, true);

	    iaux := st_auxbtadd(btRange);
	    if not replicate then begin
	      typeptr^.ifd := st_currentifd;
	      typeptr^.typendx := iaux;
	      end;
	    if typeptr^.stsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.stsize);
	    junk := st_auxrndxadd(typeptr^.Hosttype^.ifd, baseiaux);
	    junk := st_auxadd(typeptr^.Vmin);
	    junk := st_auxadd(typeptr^.Vmax);
	    end
	  else iaux := typeptr^.typendx;
	  end;
	Typetoaux := iaux;
	end;
      Power: begin
	if needpack then begin
	  if replicate or 
	   not noneedsamefile and (typeptr^.packifd <> st_currentifd) then begin
	    {take care of the host type}
	    baseiaux := Typetoaux(typeptr^.Basetype, false, true, false, true);

	    iaux := st_auxbtadd(btSet);
	    if not replicate then begin
	      typeptr^.packifd := st_currentifd;
	      typeptr^.packtypendx := iaux;
	      end;
	    if typeptr^.packsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.packsize);
	    junk := st_auxrndxadd(typeptr^.Basetype^.ifd, baseiaux);
	    end
	  else iaux := typeptr^.packtypendx;
	  end
	else begin
	  if replicate or 
	     not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	    {take care of the host type}
	    baseiaux := Typetoaux(typeptr^.Basetype, false, true, false, true);

	    iaux := st_auxbtadd(btSet);
	    if not replicate then begin
	      typeptr^.ifd := st_currentifd;
	      typeptr^.typendx := iaux;
	      end;
	    if typeptr^.stsize < Wordsize then
	      junk := st_auxbtsize(iaux, typeptr^.stsize);
	    junk := st_auxrndxadd(typeptr^.Basetype^.ifd, baseiaux);
	    end
	  else iaux := typeptr^.typendx;
	  end;
	Typetoaux := iaux;
	end;
      SPointer: if (typeptr = Addressptr) or (typeptr = Nilptr) then begin
          typeptr^.ifd := st_currentifd;
          if replicate then
	    Typetoaux := st_auxbtadd(btAdr)
          else begin
	    typeptr^.typendx := auxnums[btAdr];
            Typetoaux := typeptr^.typendx;
	    end;
          end
	else begin
	  if replicate or 
	     not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	    {take care of the host type}
	    if typeptr^.Eltype <> nil then 
	      baseiaux := Typetoaux(typeptr^.Eltype, false, true, false, true);
  
	    iaux := st_auxbtadd(btIndirect);
	    if not replicate then begin
	      typeptr^.ifd := st_currentifd;
	      typeptr^.typendx := iaux;
	      end;
            st_shifttq(iaux, tqPtr);
	    if typeptr^.Eltype <> nil then 
	      junk := st_auxrndxadd(typeptr^.Eltype^.ifd, baseiaux)
	    else begin
	      {type definition of pointed-to type not yet seen by compiler}
	      new1(aptr);
	      aptr^.iaux := st_auxrndxadd(-1, -1);
	      aptr^.ifd := st_currentifd;
	      aptr^.ptrtype := typeptr;
	      aptr^.next := headpointers;
	      headpointers := aptr;
	      end;
	    end
	  else iaux := typeptr^.typendx;
	  Typetoaux := iaux; 
	  end;
      Arrays: begin
	if replicate or 
	   not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	  {take care of the element type}
	  baseiaux := Typetoaux(typeptr^.Aeltype, true, true, typeptr^.Arraypf, false);

	  if not replicate then begin
	    typeptr^.ifd := st_currentifd;
	    typeptr^.typendx := baseiaux;
	    end;
          st_addtq(baseiaux, tqArray);
	  {take care of the indx type}
	  if typeptr^.Inxtype^.Form = Scalar then begin
	    iaux := Typetoaux(typeptr^.Inxtype, false, true, false, true);
	    junk := st_auxrndxadd(typeptr^.Inxtype^.ifd, iaux);
	    end
	  else begin
	    iaux := Typetoaux(typeptr^.Inxtype^.Hosttype, false, true, false, true); 
	    junk := st_auxrndxadd(typeptr^.Inxtype^.Hosttype^.ifd, iaux);
	    end;
	  with typeptr^ do
	    if Inxtype^.Form = Scalar then begin (* enumerated type *)
	      junk := st_auxadd(0);
	      if Inxtype^.Scalkind = Declared then
	        junk := st_auxadd(Inxtype^.Dimension)
	      else {must be charptr}
	        junk := st_auxadd(255);
	      end
	    else begin (* must be subrange *)
	      junk := st_auxadd(Inxtype^.Vmin);
	      junk := st_auxadd(Inxtype^.Vmax);
	      end;
	  junk := st_auxadd(typeptr^.Aelsize);
	  end
	else baseiaux := typeptr^.typendx;
	Typetoaux := baseiaux;
	end;
      Records: 
	begin
	if typeptr^.ifd = -1 then 
	  begin
	  typeptr^.Recidn := st_blockbegin(0, typeptr^.Stsize div addrunit, 
					   scInfo);
	  Lidp := typeptr^.Recfirstfield;
	  while (Lidp <> nil) do begin
#if 0
	    if Lidp^.Inpacked then
	      sc := scBits
	    else 
#endif
	    sc := scInfo;
	    Lidp^.symndx := st_symadd(Symaddstr(Lidp^.Idname), Lidp^.Fldaddr,
		  stMember, sc, Typetoaux(Lidp^.Idtype, false, true, 
		    			  typeptr^.Recordpf, false));
	    Lidp := Lidp^.next;
	    end {while};
	  if typeptr^.Recvar <> nil then 
	    Processvariant(typeptr^.Recvar);
	  junk := st_blockend(typeptr^.Stsize div addrunit);
	  end;
	if not auxneeded then
	  typeptr^.ifd := -2 {to indicate sym entry created but not aux entry}
	else if replicate or 
	   not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	  iaux := st_auxbtadd(btStruct);
	  if replicate then begin
	    if typeptr^.ifd = -1 then
	      typeptr^.ifd := -2;
	    end
	  else begin
	    typeptr^.ifd := st_currentifd;
	    typeptr^.typendx := iaux;
	    end;
	  junk := st_auxrndxadd_idn(typeptr^.Recidn);
	  end
	else iaux := typeptr^.typendx;
	Typetoaux := iaux;
	end;
      otherwise: begin
	typeptr^.ifd := st_currentifd;
	if replicate or 
	   not noneedsamefile and (typeptr^.ifd <> st_currentifd) then begin
	  iaux := st_auxbtadd(btAdr);
	  if not replicate then 
	    typeptr^.typendx := iaux;
	  end
        else iaux := auxnums[btAdr];
	Typetoaux := iaux;
	end;
      end {case};
  end {Typetoaux};

procedure Resolveptrauxes;
  {called at end of Resolvepointers; for patching up aux entries that are
   forward-referenced}
  var
    iaux: integer;
    ifdsave: integer;
  begin
  while headpointers <> nil do
    begin
    if headpointers^.ptrtype^.eltype <> nil then begin
      ifdsave := st_currentifd;
      st_setfd(headpointers^.ifd);
      iaux := Typetoaux(headpointers^.ptrtype^.Eltype, false, true, false, false);
      st_changeauxrndx(headpointers^.iaux, headpointers^.ptrtype^.Eltype^.ifd, 
			iaux);
      st_setfd(ifdsave);
      end;
    headpointers := headpointers^.next;
    end;
  end;
