{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upaslex.p,v 1030.7 88/02/18 14:55:09 bettina Exp $ }

#include "upasglob.h"
#include "cmplrs/uscan.h"
#include "cmplrs/uwri.h"
#include "cmplrs/uoptions.h"
#include "upasuco.h"
#include "upasutil.h"
#include "upassym.h"
#include "upaslex.h"
#include "allocator.h"

var gleveltab: array[0..3] of integer /*:= initialized in upasmain.p
				[GLEVEL_0, GLEVEL_1, GLEVEL_2, GLEVEL_3]*/;
var digit_value: array[0..127] of integer := [
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
     0,  1,  2,  3,  4,  5,  6,  7,
     8,  9, -1, -1, -1, -1, -1, -1,
    -1, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, -1, -1, -1, -1, -1,
    -1, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, -1, -1, -1, -1, -1 ];

(*Printline,Error,Warning,Skipiferr,Errandskip,Iferrskip,Printerrmsg*)
(************************************************************************)
(*									*)
(*	ERROR HANDLING MODULE						*)
(*									*)
(*	An error message, when printed on the terminal, looks like	*)
(*	this:								*)
(*									*)
(*	  4/  2 CASE KIND OF						*)
(*    PROG1	     ^---						*)
(*    1.  IDENTIFIER NOT DECLARED					*)
(*									*)
(*	If any errors or warnings occur, the line is			*)
(*	printed out (by procedure Finishline).	An arrow with dashes	*)
(*	is used to point to the current symbol, and the error number	*)
(*	is stored in Errlist.  Before Getnextline reads in the nextline,*)
(*	it prints out all the error messages that are in Errlist.	*)
(*									*)
(*	Some warnings are not associate with the current line, for	*)
(*	instance if a variable is not used or a procedure declared	*)
(*	forward never appears.	Procedure ErrorwithId and WarningwithId *)
(*	are called in these cases, an the Id to be printed is stored	*)
(*	in Errlist.							*)
(*									*)
(************************************************************************)
procedure Pusherror (
	    Errno : integer;
	    Warning : boolean;
	    Varnam : Identname;
	    Errorpos : integer);
  (* record an error in Errlist 					     *)
  begin
    if ((Errinx < Maxerr) and (Varnam[1] <> ' ')) or (Errinx < Maxprserr) then
      begin
      Errinx := Errinx+1;
      Errlist[Errinx].Errno := Errno;
      Errlist[Errinx].Warning := Warning;
      Errlist[Errinx].Varname := Varnam;
      Errlist[Errinx].Errpos := Errorpos;
    end;
  end {procedure Pusherror};

procedure Error (* Ferrnr: Integer  *);
  var
    Ignore : boolean;
  begin 				(* error			     *)
    (* if there was an error already at the same token, don't count it       *)
    Ignore := Errinx > 0;
    if Ignore then begin
      Ignore := (Symmarker = Errorpos) and not Errlist[Errinx].Warning;
    end;
    if not Ignore then begin
      Errorcount := Errorcount+1;
      debugging_symbols := false; {inhibit any output of debugging info}
      Pusherror(Ferrnr, false, '                ', Symmarker);
    end;
    StopUcode;
  end {procedure Error};


procedure Errorwithid /* ( Ferrnr : integer; Varnam : Identname)  */;
  (* report error no. ferrnr, including the string ftext, picked from the    *)
  (* source file							     *)
  begin
    Errorcount := Errorcount+1;
    Pusherror(Ferrnr, false, Varnam, Symmarker);
    StopUcode;
  end {procedure Errorwithid};

procedure Warning /* ( Ferrnr : integer)  */;
  (* report an error, but don't count it: it is not fatal                    *)
  begin 				(* warning			     *)
    if not nowarn and (Symmarker <> Errorpos) then begin
      Pusherror(Ferrnr, true, '                ', Symmarker);
    end;
  end {procedure Warning};

procedure Warningwithid /* ( Ferrnr : integer; Varnam : Identname)  */;
  begin
    if not nowarn then begin
      Pusherror(Ferrnr, true, Varnam, Symmarker);
    end;
  end {procedure Warningwithid};

procedure Skipiferr /* ( Fsyinsys : Setofsys; Ferrnr : integer; Fskipsys :   */
					/* Setofsys)  */;

  (***************************************************************************)
  (* if the last symbol scanned, sy, is not in the set fsyinssys, then:      *)
  (* report error number ferrnr and skip the tokens (symbols) until you hit  *)
  (* one of the symbols in the set fskipsys				     *)
  (***************************************************************************)

  begin
    if not (Sy in Fsyinsys) then begin
      Error(Ferrnr);
      while not (Sy in Fskipsys+Fsyinsys+[Eofsy]) do begin
	Insymbol;
      end {while};
    end;
  end {procedure Skipiferr};

procedure Iferrskip /* ( Ferrnr : integer; Fsys : Setofsys)  */;
  begin
    if not (Sy in Fsys) then begin
      Error(Ferrnr);
      while not (Sy in Fsys+[Eofsy]) do begin
	Insymbol;
      end {while};
    end;
  end {procedure Iferrskip};

procedure Errandskip /* ( Ferrnr : integer; Fsys : Setofsys)  */;
  begin
    Error(Ferrnr);
    while not (Sy in Fsys+[Eofsy]) do begin
      Insymbol;
    end {while};
  end {procedure Errandskip};

(*Writelinebuf,Putlinebuf,ArrowLine,Printerrmsg,Finishline,Getnextline,Skipedirectory,Newfile,Popfile,Pushfile*)
(************************************************************************)
(*									*)
(*	LEXER MODULE							*)
(*									*)
(*	The main procedure in this module is Insymbol, which gets	*)
(*	the next symbol and returns the symbol type in the global	*)
(*	variable Sy, the value, if any, in Val, and the symbol itself,	*)
(*	if it is an identifier, in Id.	Note that reserved words are	*)
(*	not considered identifiers, and each one is considered a	*)
(*	seperate symbol type.						*)
(*									*)
(*	The source program is read a line at a time into the line	*)
(*	buffer.  It is not uppercased until it is retrieved from	*)
(*	the buffer by Nextch, and even then only if it is not a 	*)
(*	string. 							*)
(*									*)
(*									*)
(************************************************************************)
procedure Writelinebuf (
	var Fil : text);
  (* Writes current source line to file.				     *)
  var
    I : integer;

  begin
    for I := 1 to Chcnt do begin
      write(Fil, Buffer[I]);
    end {for};
    writeln(Fil);
  end {procedure Writelinebuf};

procedure Putlinebuf;
  var
    U : Bcrec;
    I : integer;
  begin
    with U.Constval do begin
      new1(Chars);
      for I := 1 to Chcnt do begin
	Chars^.ss[I] := Buffer[I];
      end {for};
      Ival := Chcnt;
    end {with};
    U.Opc := Ucomm;
    U.Dtype := Mdt;
    Ubittobyte(U); Uwrite(U);
  end {procedure Putlinebuf};

procedure Arrows (
	var Fil : text);
  var
    Curpos, I, J : integer;
  begin
    Curpos := 0;
    for I := 1 to Errinx do begin
      with Errlist[I] do begin
	if Errpos > Curpos then begin
	  for J := 1 to Errpos-Curpos-1 do begin
	    if ord(Buffer[J+Curpos]) = Tab then begin
	      write(Fil, chr(Tab));
	    end else begin
	      write(Fil, ' ');
	    end;
	  end {for};
	  write(Fil, '^');
	  Curpos := Errpos;
	end;
      end {with};
    end {for};
  end {procedure Arrows};

procedure ArrowLine (
	var Fil : text);
  var
    Endofmessage, I : integer;
    (* Writes out the current line with arrows pointing to the beginnings of *)
    (* tokens at which errors occurred. 				     *)
    warningonly: boolean;	{whether all messages are warnings}
  begin
    {determine warningonly}
    warningonly := true;
    I := 1;
    while warningonly and (i <= Errinx) do 
      if not Errlist[I].Warning then warningonly := false
      else I := I + 1;
    writeln(Fil);
    write(Fil, 'upas: ');
    if warningonly then
      write(Fil, 'Warning: ')
    else write(Fil, 'Error: ');
    writeln(Fil, cppfilename:Fnln(cppfilename), ', line ',
	    Linecnt:1, ': ', Currname:Idln(Currname), ':');
#if 0
    writeln(Fil, '*** Line ', Linecnt : 1, ', File ',
	cppfilename : Fnln(cppfilename), ', Page ', Pagecnt : 1, ' in ',
	Currname : Idln(Currname), ' ***');
#endif
    Writelinebuf(Fil);
    Arrows(Fil);
    (* See if the error message will fit on the same line as the arrow. We   *)
    (* must compensate specially for tabs.				     *)
    Endofmessage := Listlen+1;
    if Errinx = 1 then begin
      with Errlist[1] do begin
	if not Warning and (Varname[1] = ' ') then begin
	  Endofmessage := Errpos+Errno div 50*5;
	  for I := 1 to Errpos do begin
	    if ord(Buffer[I]) = Tab then begin
	      Endofmessage := Endofmessage+Tabsetting-(I-1) mod Tabsetting-1;
	    end;
	  end {for};
	end;
      end {with};
    end;
    if Endofmessage > Listlen then begin
      writeln(Fil);
    end else begin
      write(Fil, ' ');
    end;
  end {procedure ArrowLine};

procedure Printerrmsg (
	var Fil : text;
	    Errnum : integer);
  (* print error message						     *)
  var
    I, J : integer;
  begin
    with Errlist[Errnum] do begin
      if Errinx > 1 then begin
	write(Fil, '      ', Errnum : 1, '.  ');
      end else begin
	write(Fil, '      ');
      end;
      if Warning then begin
	write(Fil, 'Warning: ');
      end;
      if Varname[1] <> ' ' then begin
	write(Fil, /* 'IN ', Currname : Max(1, Idln(Currname)), ', ', */
	    Varname : Idln(Varname), ' ');
      end;
      J := Errno div 50;
      (* error number = errormessagelength*10 + errormessageindex;	     *)
      I := Errno mod 50;
    end {with};
    case J of
    3 : write(Fil, Errmess15[I]);
    4 : write(Fil, Errmess20[I]);
    5 : write(Fil, Errmess25[I]);
    6 : write(Fil, Errmess30[I]);
    7 : write(Fil, Errmess35[I]);
    8 : write(Fil, Errmess40[I]);
    9 : write(Fil, Errmess45[I]);
    10 : write(Fil, Errmess50[I]);
    11 : write(Fil, Errmess55[I]);
    end {case};
    writeln(Fil);
  end {procedure Printerrmsg};

procedure Finishline;
  (* does all listing activity for a given line, including error messages    *)
  var
    I : integer;
  begin
    if Lptfile then begin
      if Headerneeded then begin
	write(List, Header, ' ');
	PrintDate(List);
	write(List, ' ');
	PrintTime(List);
	if Progidp <> nil then begin
	  write(List, ' ', Progidp^.Idname : Idln(Progidp^.Idname));
	end;
	write(List, ' ', cppfilename : Fnln(cppfilename));
	writeln(List, ' page ', Pagecnt : 3);
	writeln(List);
	Headerneeded := false;
      end;
      write(List, Linecnt : 5, chr(Tab));
      Writelinebuf(List);
    end;
    if Errinx > 0 then begin		(* write out erroneous line(s) and   *)
					(* set up error line		     *)
      if Lptfile then begin
	write(List, '  ***', chr(Tab));
	Arrows(List);
	writeln(List);
      end else if Logfile then begin
	ArrowLine(List);
      end;
      if Needsaneoln then begin
	writeln(err);
      end;
      ArrowLine(err);
      for I := 1 to Errinx do begin
	if Lptfile or Logfile then begin
	  Printerrmsg(List, I);
	end;
	Printerrmsg(err, I);
      end {for};
      Needsaneoln := false;
#if defined(UPASPASCAL) || defined(PASTEL)
      Break(err);
#endif
    end;
  end {procedure Finishline};

procedure Getnextline (
	var Infile : text);

  (***************************************************************************)
  (* Reads next nonempty line from source into line buffer, processing page  *)
  (* mark if there is one. When a line is encountered that is too big, it    *)
  (* backs up to the last space (so that there is always a space at the end  *)
  (* of every line -- this helps the scanner), and saves the rest in a	     *)
  (* lookahead buffer. Signals EOF by setting Chcnt to 0		     *)
  (***************************************************************************)

  label 333;
  var
    Tabcount : integer;
    I, J, junk : integer;
    cppidentcheck: packed array[1..6] of char;

  function Cppline: boolean;
    (* process a line generated by cpp: # at first column, followed by a number,
       followed by the file name; return true if successful; if unsuccessful,
       characters read so far are appended to Nextbuffer so that parser will
       continue to parse the line and give error messages *)
    var
      num, I, 
      cnt : integer; (* count number of characters read so far in this line *)
    begin
      cnt := 1;
      Nextbuffer[Nextchcnt+cnt] := Infile^;
      get(Infile);			(* skip # *)
      if Infile^ <> ' ' then begin
	Cppline := false;
	Nextchcnt := Nextchcnt + cnt;
	return;
	end;
      cnt := 2;
      Nextbuffer[Nextchcnt+cnt] := Infile^;
      get(Infile);			(* skip first blank		     *)
      if not (Infile^  in ['0' .. '9']) then begin
	Cppline := false;
	Nextchcnt := Nextchcnt + cnt;
	return;
	end;
      cnt := 3;
      Nextbuffer[Nextchcnt+cnt] := Infile^;
      num := ord(Infile^)-ord('0');
      get(Infile);
      while Infile^ in ['0'..'9'] do begin
	cnt := cnt + 1;
        Nextbuffer[Nextchcnt+cnt] := Infile^;
	num := num*10+(ord(Infile^)-ord('0'));
	get(Infile);
      end {while};
      Linecnt := num-1;
      while (Infile^ <> '"') and not eoln(Infile) do begin
	cnt := cnt + 1;
        Nextbuffer[Nextchcnt+cnt] := Infile^;
	get(Infile);
	end {while};
      if Infile^ <> '"' then begin
	Cppline := false;
	Nextchcnt := Nextchcnt + cnt;
	return;
	end;
      cnt := cnt + 1;
      Nextbuffer[Nextchcnt+cnt] := Infile^;
      get(Infile);
      I := 0;
      while (Infile^ <> '"') and (I <> Filenamelen) do begin
	cnt := cnt + 1;
        Nextbuffer[Nextchcnt+cnt] := Infile^;
	I := I+1;
	cppfilename[I] := Infile^;
	get(Infile);
      end {while};
      if Infile^ <> '"' then begin
	Cppline := false;
	Nextchcnt := Nextchcnt + cnt;
	return;
	end;
      for I := I+1 to Filenamelen do begin
	cppfilename[I] := ' ';
      end {for};
      readln(Infile);
      Headerneeded := true;
      Cppline := true;
    end {procedure Cppline};

  begin 				(* getnextline			     *)
    Finishline;
    if Nextchcnt > 0 then begin
      Tchcnt := Tchcnt+Chcnt-1; (* subtract one for the extra blank  *)
      Symmarker := 1;
      Buffer := Nextbuffer;
      Chcnt := Nextchcnt;
    end else begin
      Tchcnt := Tchcnt+Chcnt+Eolchars-1; (* sub one for the eoln 	     *)
      (* while end of page, get next page				     *)
      while Eopage(Infile) and not eof(Infile) or (Infile^ = '#') do begin
	if (Infile^ = '#') then begin
	  if not Cppline then begin
	    Buffer := Nextbuffer;
	    Chcnt := Nextchcnt;
            Linecnt := Linecnt+1;
            Tlinecnt := Tlinecnt+1;
	    goto 333;
	    end
	  else begin
  	    Addnullfilename(cppfilename);
	    fileNumber:= st_filebegin(st_str, langPascal, 1, gleveltab[glevel]);
	      if veryfirstfile then begin
    		if lsb_first then
      		  Uco1int(Ubgn, LITTLEENDIAN)
    		else Uco1int(Ubgn, BIGENDIAN);
		mainfileNumber := fileNumber;
		veryfirstfile := false;
		end;
	    Ucooptn(UCO_SOURCE, 1);(* source language is Pascal	     *)
	    Ucofname(cppfilename);
	  end
	end else begin
	  Pagecnt := Pagecnt+1;
	  Tchcnt := Tchcnt+1;
	  if Lptfile then begin
	    (* start new page in listing file				     *)
	    page(List);
	    Headerneeded := true;
	  end;
	  Readpage(Infile);
	end;
      end {while};
      Linecnt := Linecnt+1;
      Tlinecnt := Tlinecnt+1;
      Chcnt := 0;
    end;
333:Symcnt := 0;
    Errorpos := 0;
    Errinx := 0;
    if not eof(Infile) then begin
      (* main loop to read the characters of the line *)
      while not eoln(Infile) and (Chcnt < Chcntmax) do begin
	Chcnt := Chcnt+1;
	Buffer[Chcnt] := Infile^;
	get(Infile);
      end {while};
    end;
    for j := 1 to 6 do
      cppidentcheck[j] := Buffer[j];
    if cppidentcheck = '#ident' then {ignore #ident passed by cpp}
      for j := 1 to Chcnt do
	Buffer[j] := ' ';
    if not eof(Infile) then begin
      if not eoln(Infile) then begin
	(* big line -- back up until we find a non-lookahead char	     *)
	J := Chcnt;
	while Lookahead[Buffer[J]] and (J > 1) do begin
	  J := J-1;
	end {while};
	(* copy excess into holding buffer				     *)
	if Lookahead[Buffer[J]] then begin
	  Symmarker := Chcnt;
	  Warning(462); 		(* line too dense		     *)
	end else begin
	  for I := 1 to Chcnt-J do begin
	    Nextbuffer[I] := Buffer[J+I];
	  end {for};
	  Nextchcnt := Chcnt-J;
	  Chcnt := J;
	  (* makes Nextbuffer contains at least a blank so next time knows   *)
	  (* that it is not a new line					     *)
	  if Nextchcnt = 0 then begin
	    Nextbuffer[1] := ' ';
	    Nextchcnt := 1;
	  end;
	end;
      end else begin
	Nextchcnt := 0;
	readln(Infile);
	Chcnt := Chcnt+1;		(* put in space for EOLN marker      *)
	Buffer[Chcnt] := ' ';
      end;
    end;
    if Showsource and Printucode then begin
      Putlinebuf;
    end;
    Chptr := 1;
  end {procedure Getnextline};

procedure Newfile /* ( var Infile : text)  */;
  {called only once at beginning of processing}
  var
    I : integer;
  begin
    veryfirstfile := true;
    Chcnt := 0;
    Linecnt := 0;
    Pagecnt := 1;
    Tlinecnt := 0;
    Nextchcnt := 0;
    Getnextline(Infile);
    Sy := Othersy;
    Insymbol;
  end {procedure Newfile};


(*Setswitch*)
procedure Setswitch /* ( Switchname : Identname; Switchval : integer)  */;

  var
    Lch : char;
    Lswitch : boolean;

  begin
    Lch := Switchname[1];
    if (Switchname[2] <> ' ') and (Lch <> 'T') and (Lch <> 'Z') then begin
      Warningwithid(203, Switchname);
    end;				(* not a known option		     *)
    Lswitch := Switchval <> 0;
    if Switchname[1] = '!' then begin
      Resetpossible := false;
    end else if not Resetpossible and (Lch in ['D', 'P', 'O']) then begin
      Warning(558);
    end else if not (Lch in ['B', 'C', 'D', 'E', 'G', 'I', 'L', 'O', 'R',
	'S', 'U', 'W']) then begin
      Warningwithid(203, Switchname);	(* not a known option		     *)
    end else begin
      case Lch of
      'B' : Runtimecheck := Lswitch;
      'C' : begin
	  if Printucode and not Lswitch then begin
	    StopUcode;
	  end;
	  Printucode := Lswitch;
	end {case 'C'};
#if 0
      'D' : begin
	  if Lswitch then begin
	    if Lswitch and not Emitsyms then begin
	      rewrite(Symtbl, Symname);
	    end;
	    Emitsyms := true;
	    Ucooptn(UCO_FDBUG, 1);
	  end;
	end {case 'D'};
      'E' : Showsource := Lswitch;
#endif
      'G' : begin
	  Logfile := Lswitch;
	  if Logfile and not Listrewritten then begin
	    rewrite(List, Listname);
	    Listrewritten := true;
	  end;
	end {case 'G'};
      'I' : Maxidlength := Switchval;
      'L' : begin
	  Lptfile := Lswitch;
	  if Lptfile and not Listrewritten then begin
	    rewrite(List, Listname);
	    Listrewritten := true;
	  end;
	end {case 'L'};
#if 0
      'O' : Optimize := Lswitch;
      'S' : Standrdonly := Lswitch;
      'T' : begin
	  Ucooptn(Switchname, Switchval);
	  if (Switchname = 'TRTIMES') and (Switchval = 0) then begin
	    Noruntimes := true;
	  end;
	end {case 'T'};
#endif
#if 0
      'V' : begin
	  Intptr^.Stsize := Switchval;
	  Intptr^.Packsize := Switchval;
	  Cardinalptr^.Stsize := Switchval;
	  Cardinalptr^.Packsize := Switchval;
	  Ucooptn('TINTSIZE', Switchval);
	end {case 'V'};
      'W' : begin
	  Switchval := Switchval mod 100;
	  Idwarning := Switchval mod 10 = 1;
	  Switchval := Switchval div 10;
	  Commentwarning := Switchval mod 10 = 1;
	end {case 'W'};
#endif
      'Z' : begin
	  if (Switchname = 'zmark') then begin
	    Ucooptn(UCO_ZMARK, Switchval);
	  end else if (Switchname = 'zvref') then begin
	    Ucooptn(UCO_ZVREF, Switchval);
	  end else if (Switchname = 'zdbug') then begin
	    Ucooptn(UCO_ZDBUG, Switchval);
	  end else if (Switchname = 'zmovc') then begin
	    Ucooptn(UCO_ZMOVC, Switchval);
	  end else if (Switchname = 'zcopy') then begin
	    Ucooptn(UCO_ZCOPY, Switchval);
	  end else if (Switchname = 'zcomo') then begin
	    Ucooptn(UCO_ZCOMO, Switchval);
	  end else if (Switchname = 'zstor') then begin
	    Ucooptn(UCO_ZSTOR, Switchval);
	  end else if (Switchname = 'zscm') then begin
	    Ucooptn(UCO_ZSCM, Switchval);
	  end else if (Switchname = 'zaloc') then begin
	    Ucooptn(UCO_ZALOC, Switchval);
	  end;
	end {case 'Z'};
      end {case};
    end;
  end {procedure Setswitch};

(*Skipcomment,Optns,Getnumber,Getid*)
procedure Insymbol;
  label
    111, 999;

  var
    I, K, d : integer;
    Ival : integer;
    Stringtoolong : boolean;
    Ch : char;
    String : packed array[1..Strglgth] of char;

#if 0
  procedure Eoffound (
	      EofOK : boolean);
    begin
      if not EofOK then begin
	Error(265);
      end;
#if 0
      if InIncludefile then begin
	Popfile;
	goto 111;
      end else begin
#endif
	Sy := Eofsy;
	goto 999;
#if 0
      end;
#endif
    end {procedure Eoffound};
#endif

  procedure Skipspaces;
    begin
      (* Skip blanks and tabs. Note that this is the only place, except for  *)
      (* comments, where we have to check for end of line.		     *)
      while (Buffer[Chptr] = ' ') or (ord(Buffer[Chptr]) = Tab) do begin
	if Chptr < Chcnt then begin
	  Chptr := Chptr+1;
	end else begin
#if 0
	  if InIncludefile then begin
	    Getnextline(Incfile);
	  end else 
#endif
	  Getnextline(input);
	  if Chcnt = 0 then begin
	    Sy := Eofsy;
	    return;
	  end;
	end;
      end {while};
    end {procedure Skipspaces};

  procedure Skipcomment(standardcomment: boolean);
    var
      Loopdone : boolean;
      N : integer;

#if 0
    procedure Optns;

      (***********************************************************************)
      (* Parse the Optns in a comment in which the first character is a hash *)
      (* mark (#). The possible values for Optns, and consequent setting of  *)
      (* variables, are: '+': Lvalue = 1 '-': Lvalue = 0 positive number:    *)
      (* Lvalue = number quoted string: Loadname = string, Loadnamectr =     *)
      (* Length(string) 						     *)
      (***********************************************************************)

      var
	Lvalue : integer;
	Optnname : Identname;
	Loadname : Filename;
	Loadnamectr : integer;
	I : integer;
	Ch : char;

      begin				(* Optns			     *)
	repeat
	  Chptr := Chptr+1;
	  Skipspaces(false);
	  Ch := Buffer[Chptr];
	  Optnname := Blankid;
	  if (Ch >= 'a') and (Ch <= 'z') then begin
	    Ch := chr(ord(Ch)-ord('a')+ord('A'));
	  end;
	  Optnname[1] := Ch;
	  if (Ch < 'A') or (Ch > 'Z') then begin
	    Warning(203) (* UNKNOWN OPTION  *);
	  end;
	  if not (Ch in ['*', '}', '\']) then begin
	    Chptr := Chptr+1;
	  end;
	  if Optnname[1] in ['T', 'Z'] then begin (* Optimizer or code gen.  *)
					(* option			     *)
	    I := 1;
	    Symmarker := Chptr;
	    Ch := Buffer[Chptr];
	    while Ssy[Ch] = Identsy do begin
	      if (Ch >= 'a') and (Ch <= 'z') then begin
		Ch := chr(ord(Ch)-ord('a')+ord('A'));
	      end;
	      I := I+1;
	      Optnname[I] := Ch;
	      Chptr := Chptr+1;
	      Ch := Buffer[Chptr];
	    end {while};
	    (* Make sure the option name has at least 2 letters 	     *)
	    if Ssy[Optnname[2]] <> Identsy then begin
	      Error(203);
	    end;
	  end;
	  Skipspaces(false);
	  Lvalue := 0;
	  Symmarker := Chptr;
#if 0
	  if Optnname = 'TLOAD' then begin
	    Loadnamectr := 0;
	    if Buffer[Chptr] <> '''' then begin
	      Warning(254);
	    end;
	    Chptr := Chptr+1;
	    while (Buffer[Chptr] <> '''') and (Chptr < Chcnt) do begin
	      if Loadnamectr < Filenamelen then begin
		Loadnamectr := Loadnamectr+1;
		Loadname[Loadnamectr] := Buffer[Chptr];
	      end;
	      Chptr := Chptr+1;
	    end {while};
	    if Buffer[Chptr] <> '''' then begin
	      Warning(254);
	    end else if Chptr < Chcnt then begin
	      Chptr := Chptr+1;
	    end;
	    for I := Loadnamectr+1 to Filenamelen do begin
	      Loadname[I] := ' ';
	    end {for};
	    Ucooptn(name, 1);
	    Ucofname(Loadname);
	  end else
#endif
	    begin
	    Ch := Buffer[Chptr];
	    if Ch = '+' then begin
	      Lvalue := 1;
	      Chptr := Chptr+1;
	    end else if Ch = '-' then begin
	      Lvalue := 0;
	      Chptr := Chptr+1;
	    end else if (Ch >= '0') and (Ch <= '9') then begin
	      Lvalue := 0;
	      repeat
		Lvalue := Lvalue*10+(ord(Ch)-ord('0'));
		Chptr := Chptr+1;
		Ch := Buffer[Chptr];
	      until (Ch < '0') or (Ch > '9');
	    end else begin
	      Warning(254);
	    end;
	    Setswitch(Optnname, Lvalue);
	  end;
	  Skipspaces(false);
	until Buffer[Chptr] <> ',';
      end {procedure Optns};
#endif

    begin				(* SKIPCOMMENT			     *)
      Chptr := Chptr+1;
      Loopdone := false;
#if 0
      if (Buffer[Chptr] = '#') and (Endchar = '*') then begin
	Optns;
      end;
#endif
      while not Loopdone do begin
	if standardcomment then begin
	  if Buffer[Chptr] = '}' then
	    Loopdone := true
	  else begin 
	    if Buffer[Chptr] = '*' then
	      if (Chptr < Chcnt) and (Buffer[Chptr+1] = ')') then begin
	        Loopdone := true;
	        Chptr := Chptr+1;
	        end;
	    end
	  end
	else begin
	  if Buffer[Chptr] = '*' then
	    if (Chptr < Chcnt) and (Buffer[Chptr+1] = '/') then begin
	      Loopdone := true;
	      Chptr := Chptr+1;
	      end;
	  end;
#if 0
	if Buffer[Chptr] = Beginchar then begin
	  (* if nested comment, give warning, if requested		     *)
	  Symmarker := Chptr;
	  if Commentwarning then begin
	    if Beginchar <> '(' then begin
	      Warning(369);
	    end else if (Chptr < Chcnt) then begin
	      if Buffer[Chptr+1] = '*' then begin
		Warning(369);
	      end;
	    end;
	  end;
	end else if Buffer[Chptr] = Endchar then begin
	  if Beginchar <> '(' then begin
	    Loopdone := true;
	  end else if (Chptr < Chcnt) then begin
	    if Buffer[Chptr+1] = ')' then begin
	      Loopdone := true;
	      Chptr := Chptr+1;
	    end;
	  end;
	end;
#endif
	if Chptr < Chcnt then begin
	  Chptr := Chptr+1;
	end else begin
#if 0
	  if InIncludefile then begin
	    Getnextline(Incfile);
	  end else 
#endif
	  Getnextline(input);
	  if Chcnt = 0 then begin
	    Error(265);
	    Sy := Eofsy;
	    return;
	  end;
	end;
      end {while};
    end {procedure Skipcomment};


  procedure Number;

    var
      Index, I, K: integer;
      Ch : char;
      Tempival: integer;
      radix, accum, d: cardinal;

      (***********************************************************************)
      (* Parses numeric constant. This could be a decimal integer, or a real *)
      (* number, with or without an exponent				     *)
      (***********************************************************************)

      (***********************************************************************)
      (* Note: The digits of an Intconstsy are stored as and Identsy too.    *)
      (* This allows entering labels like all other identifiers into the     *)
      (* symbol table.							     *)
      (***********************************************************************)

    begin
      Id := '                ';
      (* skip any leading zeroes	     *)
      while Buffer[Chptr] = '0' do begin
	Chptr := Chptr+1;
      end {while};
      (* SAVE ALL DIGITS IN THE INTEGER PART OF THE NUMBER		     *)
      if Lastsign = Neg then begin
	Val.Chars^.ss[1] := '-';
	Lastsign := None;
      end else begin
	Val.Chars^.ss[1] := ' ';
      end;
      Index := 1;
      while Ssy[Buffer[Chptr]] = Intconstsy do begin 
	Index := Index+1;		(* POINT TO NEXT SYMDIG SLOT	     *)
	if Index <= Strglgth then begin
	  Val.Chars^.ss[Index] := Buffer[Chptr];
	end;				(* SAVE THE DIGIT		     *)
	if Index <= Identlength then begin
	  Id[Index-1] := Buffer[Chptr];
	end;				(* ADD TO SYMBOL NAME FOR LABELS     *)
	Chptr := Chptr+1;		(* READ THE NEXT CHAR		     *)
      end {while};
      Ch := Buffer[Chptr];
      if (Ch = '#') and Standrdonly or 
	 ((Ch <> '.') or (Buffer[Chptr+1] = '.')) and (Ch <> 'E')
	 and (Ch <> 'e') or (Ch = '.') and (Buffer[Chptr+1] = ')') then begin
        (* it is an integer constant         *)
	if Ch = '#' then begin
	  if index-1 > 2 then
	    Error(179); (* radix too large *)
	  radix := 0;
	  if index >= 2 then
	    radix := ord(Id[1]) - ord('0');
	  if index = 3 then
	    radix := radix*10 + ord(Id[2]) - ord('0');
	  if (radix > 36) or (radix = 0) then begin
	    Error(179); (* radix illegal   *)
	    radix := 10;
	    end;
	  (* scan the body of the number *)
	  Index := 1;
	  Chptr := Chptr + 1;
	  while (Buffer[Chptr] in ['0'..'9', 'a'..'z', 'A'..'Z']) do begin
	    Index := Index+1;
	    if Index <= Strglgth then begin
	      Val.Chars^.ss[Index] := Buffer[Chptr];
	    end;			
	    if Index <= Identlength then begin
	      Id[Index-1] := Buffer[Chptr];
	    end;		
	    Chptr := Chptr+1;		(* READ THE NEXT CHAR		     *)
	    end {while};
	  if Index = 1 then
	    Error(324);
	  end
	else radix := 10;
	accum := 0;
	for K := 2 to Index do begin
	  d := digit_value[ord(Val.Chars^.ss[K])];
	  if d >= radix then
	    Error(325)
	  else if (radix = 10) and (maxint div radix <= - accum) and 
		  ((maxint div radix < - accum) or (maxint mod 10 + 1 < d)) then
	    Error(204)
	  else accum := accum * radix - d;
#if 0
	  if Tempival <= Maxintdiv10 then begin
	    if (Tempival = Maxintdiv10) then begin
	      if ord(Val.Chars^.ss[K])-ord('0') > Maxintmod10 then begin
		Error(204);
		Tempival := 0;
	      end;
	    end;
	    Tempival := 10*Tempival+(ord(Val.Chars^.ss[K])-ord('0'));
	  end else begin
	    Error(204);
	    Tempival := 0;
	  end;
#endif
	end {for};
	if Val.Chars^.ss[1] = '-' then begin
	  Tempival := accum;
	end else begin
#if 0
	  if accum = Tgtminint then begin
	    Error(204);
	    Tempival := 0;
	  end else begin
	    Tempival := - accum;
	  end;
#else
	  Tempival := - accum;
#endif
	end;
	Val.Ival := Tempival;
      end else begin			(* real 			     *)
	Sy := Realconstsy;		(* INDICATE SYMBOL TYPE 	     *)
	if (Buffer[Chptr] = '.') then begin (* EXPLICIT FRACTION             *)
	  Chptr := Chptr+1;		(* SKIP THE POINT		     *)
	  if Index = 1 then begin
	    Index := Index+1;
	    Val.Chars^.ss[Index] := '0';
	  end;
	  if Val.Chars^.ss[1] = ' ' then begin
	    (* shift left by 1						     *)
	    for I := 1 to Index-1 do begin
	      Val.Chars^.ss[I] := Val.Chars^.ss[I+1];
	    end {for};
	  end else begin
	    Index := Index+1;
	  end;
	  Val.Chars^.ss[Index] := '.';
	  if Ssy[Buffer[Chptr]] = Intconstsy then begin (* CHAR AFTER POINT  *)
					(* IS NUMERAL			     *)
	    while Ssy[Buffer[Chptr]] = Intconstsy do begin (* SCAN THROUGH   *)
					(* ALL DIGITS LOOP THROUGH FRACTION  *)
					(* DIGITS			     *)
	      Index := Index+1; 	(* SYMDIGS POINTER		     *)
	      if Index <= Strglgth then begin
		Val.Chars^.ss[Index] := Buffer[Chptr];
	      end;
	      (* SAVE THIS DIGIT					     *)
	      Chptr := Chptr+1;
	    end {while};
	  end else begin
	    Error(205); 		(* DIGIT AFTER POINT NOT NUMERAL     *)
	  end;
	end;				(* OF EXPLICIT FRACTION 	     *)
	(* AT THIS POINT ALL DIGITS HAVE BEEN SCANNED. HANDLE A POSSIBLE     *)
	(* EXPONENT							     *)
	if (Buffer[Chptr] = 'E') or (Buffer[Chptr] = 'e') then begin
					(* HANDLE EXPLICIT EXPONENT	     *)
	  Index := Index+1;
	  Val.Chars^.ss[Index] := Buffer[Chptr];
	  Chptr := Chptr+1;		(* SKIP THE 'E'                      *)
	  if (Buffer[Chptr] = '+') or (Buffer[Chptr] = '-') then begin
					(* EXPLICIT SIGN		     *)
	    Index := Index+1;
	    Val.Chars^.ss[Index] := Buffer[Chptr];
	    Chptr := Chptr+1;		(* SKIP THE SIGN		     *)
	  end;
	  if Ssy[Buffer[Chptr]] <> Intconstsy then begin
	    Error(205); 		(* NON-NUMERIC EXPONENT 	     *)
	  end else begin		(* EXPONENT IS NUMERIC		     *)
	    repeat			(* LOOP THROUGH EXPONENT DIGITS      *)
	      Index := Index+1;
	      Val.Chars^.ss[Index] := Buffer[Chptr];
	      Chptr := Chptr+1;
	    until Ssy[Buffer[Chptr]] <> Intconstsy;
	  end;
	  (* NON-NUMERIC DELIMITS EXPONENT				     *)
	end;				(* OF EXPLICIT EXPONENT 	     *)
	Val.Ival := Index;
      end;
    end {procedure Number};		(* number			     *)


  procedure GetId;
    label
      222;
    var
      I, K : integer;
      Ch : char;
      (* The $ is non-standard, and is used to compile runtimes, so that the *)
      (* runtimes will have unique names.				     *)
    begin
      Ch := Buffer[Chptr];
      K := 0;
      Id := '                ';
      repeat
	if K < Identlength then begin
	  if (Ch >= 'A') and (Ch <= 'Z') then begin
	    Ch := chr(ord(Ch)+(ord('a')-ord('A')));
	  end;
	  K := K+1;
	  Id[K] := Ch;
	end;
	Chptr := Chptr+1;
	Ch := Buffer[Chptr];
      until not (Ssy[Ch] in [Identsy, Intconstsy]);

      (***********************************************************************)
      (* See if it is a reserved word -- compare with all reserved words of  *)
      (* the same size							     *)
      (***********************************************************************)
      if K <= 9 then begin
	for I := Frw[K] to Frw[K+1]-1 do begin
	  if (Rw[I] = Id)
		and not (Standrdonly
		     and (Rsy[I] in [(*Modulesy,*) Returnsy, Otherwisesy])) then
	    begin
	    Sy := Rsy[I];
	    goto 222;
	  end;
	end {for};
      end;
      (* if user has requested a smaller significant id length, oblige her   *)
      for K := Maxidlength+1 to Identlength do begin
	Id[K] := ' ';
      end {for};
222 :
#if 0
      if Sy = Includesy then begin	(* handle include files here!	     *)
	Skipspaces(false);
	if Buffer[Chptr] <> '''' then begin
	  Error(264);			(* string constant expected	     *)
	end else begin
	  I := 1;
	  Chptr := Chptr+1;
	  while Buffer[Chptr] <> '''' do begin
	    if I <= Filenamelen then begin
	      Incfilename[I] := Buffer[Chptr];
	    end;
	    I := I+1;
	    Chptr := Chptr+1;
	  end {while};
	  for I := I to Filenamelen do begin
	    Incfilename[I] := ' ';
	  end {for};
	  Chptr := Chptr+1;
	  Skipspaces(false);
	  if Buffer[Chptr] <> ';' then begin
	    Warning(156);
	  end else begin
	    Chptr := Chptr+1;
	  end;
	  if InIncludefile then begin
	    Error(454); 		(* only one level of Include files   *)
					(* supported			     *)
	  end else begin
	    Pushfile(Incfilename);
	  end;
	  goto 999;			(* Pushfile calls insymbol, so we    *)
					(* must exit here.		     *)
	end;
      end;
#endif
    end {procedure GetId};

(*Insymbol*)
  begin					(* INSYMBOL			     *)
111 :
    if Chcnt = 0 then begin
      writeln(err);
      writeln(err, 'Compiler error: reading past end of file...');
      Abort;
    end;
    Skipspaces;
    if sy = Eofsy then 
      goto 999;
    Symmarker := Chptr;
    Ch := Buffer[Chptr];
    Sy := Ssy[Ch];
    if not (Sy in Trickychars) then begin
      Chptr := Chptr+1;
    end else begin
      case Sy of
      Othersy : begin
	  Error(218);			(* illegal char 		     *)
	  Chptr := Chptr+1;
	  goto 111;
	end {case Othersy};
      Identsy : GetId;
      Intconstsy : Number;
      Rdivsy : begin
	  Chptr := Chptr+1;
	  if (Buffer[Chptr] = '*') and not Standrdonly then begin
	    Skipcomment(false);
	    goto 111;
	  end;
	end {case Rdivsy};
      Colonsy : begin
	  Chptr := Chptr+1;
	  if Buffer[Chptr] = '=' then begin
	    Sy := Becomessy;
	    Chptr := Chptr+1;
	  end;
	end {case Colonsy};
      Periodsy : begin
	  Chptr := Chptr+1;
	  if Buffer[Chptr] = '.' then begin
	    Sy := Rangesy;
	    Chptr := Chptr+1;
	  end else if Buffer[Chptr] = ')' then begin;
	    Sy := Rbracksy;
	    Chptr := Chptr+1;
	  end;
	end {case Periodsy};
      Ltsy, Gtsy :			(* < OR <> OR <=, > OR >=	     *)
	  begin
	  Chptr := Chptr+1;
	  if (Sy = Ltsy) and (Buffer[Chptr] = '>') then begin
	    Sy := Nesy;
	    Chptr := Chptr+1;
	  end else if Buffer[Chptr] = '=' then begin
	    if Sy = Ltsy then begin
	      Sy := Lesy;
	    end else begin
	      Sy := Gesy;
	    end;
	    Chptr := Chptr+1;
	  end;
	end {case Ltsy};
      Commentsy : begin
	  Skipcomment(true);
	  goto 111;
	end {case Commentsy};
      Lparentsy : begin
	  Chptr := Chptr+1;
	  if Buffer[Chptr] = '*' then begin
	    Skipcomment(true);
	    goto 111;
	  end else if Buffer[Chptr] = '.' then begin
	    Sy := Lbracksy;
	    Chptr := Chptr+1;
	  end;
	end {case Lparentsy};
      Stringconstsy : begin
	  Lgth := 0;
	  Stringtoolong := false;
	  if Ch = '''' then
	    repeat
	      (* get up to next quote single quote *)
	      repeat
	        Chptr := Chptr+1;
	        if Lgth < Strglgth then begin
		  Lgth := Lgth+1;
		  String[Lgth] := Buffer[Chptr];
	        end else begin
		  Stringtoolong := true;
	        end;
	      until (Chptr = Chcnt) or (Buffer[Chptr] = Ch);
	      if Stringtoolong then begin
	        Error(301);
	      end;
	      if Standrdonly and (Lgth = 0) then begin
		Warning(212);
	      end;
	      if Chptr = Chcnt then begin
	        Error(351);		(* string crosses line boundary      *)
	      end else begin
	        Chptr := Chptr+1;
	      end;
	    until Buffer[Chptr] <> Ch
	  else begin {C string}
	    repeat
	      if Standrdonly then begin
		Warning(212);
	      end;
	      Chptr := Chptr+1;
	      if Lgth < Strglgth then begin
		Lgth := Lgth+1;
		if Buffer[Chptr]  = '\' then (* an escaped character *)
		  begin
		  if Chptr < Chcnt then
	  	    Chptr := Chptr+1
		  else Error(326);
		  case Buffer[Chptr] of
	  	  'a': String[Lgth] := chr(7);
	  	  'b': String[Lgth] := chr(8);
	  	  't': String[Lgth] := chr(9);
	  	  'n': String[Lgth] := chr(10);
	  	  'v': String[Lgth] := chr(11);
	  	  'f': String[Lgth] := chr(12);
	  	  'r': String[Lgth] := chr(13);
	  	  '\': String[Lgth] := '\';
	  	  '"': String[Lgth] := '"';
	  	  '?': String[Lgth] := '?';
	  	  '''': String[Lgth] := '''';
	  	  '0','1','2','3','4','5','6','7','8','9': begin (* octal *)
		    d := ord(Buffer[Chptr])- ord('0');
		    if (Chptr < Chcnt) and (Buffer[Chptr+1] in ['0'..'9']) then
		      begin
		      Chptr := Chptr+1;
		      d := d*8 + ord(Buffer[Chptr])- ord('0');
		      end {then};
		    if (Chptr < Chcnt) and (Buffer[Chptr+1] in ['0'..'9']) then
		      begin
		      Chptr := Chptr+1;
		      d := d*8 + ord(Buffer[Chptr])- ord('0');
		      end {then};
		    String[Lgth] := chr(d);
		    end;
	  	  'x': begin (* hex *)
		    if Chptr < Chcnt then
	  	      Chptr := Chptr+1
		    else Error(326);
		    d := digit_value[ord(Buffer[Chptr])];
		    if (Chptr < Chcnt) and 
		       (Buffer[Chptr+1] in ['0'..'9','a'..'f','A'..'F']) then
		      begin
		      Chptr := Chptr+1;
		      d := d*16 + digit_value[ord(Buffer[Chptr])];
		      end {then};
		    if (Chptr < Chcnt) and 
		       (Buffer[Chptr+1] in ['0'..'9','a'..'f','A'..'F']) then
		      begin
		      Chptr := Chptr+1;
		      d := d*16 + digit_value[ord(Buffer[Chptr])];
		      end {then};
		    String[Lgth] := chr(d);
		    end;
		  otherwise: Error(326);
	          end {case};
		  end
		else String[Lgth] := Buffer[Chptr];
		end
	      else begin
		Stringtoolong := true;
	      end;
	    until (Chptr = Chcnt) or (Buffer[Chptr] = Ch) and 
		  (Buffer[Chptr-1] <> '\');
	    if Stringtoolong then begin
	      Error(301);
	    end;
	    if Chptr = Chcnt then begin
	      Error(351);		(* string crosses line boundary      *)
	    end else begin
	      Chptr := Chptr+1;
	    end;
	    end;
	  Lgth := Lgth-1;
	  (* convert string constant to character constant		     *)
	  if Lgth = 1 then begin
	    Val.Ival := ord(String[1]);
	  end else begin
	    with Val do begin
	      Ival := Lgth;
	      Chars^.ss := String;
	    end {with};
	  end;
	end {case Stringconstsy};
      end {case};
    end;
    Firstsymbol := false;
    Symcnt := Symcnt+1;
999 : ;
  end {procedure Insymbol};
