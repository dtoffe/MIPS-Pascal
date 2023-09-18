{ --------------------------------------------------- }
{ | Copyright (c) 1986 MIPS Computer Systems, Inc.  | }
{ | All Rights Reserved.                            | }
{ --------------------------------------------------- }
{ $Header: upasinit.p,v 1030.7 88/02/18 14:55:05 bettina Exp $ }

#include "upasglob.h"
#include "upasutil.h"
#include "cmplrs/uscan.h"
#include "cmplrs/uini.h"
#include "cmplrs/uwri.h"
#include "upaslex.h"
#include "upasinit.h"
#include "upassym.h"
#include "allocator.h"

(*system-dependent routines*)
(* this page contains all system-dependent routines			     *)
procedure Processargs;
  var
    Str : Filename;
    i, j, k, numoffiles, switchval : integer;
    switch : Identname;
    illegal: boolean;
  begin
    Needsaneoln := false;
    lsb_first := true;
    verbose := false;
    useframeptr := false;
    symname[1] := ' ';
    listname[1] := ' ';
    sourcename[1] := ' ';
    numoffiles := 0;
    if argc < 2 then Abort;
    i := 1;
    while i <> argc do begin
      argv(i, Str);
      if Str[1] <> '-' then begin
	numoffiles := numoffiles+1;
	if numoffiles = 1 then sourcename := Str
	else if numoffiles = 2 then Uname := Str
	else if numoffiles = 3 then symname := Str
	else begin
	  writeln (err, "Too many filenames specified.");
	  Abort;
	end;
      end else if (Str[2] = 't') and (Str[3] = ' ') then begin
	i := i+1;
	argv(i, symname);
      end else if (Str[2] = 'o') and (Str[3] = ' ') then begin
	i := i+1;
	argv(i, Uname);
      end else if (Str[2] = 'l') and (Str[3] = ' ') then begin
	i := i+1;
	argv(i, listname);
	Setswitch('L ', 1);
      end else if (Str[2] = 'w') and (Str[3] = ' ') then begin
	nowarn := true;
	Idwarning := false;
      end else if (Str[2] = 'v') and (Str[3] = ' ') then begin
	verbose := true;
      end else if (Str[2] = 'E') and (Str[3] = 'L') and (Str[4] = ' ')then begin
	lsb_first := true;
      end else if (Str[2] = 'E') and (Str[3] = 'B') and (Str[4] = ' ')then begin
	lsb_first := false;
      end else if (Str[2] = 'F') and (Str[3] = 'P') and (Str[4] = ' ')then begin
	useframeptr := true;
      end else if (Str[2] = 'n') and (Str[3] = 'o') and (Str[4] = 'i') and
		  (Str[5] = 'd') and (Str[6] = 'w') and (Str[7] = 'a') and
	      (Str[8] = 'r') and (Str[9] = 'n') and (Str[10] = ' ') then begin
	Idwarning := false;
      end else if (Str[2] = 'g') then begin 
	debugging_symbols := Str[3] in ['1','2','3', ' '];
	if not debugging_symbols then
	  glevel := 0
	else glevel := ord(Str[3]) - ord('0');
      end else if (Str[2] = 'G') and (Str[3] = ' ') then begin
	i := i + 1;	{ skip numeric argument }
      end else if (Str[2] = 's') and (Str[3] = 't') and (Str[4] = 'd') and
		  (Str[5] = ' ') then begin
	Standrdonly := true;
	Doubleonly := true;
      end else if (Str[2] = 'O') and (Str[3] in [' ', '0', '1', '2', '3', '4'])
		  and (Str[4] = ' ') then begin
      end else if (Str[2] = 'C') and (Str[3] = ' ') then begin
	Runtimecheck := true;
      end else if (Str[2] = 's') and (Str[3] = 't') and (Str[4] = 'd') and
		  (Str[5] = 'u') and (Str[6] = 'm') and (Str[7] = 'p') and
		  (Str[8] = ' ') then begin
	stdump := true;
      end else begin
	switch := blankid;
	j := 2;
	while Str[j] in ['a'..'z', 'A'..'Z'] do begin
	  switch[j-1] := Str[j];
	  j := j+1;
	end {while};
        illegal := false;
        case str[j] of
        '+': switchval := 1;
        '-': switchval := 0;
        ':': begin
	     j := j + 1;
	     switchval := 0;
	     while (str[j] >= '0') and (str[j] <= '9') do
	       begin
	       switchval := switchval * 10 + ord(str[j]) - ord('0');
	       j := j + 1;
	       end;
	     end;
        otherwise: begin
	  write(err, 'upas: Warning: unrecognized option ');
	  k := 1;
	  while str[k] <> ' ' do begin
	    write(err, str[k]);
	    k := k + 1;
	    end {while};
	  writeln(err);
	  flush(err);
	  illegal := true;
	  end;
        end {case};
        if not illegal then
          Setswitch(switch, switchval);
      end;
      i := i+1;
    end {while};
    if numoffiles = 1 then Filenameassign(Uname, 'out:');
    if sourcename[1] = ' ' then Abort;
    if symname[1] = ' ' then Filenameassign(symname, 'upassym');
    if listname[1] = ' ' then Filenameassign(listname, 'upaslist');
    Openstdout(err);
    Openinput(input, sourcename);
    cppfilename := sourcename;
    Uini;
    Inituwrite(Uname);
  end {procedure Processargs};


(*Initialize,Initruntimes,Initreservedwords,Inituwrite,Initbwrite,Initerrormes*)
(************************************************************************)
(************************************************************************)
(*									*)
(*	INITIALIZATION MODULE						*)
(*									*)
(*	The procedure Initialize initializes all the global tables	*)
(*	and variables.							*)
(*									*)
(************************************************************************)
(************************************************************************)
procedure Initialize;

  procedure Init;			(* miscellaneous initialization      *)

    var
      Lmemtype : Memtype;
      i : integer;
      Ch : char;

    begin				(* init 			     *)
      Gheap := nil;
      (***********************************************************************)
      (* user option switches						     *)
      (***********************************************************************)
      Runtimecheck := false;
      Printucode := true;
      Lptfile := false;
      Logfile := false;
      Maxidlength := Identlength;
      Chcntmax := Sbufmax;
#if 0
      InIncludefile := false;
#endif
      Listrewritten := false;
      Showsource := false;
      Optimize := false;
      Idwarning := true;
      nowarn := false;
#if 0
      Commentwarning := false;
#endif
      Noruntimes := false;
      Standrdonly := false;
      Doubleonly := false;
      Resetpossible := true;
#if 0
      Emitsyms := false;
#endif
      stdump := false;
      debugging_symbols := false;
      glevel := 0;
      Extnamcounter := 0;
      Stampctr := 0;
      Tchcnt := 0;
      Headerneeded := true;
#if 0
      Symfcnt := 0;
#endif
      Efile := false;
      (* this value of currname will be printed iff an error occurs before   *)
      (* the program header or in the program header			     *)

      Currname := 'outermost level';
#if 0
      (* Calculates length of a file (File Descriptor Block, actually). This *)
      (* must correspond with description of FDB in PIO. size of FDB = 7     *)
      (* booleans, 9 integers, an identifier, and a file name		     *)
      Fdbsize := Roundup(Stringsize(Filenamelen),
	  Salign)+Roundup(Stringsize(Identlength),
	  Salign)+Roundup(7*Boolsize, Salign)+9*Intsize;
#else
      (* See stdio.h *)
      Fdbsize := 5*wordsize;
#endif

      for Ch := chr(0) to chr(Ordlastchar) do Ssy[Ch] := Othersy;
      for Ch := '0' to '9' do Ssy[Ch] := Intconstsy;
      for Ch := 'A' to 'Z' do Ssy[Ch] := Identsy;
      for Ch := 'a' to 'z' do Ssy[Ch] := Identsy;

      Ssy[''''] := Stringconstsy;
      if not Standrdonly then
        Ssy['"'] := Stringconstsy;
      Ssy['_'] := Identsy;
#if 0
      Ssy['$'] := Identsy;
#endif
      Ssy['{'] := Commentsy;
      Ssy['+'] := Plussy;
      Ssy['-'] := Minussy;
      Ssy['*'] := Mulsy;
      Ssy['/'] := Rdivsy;
      Ssy['('] := Lparentsy;
      Ssy[')'] := Rparentsy;
      Ssy['='] := Eqsy;
      Ssy[','] := Commasy;
      Ssy['.'] := Periodsy;
      Ssy['['] := Lbracksy;
      Ssy[']'] := Rbracksy;
      Ssy[':'] := Colonsy;
      Ssy['^'] := Arrowsy;
      Ssy['@'] := Arrowsy;
      Ssy[';'] := Semicolonsy;
      Ssy['<'] := Ltsy;
      Ssy['>'] := Gtsy;

      (***********************************************************************)
      (* When the first character of a token is mapped to one of the	     *)
      (* following symbols, then then token may be made up of more than one  *)
      (* character							     *)
      (***********************************************************************)

      Trickychars := [Identsy, Intconstsy, Stringconstsy, Lparentsy,
	  Periodsy, Colonsy, Ltsy, Gtsy, Rdivsy, Commentsy, Othersy];
      (* The following characters require lookahead without first checking   *)
      (* for end of broken line 					     *)

      for Ch := chr(0) to chr(Ordlastchar) do begin
	Lookahead[Ch] := Ssy[Ch] in [Intconstsy, Identsy, Rdivsy, Colonsy,
	    Periodsy, Ltsy, Gtsy, Lparentsy, Mulsy];
      end {for};

      (***********************************************************************)
      (* parser 							     *)
      (***********************************************************************)
      Parseright := true;
      Searcherror := true;
      Firstsymbol := true;
      Lastsign := None;

      Mulopsys := [Mulsy, Idivsy, Rdivsy, Modsy, Andsy];
      Addopsys := [Plussy, Minussy, Orsy];
      Relopsys := [Ltsy, Lesy, Gesy, Gtsy, Nesy, Eqsy, Insy];
      Constbegsys := Addopsys+[Intconstsy, Realconstsy, Stringconstsy,
	Identsy];
      Simptypebegsys := Addopsys+[Intconstsy, Realconstsy, Stringconstsy,
	  Identsy, Lparentsy];
      Typebegsys := Addopsys+[Intconstsy, Realconstsy, Stringconstsy,
	  Identsy, Lparentsy, Arrowsy, Packedsy, Arraysy, Recordsy, Setsy,
	  Filesy];
      Typedels := [Arraysy, Recordsy, Setsy, Filesy];
      Blockbegsys := [Labelsy, Constsy, Typesy, Varsy, Proceduresy,
	  Functionsy, Beginsy];
      Selectsys := [Arrowsy, Periodsy, Lbracksy];
      Facbegsys := [Intconstsy, Realconstsy, Stringconstsy, Identsy,
	  Lparentsy, Lbracksy, Notsy, Nilsy];
      Statbegsys := [Beginsy, Gotosy, Ifsy, Whilesy, Repeatsy, Forsy, Withsy,
	  Casesy, Returnsy];

      (***********************************************************************)
      (* error handler							     *)
      (***********************************************************************)
      Errinx := 0;
      Errorcount := 0;

      (***********************************************************************)
      (* storage allocation						     *)
      (***********************************************************************)
      Memblock := 0;
#if 0
      Memblkctr := 1;
      for Lmemtype := Zmt to Tmt do Memcnt[Lmemtype] := 0;
#endif
      PmtMemcnt := 0;
      MmtMemcnt := 0;
      SmtMemcnt := 0;

      (***********************************************************************)
      (* others 							     *)
      (***********************************************************************)
      Forwardpointertype := nil;
      Lastuclabel := 0;
#if 0
      Lastmarker := 1;
#endif
      loop_continue_label := 0;
      loop_break_label := 0;
      current_block := nil;

      with Emptytargetset do begin
	Ival := Setunitsize div 4;
	new1(Chars);
	for i := 1 to Strglgth do Chars^.ss[i] := '0';
      end {with};

      new1(Val.Chars);			{ Initialize the string area for the  }
					{ value record			      }
    end {procedure Init};



  procedure Initreservedwords;

    var
      Rwctr : 1..Rswmaxp1;

    begin
      (* Change RSWMAX if you add a symbol. Frw[N] is the index of the first *)
      (* reserved word of length N (see INSYMBOL for algorithm). Note:	     *)
      (* INSYMBOL expects reserved words to be at most 9 characters long.    *)

      Rwctr := 1;
      Frw[1] := 1;
      Frw[2] := 1;
      Rw[Rwctr] := 'if              ';
      Rsy[Rwctr] := Ifsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'do              ';
      Rsy[Rwctr] := Dosy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'of              ';
      Rsy[Rwctr] := Ofsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'to              ';
      Rsy[Rwctr] := Tosy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'in              ';
      Rsy[Rwctr] := Insy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'or              ';
      Rsy[Rwctr] := Orsy;
      Rwctr := Rwctr+1;
      Frw[3] := Rwctr;
      Rw[Rwctr] := 'end             ';
      Rsy[Rwctr] := Endsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'for             ';
      Rsy[Rwctr] := Forsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'var             ';
      Rsy[Rwctr] := Varsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'div             ';
      Rsy[Rwctr] := Idivsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'mod             ';
      Rsy[Rwctr] := Modsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'set             ';
      Rsy[Rwctr] := Setsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'and             ';
      Rsy[Rwctr] := Andsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'not             ';
      Rsy[Rwctr] := Notsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'nil             ';
      Rsy[Rwctr] := Nilsy;
      Rwctr := Rwctr+1;
      Frw[4] := Rwctr;
      Rw[Rwctr] := 'then            ';
      Rsy[Rwctr] := Thensy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'else            ';
      Rsy[Rwctr] := Elsesy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'with            ';
      Rsy[Rwctr] := Withsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'goto            ';
      Rsy[Rwctr] := Gotosy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'case            ';
      Rsy[Rwctr] := Casesy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'type            ';
      Rsy[Rwctr] := Typesy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'file            ';
      Rsy[Rwctr] := Filesy;
      Rwctr := Rwctr+1;
      Frw[5] := Rwctr;
      Rw[Rwctr] := 'begin           ';
      Rsy[Rwctr] := Beginsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'until           ';
      Rsy[Rwctr] := Untilsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'while           ';
      Rsy[Rwctr] := Whilesy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'array           ';
      Rsy[Rwctr] := Arraysy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'const           ';
      Rsy[Rwctr] := Constsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'label           ';
      Rsy[Rwctr] := Labelsy;
      Rwctr := Rwctr+1;
      Frw[6] := Rwctr;
      Rw[Rwctr] := 'record          ';
      Rsy[Rwctr] := Recordsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'downto          ';
      Rsy[Rwctr] := Downtosy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'packed          ';
      Rsy[Rwctr] := Packedsy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'repeat          ';
      Rsy[Rwctr] := Repeatsy;
      Rwctr := Rwctr+1;
#if 1	/* remove? */
      Rw[Rwctr] := '                ';
      Rsy[Rwctr] := Modulesy;
      Rwctr := Rwctr+1;
#endif
#if 0	/* replaced by 'otherwise' */
      Rw[Rwctr] := 'others          ';
      Rsy[Rwctr] := Otherwisesy;
      Rwctr := Rwctr+1;
#endif
      Rw[Rwctr] := 'return          ';
      Rsy[Rwctr] := Returnsy;
      Rwctr := Rwctr+1;
      Frw[7] := Rwctr;
#if 0
      Rw[Rwctr] := 'include         ';
      Rsy[Rwctr] := Includesy;
      Rwctr := Rwctr+1;
#endif
      Rw[Rwctr] := 'program         ';
      Rsy[Rwctr] := Programsy;
      Rwctr := Rwctr+1;
      Frw[8] := Rwctr;
      Rw[Rwctr] := 'function        ';
      Rsy[Rwctr] := Functionsy;
      Rwctr := Rwctr+1;
      Frw[9] := Rwctr;
      Rw[Rwctr] := 'procedure       ';
      Rsy[Rwctr] := Proceduresy;
      Rwctr := Rwctr+1;
      Rw[Rwctr] := 'otherwise       ';
      Rsy[Rwctr] := Otherwisesy;
      Rwctr := Rwctr+1;
      Frw[10] := Rwctr;

    end {procedure Initreservedwords};


  procedure Initerrormessages;
    begin

      Errmess15[1] := '":" expected   ';
      Errmess15[2] := '")" inserted   ';
      Errmess15[3] := '"(" expected   ';
      Errmess15[4] := '"[" expected   ';
      Errmess15[5] := '"]" expected   ';
      Errmess15[6] := '";" inserted   ';
      Errmess15[7] := '"=" expected   ';
      Errmess15[8] := '"," expected   ';
      Errmess15[9] := '":=" expected  ';
      Errmess15[10] := '"OF" expected  ';
      Errmess15[11] := '"DO" inserted  ';
      Errmess15[12] := '"IF" expected  ';
      Errmess15[13] := '"END" expected ';
      Errmess15[14] := '"THEN" inserted';
      Errmess15[15] := '"EXIT" expected';
      Errmess15[16] := 'Illegal symbol ';
      Errmess15[17] := 'No sign allowed';
      Errmess15[18] := 'Number expected';
      Errmess15[19] := 'Not implemented';
      Errmess15[20] := 'Error in type  ';
      Errmess15[21] := 'Compiler error ';
      Errmess15[22] := 'Unknown machine';
      Errmess15[23] := 'Error in factor';
      Errmess15[24] := 'Too many digits';
      Errmess15[25] := 'Not referenced ';
      Errmess15[26] := 'Not assigned to';
      Errmess15[27] := 'Set too large  ';
      Errmess15[28] := 'Divide by zero ';
      Errmess15[29] := 'Illegal radix  ';
      Errmess15[30] := '":" inserted   ';
      Errmess15[31] := '"]" inserted   ';

      Errmess20[1] := '"BEGIN" expected    ';
      Errmess20[2] := '"UNTIL" expected    ';
      Errmess20[3] := 'Not a known option  ';
      Errmess20[4] := 'Constant too large  ';
      Errmess20[5] := 'Digit must follow   ';
      Errmess20[6] := 'Exponent too large  ';
      Errmess20[7] := 'Constant expected   ';
      Errmess20[8] := 'Simple type expected';
      Errmess20[9] := 'Identifier expected ';
      Errmess20[10] := 'Real type illegal   ';
      Errmess20[11] := 'Multidefined label  ';
      Errmess20[12] := 'Not standard pascal ';
      Errmess20[13] := 'Set type expected   ';
      Errmess20[14] := 'Undefined label     ';
      Errmess20[15] := 'Undeclared label    ';
      Errmess20[16] := 'File name expected  ';
      Errmess20[17] := 'Inter-procedure goto';
      Errmess20[18] := 'Illegal character   ';

      Errmess25[1] := '"TO"/"DOWNTO" expected   ';
      Errmess25[2] := '8 or 9 in octal number   ';
      Errmess25[3] := 'Identifier not declared  ';
      Errmess25[4] := 'Illegal option value     ';
      Errmess25[5] := 'Integer constant expected';
      Errmess25[6] := 'Error in parameterlist   ';
      Errmess25[7] := 'Already forward declared ';
      Errmess25[8] := 'This format for real only';
      Errmess25[9] := 'Comment not opened       ';
      Errmess25[10] := 'Type conflict of operands';
      Errmess25[11] := 'Multidefined case label  ';
      Errmess25[12] := 'For integer only "o"/"h" ';
      Errmess25[13] := 'Array index out of bounds';
      Errmess25[14] := 'String constant expected ';
      Errmess25[15] := 'Unexpected end of file.  ';
      Errmess25[16] := 'Label already declared   ';
      Errmess25[17] := 'End of program not found ';
      Errmess25[18] := 'Type conflict in RETURN  ';
      Errmess25[19] := 'Radix must be integer    ';

      Errmess30[1] := 'String constant is too long   ';
      Errmess30[2] := 'Identifier already declared   ';
      Errmess30[3] := 'Subrange bounds must be scalar';
      Errmess30[4] := 'Incompatible subrange types   ';
      Errmess30[5] := 'Incompatible with tagfieldtype';
      Errmess30[6] := 'Index type may not be integer ';
      Errmess30[7] := 'Type of variable is not array ';
      Errmess30[8] := 'Type of variable is not record';
      Errmess30[9] := 'No such field in this record  ';
      Errmess30[10] := 'Function result not defined   ';
      Errmess30[11] := 'Illegal type of operand(s)    ';
      Errmess30[12] := 'Tests on equality allowed only';
      Errmess30[13] := 'Strict inclusion not allowed  ';
      Errmess30[14] := 'File comparison not allowed   ';
      Errmess30[15] := 'Illegal type of expression    ';
      Errmess30[16] := 'Illegal position for begin    ';

      Errmess30[17] := 'Too many nested withstatements';
      Errmess30[18] := 'Invalid or no program heading ';
      Errmess30[20] := 'Constant expression expected  ';
      Errmess30[21] := 'Memory requirement is too high';
      Errmess30[22] := 'Too many case list elements   ';
      Errmess30[23] := 'Break/continue not in loop';
      Errmess30[24] := 'Number does not follow # sign';
      Errmess30[25] := 'Illegal digit in given radix';
      Errmess30[26] := 'Error in char escape sequence';
      Errmess30[27] := 'Program statement expected';
      Errmess30[28] := 'Not all elements initialized';
      Errmess30[29] := 'Only ordinal subrange allowed ';

      Errmess35[1] := 'String constant crosses line end  "';
      Errmess35[2] := 'Label not declared on this level   ';
      Errmess35[5] := 'File as value parameter not allowed';
      Errmess35[6] := 'Illegal assignment to loop variable';
      Errmess35[7] := 'No packed structure allowed here   ';
      Errmess35[8] := 'Variant must belong to tagfieldtype';
      Errmess35[9] := 'Type of operand(s) must be boolean ';
      Errmess35[10] := 'Set element types not compatible   ';
      Errmess35[11] := 'Assignment to files not allowed    ';
      Errmess35[14] := 'Control variable may not be formal ';
      Errmess35[15] := 'Illegal type of for-controlvariable';
      Errmess35[16] := 'Only packed file of char allowed   ';
      Errmess35[17] := 'Constant not in bounds of subrange ';
      Errmess35[18] := 'Neither referenced nor assigned to ';
      Errmess35[19] := 'New comment begun inside comment   ';
      Errmess35[20] := 'Incongruent parameter              ';
      Errmess35[21] := '[ expected for array initialization';
      Errmess35[22] := 'Incompatible with array index type ';
      Errmess35[23] := 'Array element initialized twice    ';

      Errmess40[1] := 'Identifier is not of appropriate class  ';
      Errmess40[2] := 'Tagfield type must be scalar or subrange';
      Errmess40[3] := 'Index type must be scalar or subrange   ';
      Errmess40[4] := 'Too many nested scopes of identifiers   ';
      Errmess40[5] := 'Pointer forward reference unsatisfied   ';
      Errmess40[6] := 'This error message should not appear    ';
      Errmess40[7] := 'Type of variable must be file or pointer';
      Errmess40[8] := 'Missing corresponding variantdeclaration';
      Errmess40[9] := 'Argument to lbound/hbound must be array ';

      Errmess45[1] := 'Low bound may not be greater than high bound ';
      Errmess45[2] := 'Identifier or "case" expected in fieldlist   ';
      Errmess45[3] := 'Assignment to non-activated function         ';
      Errmess45[4] := 'Initial value not compatible with VAR type   ';
      Errmess45[5] := 'Missing result type in function declaration  ';
      Errmess45[6] := 'N switch must be turned on for mark/release  ';
      Errmess45[7] := 'Index type is not compatible with declaration';
      Errmess45[8] := 'Error in type of standard procedure parameter';
      Errmess45[9] := 'Error in type of standard function parameter ';
      Errmess45[10] := 'Real and string tagfields not implemented    ';
      Errmess45[11] := 'Set element type must be scalar or subrange  ';
      Errmess45[12] := 'I need at least one blank in this line!      ';
      Errmess45[13] := 'No constant or expression for var argument   ';
      Errmess45[15] := 'bodies of forward declared procedure missing ';
      Errmess45[16] := 'Double file specification in program heading ';
      Errmess45[17] := 'Outside of array bounds in initialization    ';
      Errmess45[18] := 'Label section not allowed outside program    ';
      Errmess45[19] := 'Procedure header cannot be in include file   ';
      Errmess45[20] := 'Internal: Error in compiler expr stack       ';

      Errmess50[3] := 'Parameter type does not agree with declaration    ';
      Errmess50[4] := 'Initialization only supported on static variables ';
      Errmess50[5] := 'Label type incompatible with selecting expression ';
      Errmess50[6] := 'Statement must end with ";","end","else"or"until" ';
      Errmess50[7] := 'Underbar may occur only in the middle of an id.   ';

      Errmess50[10] := 'Standrd procedures may not be parameters.        ';

      Errmess55[1] := 'Illegal function result type                           ';
      Errmess55[2] := 'Repetition of result type not allowed if forw. decl.   ';
      Errmess55[3] := 'Repetition of parameter list not allowed if forw. decl.';
      Errmess55[4] := 'Number of parameters does not agree with declaration   ';
      Errmess55[5] := 'Result type of parameter-func does not agree with decl.';
      Errmess55[6] := 'Selected expression must have type of control variable ';
      Errmess55[7] := 'Already declared. previous declaration was not forward ';
      Errmess55[8] := 'Option may not be changed after beginning of program   ';
      Errmess55[9] := 'N switch must be turned off for dispose -- release used';
      Errmess55[10] := 'OTHERWISE already specified in array initialization    ';
      Errmess55[11] := 'Extern declaration only allowed in outermost scope     ';
    end {procedure Initerrormessages};


  begin 				(* initialize			     *)
    Init;
    Initreservedwords;
    Initerrormessages;

    new1(stak);
    stak^.prev := nil;
    stak^.next := nil;
    new(stak^.tree); {to avoid having to check tree=nil when error has occurred}
    stakbot := stak;
  end {procedure Initialize};


(*Enterstdtypes,Enterstdnames,Enterundecl*)
procedure Enterstdtypes;
  (* Create the Structure (type) descriptor blocks for the predefined types, *)
  (* and hang them from known global pointers				     *)
  var
    i : integer;

  begin 				(* enterstdtypes		     *)
    new3(Intptr, Scalar, Standrd);	(* integer			     *)
    with Intptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      bt := btInt;
      Wheredeclared := 0;
      Stsize := Intsize;
      Packsize := Intsize;
      Align := Intalign;
      Packalign := Intalign;
      Stdtype := Jdt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new3(Cardinalptr, Scalar, Standrd);	(* non-neg integer		     *)
    with Cardinalptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      bt := btUInt;
      Wheredeclared := 0;
      Stsize := Intsize;
      Packsize := Intsize;
      Align := Intalign;
      Packalign := Intalign;
      Stdtype := Ldt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new3(Realptr, Scalar, Standrd);	(* real 			     *)
    with Realptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      bt := btFloat;
      Wheredeclared := 0;
      Stsize := Realsize;
      Packsize := Realsize;
      Align := Realalign;
      Packalign := Realalign;
      Stdtype := Rdt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new3(Doubleptr, Scalar, Standrd);
    with Doubleptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      bt := btDouble;
      Wheredeclared := 0;
      Stsize := Doublesize;
      Packsize := Doublesize;
      Align := Doublealign;
      Packalign := Doublealign;
      Stdtype := Qdt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    if Doubleonly then begin
#if 0
      dispose(Realptr);
#endif
      Realptr := Doubleptr;
    end;
    new3(Extendedptr, Scalar, Standrd);
    with Extendedptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Stsize := Extendedsize;
      Packsize := Extendedsize;
      Align := Extendedalign;
      Packalign := Extendedalign;
      Stdtype := Xdt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new3(Charptr, Scalar, Standrd);	(* char 			     *)
    with Charptr^ do begin
      Form := Scalar;
      Scalkind := Standrd;
      ifd := -1;
      packifd := -1;
      bt := btChar;
      Wheredeclared := 0;
      Stsize := Charsize;
      Packsize := Pcharsize;
      Align := Charalign;
      Packalign := 1;
      Stdtype := Ldt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new3(Boolptr, Scalar, Declared);	(* boolean			     *)
    with Boolptr^ do begin
      Form := Scalar;
      Scalkind := Declared;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Stsize := Boolsize;
      Packsize := Rpackunit;
      Align := Boolalign;
      Packalign := Rpackunit;
      Stdtype := Ldt;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new2(Nilptr, SPointer);		(* nil				     *)
    with Nilptr^ do begin
      Form := SPointer;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Stdtype := Hdt;
      Eltype := nil;
      Stsize := Pointersize;
      Packsize := Pointersize;
      Align := Pointeralign;
      Packalign := Pointeralign;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new2(Addressptr, SPointer);		(* pointer to anything	     *)
    with Addressptr^ do begin
      Form := SPointer;
      Stdtype := Adt;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Eltype := nil;
      Stsize := Pointersize;
      Packsize := Pointersize;
      Align := Pointeralign;
      Packalign := Pointeralign;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new2(Heapptr, SPointer);		(* pointer to heap		     *)
    with Heapptr^ do begin
      Form := SPointer;
      Stdtype := Hdt;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Eltype := nil;
      Stsize := Pointersize;
      Packsize := Pointersize;
      Align := Pointeralign;
      Packalign := Pointeralign;
      Hasholes := false;
      Hasfiles := false;
    end {with};
    new2(Anyptr, SPointer);
#if 0	/* was going to use for builtin "pointer" type, but used Nilptr instead. */
    with Anyptr^ do begin
      Form := SPointer;
      Stdtype := Hdt;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Eltype := nil;
      Stsize := Pointersize;
      Packsize := Pointersize;
      Align := Pointeralign;
      Packalign := Pointeralign;
      Hasholes := false;
      Hasfiles := false;
    end {with};
#endif
    new2(Anyfileptr, Files);		(* 'any file'                        *)
    Anyfileptr^.Form := Files;
    new2(Anytextptr, Files);		(* 'any text file'                   *)
    Anytextptr^.Form := Files;
    new2(Anystringptr, Arrays);		(* 'any string'                      *)
    with Anystringptr^ do begin
      Form := Arrays;
      Stsize := Charsize * 5; {so that it is alwasy passed using address}
      Packsize := PCharsize * 5;
      ifd := -1;
      packifd := -1;
      Align := Charalign;
      Packalign := 1;
      Stdtype := Mdt;
      Hasholes := false;
      Hasfiles := false;
    end {with};

    new2(Textptr, Files);		(* text 			     *)
    with Textptr^ do begin
      Form := Files;
      Filetype := Charptr;
      ifd := -1;
      packifd := -1;
      Wheredeclared := 0;
      Filepf := false;
      Textfile := true;
#if 0
      Stdtype := Hdt;
      Componentsize := Pcharsize;
      Stsize := Pointersize;
      Packsize := Pointersize;
      Align := Pointeralign;
      Packalign := Pointeralign;
#else
      Stdtype := Mdt;
      Componentsize := Pcharsize;
      Stsize := Filesize;
      Packsize := Filesize;
      Align := Filealign;
      Packalign := Filealign;
#endif
      Hasholes := false;
      Hasfiles := true;
    end {with};

  end {procedure Enterstdtypes};

procedure Enterstdnames;
  (* insert in the symbol table the identifier descriptor blocks for the     *)
  (* predeclared types, variables, constants, procedures and functions	     *)
  var
    Lidp : Idp;


  procedure Enterstdid (
	      Fidclass : Idclass;
	      Fname : Identname;
	      Fidtype : Strp;
	      Fnext : Idp;
	      Fival : integer);
    var
      Ordinalconst : boolean;
      (* enter in the symbol table the descriptor of a predefined type or    *)
      (* constant							     *)
    begin				(* enterstdid			     *)
      if Fidclass = Types then new2(Lidp, Types)
      else new3(Lidp, Konst, true);
      with Lidp^ do begin
	Klass := Fidclass;
	Idname := Fname;
	Idtype := Fidtype;
	next := Fnext;
	if Fidclass = Konst then begin
	  Isordinal := true;
	  Ival := Fival;
	end;
      end {with};
      Enterid(Lidp);
    end {procedure Enterstdid};

  begin 				(* enterstdnames		     *)

    Enterstdid(Types, 'integer         ', Intptr, nil, 0);
    Enterstdid(Types, 'cardinal        ', Cardinalptr, nil, 0);
    Enterstdid(Types, 'real            ', Realptr, nil, 0);
    Enterstdid(Types, 'double          ', Doubleptr, nil, 0);
    Enterstdid(Types, 'extended_float  ', Extendedptr, nil, 0);
    Enterstdid(Types, 'char            ', Charptr, nil, 0);
    Enterstdid(Types, 'boolean         ', Boolptr, nil, 0);
    Enterstdid(Types, 'text            ', Textptr, nil, 0);
    Enterstdid(Types, 'pointer         ', Nilptr, nil, 0);
    Enterstdid(Konst, 'maxint          ', Intptr, nil, Tgtmaxint);

    Enterstdid(Konst, 'true            ', Boolptr, nil, 1);
    Enterstdid(Konst, 'false           ', Boolptr, Lidp, 0);

    with Boolptr^ do begin
      Fconst := Lidp;
      Tlev := 0;
      Dimension := 1;
    end {with};

    new2(Inputptr, Vars);
    with Inputptr^ do begin
      Klass := Vars;
      Idname := 'input           ';
      Idtype := Textptr;
      Vkind := Actual;
      next := nil;
      Vblock := 1;
      Vaddr := 0;
      Vmty := Smt;
      Vaddr := 0;
      Referenced := true;
      Loopvar := false;
      Vexternal := true;
    end {with};
    Enterid(Inputptr);

    new2(Outputptr, Vars);
    with Outputptr^ do begin
      Klass := Vars;
      Idname := 'output          ';
      Idtype := Textptr;
      Vkind := Actual;
      next := nil;
      Vblock := 1;
      Vaddr := 0;
      Vmty := Smt;
      Referenced := true;
      Loopvar := false;
      Vexternal := true;
    end {with};
    Enterid(Outputptr);

    new2(Sysoutptr, Vars);
    with Sysoutptr^ do begin
      Klass := Vars;
      Idname := 'err';
      Idtype := Textptr;
      Vkind := Actual;
      next := nil;
      Vblock := 1;
      Vaddr := 0;
      Vmty := Smt;
      Referenced := true;
      Loopvar := false;
      Vexternal := true;
    end {with};
    Enterid(Sysoutptr);

    new2(Argcptr, Vars);
    with Argcptr^ do begin
      Klass := Vars;
      Idname := 'argc';
      Idtype := Intptr;
      Vkind := Actual;
      next := nil;
#if 0
      Vblock := Symdef('argc', 0, stGlobal, scNil, btNil, true, false);
#endif
      Vaddr := 0;
      Vmty := Smt;
      Referenced := true;
      Loopvar := false;
      Vexternal := true;
    end {with};
    Enterid(Argcptr);

  end {procedure Enterstdnames};

procedure Enterundecl;

  (***************************************************************************)
  (* create identifier descriptor blocks for an 'undeclared' or 'undefined'  *)
  (* object of each class, and hang them from global variables, for searchid *)
  (* to return when an identifier is not found. this way, an idptr will      *)
  (* never be nil							     *)
  (***************************************************************************)

  begin 				(* enterundecl			     *)
    new2(Utypptr, Types);
    with Utypptr^ do begin
      Klass := Types;
      Idname := '                ';
      Idtype := nil;
      next := nil;
    end {with};
    new2(Ucstptr, Konst);
    with Ucstptr^ do begin
      Klass := Konst;
      Idname := '                ';
      Idtype := nil;
      next := nil;
      Ival := 0;
      Isordinal := true;
    end {with};
    new2(Uvarptr, Vars);
    with Uvarptr^ do begin
      Klass := Vars;
      Idname := '                ';
      Idtype := nil;
      next := nil;
      Vblock := 0;
      Vaddr := 0;
      Vkind := Actual;
      Loopvar := false;
      Vexternal := false;
    end {with};
    new2(Ufldptr, Field);
    with Ufldptr^ do begin
      Klass := Field;
      Idname := '                ';
      Idtype := nil;
      next := nil;
      Fldaddr := 0;
      Inpacked := false;
    end {with};
    new4(Uprocptr, Proc, Regular, Actual);
    with Uprocptr^ do begin
      Klass := Proc;
      Prockind := Regular;
      Pfkind := Actual;
      Idname := '                ';
      Idtype := nil;
      Forwdecl := false;
      next := nil;
#if 0
      Externdecl := false;
#endif
      Externproc := true;
      Pflev := 0;
      Nonstandard := false;
    end {with};
    new4(Ufuncptr, Func, Regular, Actual);
    with Ufuncptr^ do begin
      Klass := Func;
      Prockind := Regular;
      Pfkind := Actual;
      Idname := '                ';
      Idtype := nil;
      next := nil;
      Forwdecl := false;
      Nonstandard := false;
      Externproc := true;
      Pflev := 0;
      Resmemtype := Zmt;
      Resaddr := 0;
    end {with};
  end {procedure Enterundecl};

(*Enterstdprocs*)
procedure Enterstdprocs;
  (* enter standard procedures and functions into the symbol table	     *)
  var
    Lmty : Memtype;
    Lparnumber : integer;
    Nullstrptr : Strp;
    Minusoneptr, Zeroptr, Oneptr, Nullstridptr: Idp;
    Listhead, Listtail, Procidp : Idp;

  procedure Enterspecialproc (
	      Fname : Identname;
	      Fkey : Stdprocfunc;
	      Fklass : Idclass);

    var
      Lidp : Idp;

      (***********************************************************************)
      (* create an Id record for a procedure/function needing special	     *)
      (* parsing							     *)
      (***********************************************************************)

    begin
      new3(Lidp, Proc, Special);
      with Lidp^ do begin
	Klass := Fklass;
	Prockind := Special;
	Idname := Fname;
	Idtype := nil;
	next := nil;
	Key := Fkey;
      end {with};
      Enterid(Lidp);
    end {procedure Enterspecialproc};

  procedure Enterinlinefunc (
	      Fname : Identname;
	      Finst : Uopcode;
	      FDtypes : Dtypeset;
	      FResdtype : Strp);
    (* create an Id record for a function that is generated inline	     *)

    var
      Lidp : Idp;

    begin
      new3(Lidp, Proc, Inline);
      with Lidp^ do begin
	Klass := Func;
	Prockind := Inline;
	Idname := Fname;
	Idtype := nil;
	next := nil;
	Dtypes := FDtypes;
	Resdtype := FResdtype;
	Uinst := Finst;
      end {with};
      Enterid(Lidp);
    end {procedure Enterinlinefunc};

#if 0
  procedure Enterstdstring (
	  var Stringptr : Strp;
	      Strsize : integer);
    (* Create a Structure (type) descriptor stringptr, for a string with     *)
    (* size Strsize. This is for standard procedures that take string	     *)
    (* arguments							     *)

    var
      Lstrp : Strp;


    begin				(* enterstdstring		     *)
      new2(Lstrp, Subrange);		(* create Structure for index	     *)
      with Lstrp^ do begin
	Form := Subrange;
	Hosttype := Intptr;
	Vmin := 1;
	Vmax := Strsize;
	Stsize := Intsize;
	Packsize := Intsize;
	Align := Intalign;
	Packalign := Intalign;
	Stdtype := Jdt;
        ifd := -1;
        packifd := -1;
	Wheredeclared := 0;
	Hasholes := false;
	Hasfiles := false;
      end {with};
      new2(Stringptr, Arrays);		(* create Structure for array	     *)
      with Stringptr^ do begin
	Form := Arrays;
	Arraypf := true;
        ifd := -1;
        packifd := -1;
	Wheredeclared := 0;
	Aeltype := Charptr;
	Inxtype := Lstrp;
	Aelsize := Pcharsize;
	Stsize := Stringsize(Strsize);
	Packsize := Stsize;
	Align := Charalign;
	Packalign := Charalign;
	Stdtype := Mdt;
	Hasholes := true;
	Hasfiles := false;
      end {with};
    end {procedure Enterstdstring};
#endif

  procedure Enterstdparameter (
	      Fidtype : Strp;
	      Fidkind : Idkind;
	      Defaultidp : Idp);
    (* Add one more element to the list of parameters for a predefined	     *)
    (* procedure/function						     *)

    var
      Lmty : Memtype;
      Lidp : Idp;
    begin				(* enterstdparameter		     *)
      new2(Lidp, Vars);
      if Listhead = nil then begin
#if 0
	for Lmty := Zmt to Tmt do Memcnt[Lmty] := 0;
#endif
	Lparnumber := 1;
      end else Lparnumber := Lparnumber+1;
      (* The length of the string is passed as an extra parameter.	     *)
#if 0
      if Fidtype = Anystringptr then Lparnumber := Lparnumber+1;
#endif
      with Lidp^ do begin
	Klass := Vars;
	Idname := '                ';
	Idtype := Fidtype;
	Vkind := Fidkind;
	if next = nil then Vblock := 0;
	Vmty := Zmt;
	Vaddr := 0;
	next := nil;
	Isparam := true;
	Default := Defaultidp;
      end {with};
      (* add to end of parameter list					     *)
      if Listhead = nil then Listhead := Lidp
      else Listtail^.next := Lidp;
      Listtail := Lidp;
    end {procedure Enterstdparameter};


  procedure Enterregularproc (
	      Fname,
	      Fextname : Identname;
	      Fidtype : Strp;
	      Nonstd : boolean);
    (* enter in the symbol table the id record for a predefined 	     *)
    (* procedure/function; Listhead should be the list of parameters, and    *)
    (* Fidtype the type of the function result, or NIL if not a function; a  *)
    (* ptr to the new record is returned in Procidp (global)		     *)

    var
      junk: integer;
      iaux: cardinal;
    begin				(* Enterregularproc		     *)
      if Fidtype <> nil then begin
	new4(Procidp, Func, Regular, Actual);
	Procidp^.Klass := Func;
      end else begin
	new4(Procidp, Proc, Regular, Actual);
	Procidp^.Klass := Proc;
      end;
      with Procidp^ do begin
	Prockind := Regular;
	Pfkind := Actual;
	Pfmemblock := 0;
	Nonstandard := Nonstd;
	Idtype := Fidtype;
	next := Listhead;
	Forwdecl := true;
	if Listhead = nil then Parnumber := 0
	else Parnumber := Lparnumber;
	Pflev := 1;			(* level 1 for standard procedure    *)
	Externproc := true;
#if 0
	Externdecl := true;
#endif
	Idname := Fname;
	if Fidtype <> nil then
	  iaux := Typetoaux(Fidtype, false, true, false, false)
	else iaux := indexNil;
        symndx := st_idn_index_fext(st_extadd(Symaddextstr(Fextname), 0, stProc,
				scNil, iaux), 1);  
	if debugging_symbols then
	  junk := st_auxadd(0); {for type of function}
      end {with};
      Enterid(Procidp);
    end {procedure Enterregularproc};

  var
    junk : integer;
  begin 				(* Enterstdprocs		     *)
#if 0
    new4(Stdfileinitidp, Proc, Regular, Actual);
    with Stdfileinitidp^ do begin
      Klass := Proc;
      Prockind := Regular;
      Pfkind := Actual;
      Idtype := nil;
      next := nil;
      Forwdecl := true;
      Parnumber := 5;
      Pflev := 1;
#if 0
      Externdecl := false;
#endif
      Externproc := true;
      Pfmemblock := 0;
      Idname := 'pascal_runtime_init';
      symndx := st_idn_index_fext(st_extadd(Symaddextstr(Idname), 0, stProc, 
				scNil, indexNil), 1);  
      if debugging_symbols then
        junk := st_auxadd(0); {for type of function}
    end {with};
#endif

(* enter proc/funcs needing special treatment *)
    Enterspecialproc('read            ', Spread, Proc);
    Enterspecialproc('readln          ', Spreadln, Proc);
    Enterspecialproc('write           ', Spwrite, Proc);
    Enterspecialproc('writeln         ', Spwriteln, Proc);
    Enterspecialproc('pack            ', Sppack, Proc);
    Enterspecialproc('unpack          ', Spunpack, Proc);
    Enterspecialproc('new             ', Spnew, Proc);
    Enterspecialproc('dispose         ', Spdispose, Proc);
    Enterspecialproc('break',		 Spbreak, Proc);
    Enterspecialproc('continue',	 Spcontinue, Proc);
    Enterspecialproc('assert',		 Spassert, Proc);
    Enterspecialproc('first',		 Spfirst, Func);
    Enterspecialproc('last',		 Splast, Func);
    Enterspecialproc('lbound',		 Splbound, Func);
    Enterspecialproc('hbound',		 Sphbound, Func);
    Enterspecialproc('sizeof',		 Spsizeof, Func);

(* enter funcs for which inline code will be generated *)
    Enterinlinefunc('abs             ', Uabs, [Jdt, Ldt, Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('sqr             ', Usqr, [Jdt, Ldt, Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('odd             ', Uodd, [Jdt, Ldt], Boolptr);
    Enterinlinefunc('ord             ', Ucvt, [Adt, Hdt, Jdt, Ldt], Intptr);
    Enterinlinefunc('chr             ', Ucvt, [Jdt, Ldt], Charptr);
    Enterinlinefunc('pred            ', Udec, [Jdt, Ldt], nil);
    Enterinlinefunc('succ            ', Uinc, [Jdt, Ldt], nil);
    Enterinlinefunc('round           ', Urnd, [Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('trunc           ', Ucvt, [Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('min             ', Umin, [Jdt, Ldt, Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('max             ', Umax, [Jdt, Ldt, Rdt, Qdt, Xdt], nil);
    Enterinlinefunc('bitand          ', Uand, [Jdt, Ldt], nil);
    Enterinlinefunc('bitor           ', Uior, [Jdt, Ldt], nil);
    Enterinlinefunc('bitxor          ', Uxor, [Jdt, Ldt], nil);
    Enterinlinefunc('bitnot          ', Unot, [Jdt, Ldt], nil);
    Enterinlinefunc('lshift          ', Ushl, [Jdt, Ldt], nil);
    Enterinlinefunc('rshift          ', Ushr, [Jdt, Ldt], nil);

(* enter all other standard proc/funcs *)

    new3(Zeroptr, Konst, true);
    with Zeroptr^ do begin
      Klass := Konst;
      Idtype := Intptr;
      Ival := 0;
      Isordinal := true;
    end {with};
    new3(Oneptr, Konst, true);
    with Oneptr^ do begin
      Klass := Konst;
      Idtype := Intptr;
      Ival := 1;
      Isordinal := true;
    end {with};
    new3(Minusoneptr, Konst, true);
    with Minusoneptr^ do begin
      Klass := Konst;
      Idtype := Intptr;
      Ival := -11;
      Isordinal := true;
    end {with};

#if 0
    Enterstdstring(Nullstrptr, 1);
#endif
    new3(Nullstridptr, Konst, false);
    with Nullstridptr^ do begin
      Idtype := Anystringptr;
      Klass := Konst;
      Isordinal := false;
      Sval.Len := 1;
      new1(Sval.Chars);
      Sval.Chars^.ss[1] := ' ';
    end {with};

    Listhead := nil;
    Enterstdparameter(Anyptr, Formal, nil);
    Enterregularproc('mark            ', 'mark            ', nil, true);
    Enterregularproc('release         ', 'release         ', nil, true);

    Listhead := nil;
    Enterstdparameter(Anyfileptr, Actual, nil);
    Enterregularproc('get             ', 'get             ', nil, false);
    Getptr := Procidp;
    Enterregularproc('put             ', 'put             ', nil, false);
    Putptr := Procidp;
#if 0
    Enterregularproc('bufval          ', 'bufval          ', Charptr, true);
    Bufvalptr := Procidp;
#endif
    Enterregularproc('close           ', 'fclose          ', nil, true);
    Closeptr := Procidp;
    Enterregularproc('flush           ', 'fflush          ', nil, true);

#if 0
    Listhead := nil;
    Enterstdparameter(Anyfileptr, Actual, nil);
    Enterstdparameter(Intptr, Actual, nil);
    Enterregularproc('strwrite        ', '$STRWRITE       ', nil, true);
    Enterregularproc('strset          ', '$STRSET         ', nil, true);
#endif

#if 1
    Listhead := nil;
    Enterstdparameter(Anyfileptr, Actual, nil);
    Enterregularproc('filesize        ', 'filesize        ', Intptr, true);
    Enterregularproc('curpos          ', 'curpos          ', Intptr, true);
#endif

#if 1
    Listhead := nil;
    Enterstdparameter(Anyfileptr, Actual, nil);
    Enterstdparameter(Intptr, Actual, Zeroptr);
    Enterregularproc('seek            ', 'seek            ', nil, true);
#endif

    Listhead := nil;
    Enterstdparameter(Anyfileptr, Actual, Inputptr);
    Enterregularproc('eof             ', 'eof             ', Boolptr, false);

    Listhead := nil;
    Enterstdparameter(Anytextptr, Actual, Inputptr);
    Enterregularproc('eoln            ', 'eoln            ', Boolptr, false);

    Listhead := nil;
    Enterstdparameter(Anytextptr, Actual, Outputptr);
    Enterregularproc('page            ', 'page            ', nil, false);

    Listhead := nil;
    Enterstdparameter(Anyfileptr, Formal, nil /*Inputptr*/);
    Enterstdparameter(Anystringptr, Actual, Nullstridptr);
    Enterstdparameter(Intptr, Actual, Zeroptr);
    Enterregularproc('reset           ', 'reset           ', nil, false);
    Resetptr := Procidp;

    Listhead := nil;
    Enterstdparameter(Anyfileptr, Formal, nil /*Outputptr*/);
    Enterstdparameter(Anystringptr, Actual, Nullstridptr);
    Enterstdparameter(Intptr, Actual, Zeroptr);
    Enterregularproc('rewrite         ', 'rewrite         ', nil, false);
    Rewriteptr := Procidp;

(*log,sin,cos,exp,sqrt,atn*)

    Listhead := nil;
    Enterstdparameter(Doubleptr, Actual, nil);
    Enterregularproc('cos             ', 'cos             ', Doubleptr, false);
    Enterregularproc('exp             ', 'exp             ', Doubleptr, false);
    Enterregularproc('sqrt            ', 'sqrt            ', Doubleptr, false);
    Enterregularproc('ln              ', 'log             ', Doubleptr, false);
    Enterregularproc('arctan          ', 'atan            ', Doubleptr, false);
    Enterregularproc('sin             ', 'sin             ', Doubleptr, false);

    Listhead := nil;
    Enterregularproc('random          ', '__random_float  ', Doubleptr, true);

    Listhead := nil;
    Enterstdparameter(Intptr, Actual, Oneptr);
    Enterregularproc('clock           ', 'clock           ', Intptr, true);

    Listhead := nil;
    Enterstdparameter(Intptr, Actual, Zeroptr);
    Enterregularproc('halt            ', 'exit            ', nil, true);

#if 0
    Listhead := nil;
    Enterstdparameter(Intptr, Formal, nil);
    Enterstdparameter(Intptr, Formal, nil);
    Enterstdparameter(Intptr, Formal, nil);
    Enterregularproc('pdate           ', '$PDATE          ', nil, true);
#endif

    Listhead := nil;
    Enterstdparameter(Anystringptr, Formal, nil);
    Enterstdparameter(Intptr, Actual, nil);
    Enterregularproc('date            ', '__date          ', nil, true);
    Enterregularproc('time            ', '__time          ', nil, true);

    Listhead := nil;
    Enterstdparameter(Intptr, Actual, nil);
    Enterstdparameter(Anystringptr, Formal, nil);
    Enterstdparameter(Intptr, Actual, nil);
    Enterregularproc('argv            ', 'get_arg         ', nil, true);

  end {procedure Enterstdprocs};


procedure Initruntimes;

(* initializes tables used for calls of runtime procedures *)

  procedure rtdef (
	      rt : Supports;
	      name : Identname;
	      Fidtype : Strp;
	      pop : integer);
    var
      junk, isym: integer;
      iaux: cardinal;
    begin
      if Fidtype <> nil then
	iaux := Typetoaux(Fidtype, false, true, false, false)
      else iaux := indexNil;
      isym := st_extadd(Symaddextstr(name), 0, stProc, scNil, iaux);
      Runtimesupport.Symndx[rt] := st_idn_index_fext(isym, 1);
      if debugging_symbols then
        junk := st_auxadd(0); {for type of function}
      if Fidtype = nil then
        Runtimesupport.Dty[rt] := Pdt
      else Runtimesupport.Dty[rt] := Fidtype^.Stdtype;
      Runtimesupport.pop[rt] := pop;
    end {procedure rtdef};

  begin 				(* Initruntimes 		     *)
    rtdef(Allocate,	'new',             Heapptr, 2);
    rtdef(Free,		'dispose',         nil, 1);
    rtdef(Ifile,	'initfile',        nil, 5);
    rtdef(Peekchar,	'peek_char',       Charptr, 1);
    rtdef(Nextchar,	'next_char',       nil, 1);
    rtdef(Readline,	'readln',          nil, 1);
    rtdef(Readinteger,	'read_integer',    Intptr, 2);
    rtdef(Readcardinal,	'read_cardinal',   Cardinalptr, 2);
    rtdef(Readintrange,	'read_integer_range',   Intptr, 4);
    rtdef(Readreal,	'read_real',       Realptr, 1);
    rtdef(Readdouble,	'read_double',     Doubleptr, 1);
    rtdef(Readextended,	'read_extended',   Extendedptr, 1);
    rtdef(Readstring,	'read_string',     nil, 3);
    rtdef(Readenum,	'read_enum',       Cardinalptr, 4);
    rtdef(Readchar,	'read_char',       Charptr, 1);
    rtdef(Readcharrange,'read_char_range', Charptr, 3);
    rtdef(Readboolean,	'read_boolean',    Cardinalptr, 1);
    rtdef(Readset,	'read_set',        nil, 6);
    rtdef(Writeline,	'writeln',         nil, 1);
    rtdef(Writeinteger,	'write_integer',   nil, 4);
    rtdef(Writecardinal,'write_cardinal',  nil, 4);
    rtdef(Writeboolean,	'write_boolean',   nil, 3);
    rtdef(Writechar,	'write_char',      nil, 3);
    rtdef(Writereal,	'write_real',      nil, 4);
    rtdef(Writedouble,	'write_double',    nil, 4);
    rtdef(Writeextended,'write_extended',  nil, 4);
    rtdef(Writestring,	'write_string',    nil, 4);
    rtdef(Writeenum,	'write_enum',      nil, 4);
    rtdef(Writeset,	'write_set',       nil, 8);
    rtdef(Caseerror,	'caseerror',       nil, 4);
    rtdef(Assertionfailure,	'assertfail',      nil, 2);
    rtdef(Nloc_goto,	'__pc_nloc_goto',       nil, 2);

    Readsupport[Jdt, Scalar] := Readinteger;
    Readsupport[Jdt, Subrange] := Readintrange;

    Readsupport[Ldt, Scalar] := Readcardinal;
    Readsupport[Ldt, Subrange] := Readintrange;

    Readsupport[Rdt, Scalar] := Readreal;
    Readsupport[Qdt, Scalar] := Readdouble;
    Readsupport[Xdt, Scalar] := Readextended;

    Writesupport[Jdt] := Writeinteger;
    Writesupport[Ldt] := Writecardinal;
    Writesupport[Rdt] := Writereal;
    Writesupport[Qdt] := Writedouble;
    Writesupport[Xdt] := Writeextended;

    Widthdefault[Jdt] := 12;
    Widthdefault[Ldt] := 12;
    Widthdefault[Rdt] := 15;		(* space, sign, 8 digits with point, *)
					(* exponent marker, exponent sign, 2 *)
					(* exponent digits		     *)
    Widthdefault[Qdt] := 24;		(* 16 digits, 3 exponent digits      *)
    Widthdefault[Xdt] := 29;		(* 20 digits, 4 exponent digits      *)

  end {procedure Initruntimes};
