/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: upasglob.h,v 1030.7 88/02/18 14:55:28 bettina Exp $ */

#include "cmplrs/mipspascal.h"
#include "cmplrs/usys.h"
#include "cmplrs/ucode.h"
#include "cmplrs/stinfc.h"
#include "symconst.h"

#define new1(_x) 		_x := alloc_new(sizeof(_x^), Gheap)
#ifdef PASTEL
#define new2(_x, _y) 		_x := alloc_new(sizeof(_x^), Gheap)
#define new3(_x, _y, _z) 	_x := alloc_new(sizeof(_x^), Gheap)
#define new4(_x, _y, _z, _w) 	_x := alloc_new(sizeof(_x^), Gheap)
#else
#define new2(_x, _y) 		_x := alloc_new(sizeof(_x^, _y), Gheap)
#define new3(_x, _y, _z) 	_x := alloc_new(sizeof(_x^, _y, _z), Gheap)
#define new4(_x, _y, _z, _w)    _x := alloc_new(sizeof(_x^, _y, _z, _w), Gheap)
#endif

#define indexNil 16#fffff

#define BIGENDIAN	0
#define LITTLEENDIAN	1

const
  Header = 'UPAS 6/86';                 (* list file heading                 *)
  Shortheader = 'upas';                 (* monitor heading                   *)

  Displimit = 20;			(* maximum declaration-scope nesting *)
  Maxerr = 20;				(* maximum errors reported in 1      *)
					(* source line			     *)
  Maxprserr = 4;			(* maximum token-specific errors     *)
					(* reported in 1 source line	     *)

  Rswmax = 43;				(* reserved words		     *)
  Rswmaxp1 = 44;			(* reserved words plus 1	     *)
  Sbufsize = 1600;			(* size of source line buffer (but   *)
					(* there is no limit to length of    *)
					(* source lines)		     *)
  Sbufmax = 1599;			(* Sbufsize - 1 		     *)
  Listlen = 72; 			(* line length of listing device     *)
#if 0
  Maxblocks = 1023;			(* maximum number of procedures      *)
					(* allowed			     *)
  Maxtypes = 1023;			(* maximum number of types allowed   *)
#endif
  Maxnest = 20; 			(* maximum number of nested	     *)
					(* procedures			     *)
  Maxnestfor = 60;			(* maximum number of nested (for,    *)
					(* while, repeat)                    *)
  Maxtemps = 50;			(* maximum number of temporaries     *)
					(* active at one time within one     *)
					(* procedure			     *)
  intRmtoffset = 64;			(* offset in R memory of R2 *)
  fpRmtoffset = 1024;			(* offset in R memory of 1st fp reg  *)
  Wordoffmask = 5;			{ for computing "DIV Wordsize" }

  Filesize = 2*Pointersize;		{ size of a file variable }
  Filealign = Pointeralign;		{ alignment of a file variable }
  File_stdio_offset = 0*Pointersize;	{ offset of stdio FILE* }
  File_name_offset = 1*Pointersize;	{ offset of file name pointer }

type					(* Ucode			     *)
  Levrange = 0..Maxnest;		(* lexical (procedure and record     *)
					(* nesting) levels		     *)
  Nestforrange = 0..Maxnestfor; 	(* (for, while, repeat) nesting      *)
#if 0
  Blockrange = 0..Maxblocks;		(* procedure numbers		     *)
#else
  Blockrange = integer;
#endif
  Addrrange = integer;			(* memory addresses, in bits	     *)
  Sizerange = cardinal;		(* size of data objects, in bits     *)
  Bitrange = integer;			(* for bit sizes, less than a word   *)

  (***************************************************************************)
  (* for keeping track of memory allocation:				     *)
  (***************************************************************************)
#if 0
  Memsize = packed array[Memtype] of Addrrange;
#endif

  Dtypeset = set of Datatype;

  Srcline = array[1..Sbufsize] of char;

  (***************************************************************************)
  (* structures 							     *)
  (***************************************************************************)
  Strp = ^Structure;			(* pointer to a type descriptor, or  *)
					(* to a part of it		     *)
  Idp = ^Identifier;			(* pointer to a user-defined	     *)
					(* identifier descriptor	     *)

  Structform = (Scalar, Subrange, SPointer, Power, Arrays, Records, Files,
	  Tagfwithid, Tagfwithoutid, Variant);

  Declkind = (Standrd, Declared);	(* Declared scalar = enumerated type *)

  Structure = packed record		(* describes a type or part of it    *)
      Stsize : Sizerange;		(* size 			     *)
      Packsize : Sizerange;		(* size if in packed structure	     *)
      Align : Sizerange;		(* alignment			     *)
      Packalign : Sizerange;		(* alignment if in packed structure  *)
      Typendx : integer;		(* aux table index for type       *)
      PackTypendx : integer;		(* aux table index for packed type *)
      ifd: integer;		(* if -1, indicate type not yet in table *)
      packifd: integer;		(* if -1, indicate type not yet in table *)
      {PackTypendx and packifd used only in cases scalar, subrange and power}
      Stdtype : Datatype;		(* ucode data type		     *)
      Hasholes, 			(* contains hole somewhere within it *)
      Hasfiles : boolean;		(* contains files somewhere within   *)
					(* it				     *)
      Wheredeclared : Blockrange;	(* block number of proc where	     *)
					(* declared			     *)

      case Form : Structform of
	Scalar : (
	  case Scalkind : Declkind of	(* for enumerated types:	     *)
	    Standrd : (
	      bt: integer);		{the st basic type for it}
	    Declared : (
	      Tlev : Levrange;		(* level when declared		     *)
	      Fconst : Idp;		(* to the first element 	     *)
	      Saddress : Addrrange;	(* of name table for i/o	     *)
	      Dimension : integer;	(* number of elements		     *)
	      Scalaridn: integer);	(* dense blk number of the begin
					   entry in symbol table *)
	);
	Subrange : (
	  Hosttype : Strp;		(* to the unbound type		     *)
	  Vmin, Vmax : integer);	(* values of the boundaries	     *)
	SPointer : (
	  Eltype : Strp);		(* to the pointed type		     *)
	Power : (
	  Basetype : Strp;		(* to the type of the element	     *)
	  Hardmin, Hardmax,		(* absolute limits of set	     *)
	  Softmin, Softmax :		(* moveable limits of set	     *)
	    integer);
	Arrays : (
	  Arraypf : boolean;		(* true if packed		     *)
	  Aeltype,			(* type of the array element	     *)
	  Inxtype : Strp;		(* type of the array subscript	     *)
	  Aelsize : Sizerange);		(* size of each element 	     *)
	Records : (
	  Recordpf : boolean;		(* true if packed		     *)
	  Recfirstfield : Idp;		(* pointer to the first field	     *)
	  Recvar : Strp;		(* pointer to the variant tag	     *)
	  Recidn: integer);		(* dense blk number of the begin
					   entry in symbol table *)
	Files : (
	  Filepf : boolean;		(* true if packed file		     *)
	  Textfile : boolean;		(* true if the file is type text     *)
	  Filetype : Strp;		(* type of the file elements	     *)
	  Componentsize : integer);
	Tagfwithid,			(* variant tag			     *)
	Tagfwithoutid : (
	  Fstvar,			(* head of the chain of variants     *)
	  Elsevar : Strp;		(* represents undeclared variants    *)
	  case boolean of		(* ptr to Id representing named tag  *)
	    true : (
	      Tagfieldp : Idp); 	(* ptr to Structure representing     *)
					(* unnamed tag			     *)
	    false : (
	      Tagfieldtype : Strp) (* if no name was given	     *)
	);
	Variant : (
	  Nxtvar,			(* next variant in list 	     *)
	  Subvar : Strp;		(* to the variant inside this one    *)
	  Varfirstfield : Idp;		(* to the first field		     *)
	  Varval : integer)		(* value that makes this variant     *)
					(* active			     *)
    end {record};

  (***************************************************************************)
  (* identifiers							     *)
  (***************************************************************************)
  Parp = ^Programparameter;
  Programparameter =			(* describes a program parameter     *)
    packed record
      Nextparp : Parp;			(* chain of program parameters	     *)
      Fileid : Identname;		(* the actual id-name of the	     *)
					(* parameter			     *)
    end {record};


  (***************************************************************************)
  (* standard procedures and functions requiring special handling	     *)
  (***************************************************************************)
  Stdprocfunc = (Spread, Spreadln, Spwrite, Spwriteln, Sppack, Spunpack,
	  Spnew, Spdispose, Spbreak, Spcontinue, Spassert, Spsizeof,
	  Spfirst, Splast, Splbound, Sphbound, Spargv);

  (***************************************************************************)
  (* different kinds of identifiers					     *)
  (***************************************************************************)
  Idclass = (Types, Konst, Vars, Field, Proc, Func, Labels, Progname);

  Setofids = set of Idclass;
  Idkind = (Actual, Formal);		(* for parameters		     *)

  (***************************************************************************)
  (* describes a user-defined identifier				     *)
  (***************************************************************************)

  Proctype = (Special, Inline, Regular);

  Identifier = packed record

      Idname : Identname;		(* the actual name	     *)
      symndx : integer;			(* indexed returned by st routines *)
      Llink, Rlink : Idp;		(* alphabetic binary tree    *)
      Idtype : Strp;			(* to the type descriptor    *)
      Next : Idp;			(* makes chains of params, decl     *)
					(* scalars, etc.		    *)
      Referenced : boolean;		(* keeps track of unused identifiers *)
      case Klass : Idclass of
	Types : ();
	Konst : (
	  case Isordinal : boolean of
	    true : (
	      Ival : integer);
	    false : (
	      Sval : Strg)
	);
	Vars : (
	  Vkind : Idkind;		(* formal: var parameter	     *)
	  Assignedto : boolean; 	(* for warnings 		     *)
	  Isparam : boolean;		(* for warnings: param or var?	     *)
	  Default : Idp;		(* default value of parameter	     *)
	  Loopvar : boolean;		(* true if in use as a loop varable  *)
	  Vblock : Blockrange;		(* block number 		     *)
	  Vmty : Memtype;		(* ucode memory type		     *)
	  Vaddr : Addrrange;		(* ucode offset or,for long value    *)
					(* parameters: address where the     *)
					(* address of the actual parameter   *)
					(* is passed			     *)
	  Vexternal : boolean;		{ whether it is ESYM }
	  Loopvar_idtype: Strp);	{used during body of for loop}
#if 0
	  Vindtype : Memtype;		(* ucode memory type		     *)
	  Vindaddr : Addrrange);	(* ucode offset 		     *)
#endif
	Field : (
	  Fldaddr : Addrrange;		(* offset inside the record	     *)
	  Fieldsize : integer;
	  Inpacked : boolean);		(* true if packed		     *)
	Proc, Func : (
	  case Prockind : Proctype of
	    Special : (
	      Key : Stdprocfunc);
	    Inline : (
	      Uinst : Uopcode;		(* Ucode instr generated	     *)
	      Resdtype : Strp;		(* type of result		     *)
	      Dtypes : Dtypeset);	(* data types of args		     *)
	    Regular : (
	      Pflev : Levrange; 	(* lexical scope		     *)
	      Pfmemblock : integer;	(* local ucode block number	     *)
	      Parnumber : integer;	(* number of parameters 	     *)
	      lineno : integer;		(* line number of declaration *)
	      (* address of the function result, if any:		     *)
	      Resmemtype : Memtype;	(* ucode memory type		     *)
	      Resaddr : Addrrange;	(* ucode offset 		     *)
	      Fassigned : boolean;	(* set to true when function	     *)
					(* assigned value		     *)
	      Nonstandard : boolean;	(* used for warnings		     *)
	      case Pfkind : Idkind of	(* formal means parameter	     *)
		Actual : (
		  Forwdecl : boolean;	(* true if forward declared, reset to
					   false when declaration appears    *)
#if 0
		  Externdecl : boolean; (* true if imported		     *)
#endif
		  Externproc: boolean;  (* true if link-time external        *)
#if 0
		  Savedmsize : Memsize; (* for saving mem counts	     *)
#endif
		  SavedMmtMemcnt,
		  SavedPmtMemcnt: Addrrange; (* for saving memory counts	     *)
		  Filelist : Idp;	(* list of files		     *)
		  Testfwdptr : Idp;	(* linked list of procedures	     *)
					(* declared fwd 		     *)
		  Internsymndx: integer);(* the index in   *)
					(* internal symbol table *)
		Formal : (
		  Pfaddr : Addrrange;	(* ucode offset of descriptor	     *)
		  Pfmty : Memtype;	(* ucode memory type of descr	     *)
		  Pfblock : Blockrange; (* block no. of descr		     *)
		  Fparam : Idp)
	    )
	);				(* chain of parameters		     *)

	Labels : (
	  Scope : Levrange;		(* lexical level where it was	     *)
					(* declared			     *)
	  Defined : boolean;		(* true when appears		     *)
	  Externallab: boolean;		(* if true, used in GOOB *)
	  Uclabel : integer);		(* ucode label assigned to it	     *)
	Progname : (
	  Proglev : Levrange;		(* always one			     *)
	  Progmemblock : integer;	(* always one			     *)
	  Progparnumber : integer;	(* no. of prog parameters	     *)
	  Entname : Identname;		(* ucode name			     *)
	  Progfilelist : Idp;		(* list of global files 	     *)
	  Progparamptr : Parp; 	(* to the chain of prog parameters   *)
	  Progisym: integer; (* index in internal symbol table *)
	  Proglineno : integer);	(* line number of program statement *)
    end {record};

  (***************************************************************************)
  (* other types lexical tokens 					     *)
  (***************************************************************************)
  Symbol = (Identsy, Intconstsy, Realconstsy, Stringconstsy, Notsy, Mulsy,
	  Rdivsy, Andsy, Idivsy, Modsy, Plussy, Minussy, Orsy, Ltsy, Lesy,
	  Gesy, Gtsy, Nesy, Eqsy, Insy, Lparentsy, Rparentsy, Lbracksy,
	  Rbracksy, Commasy, Semicolonsy, Periodsy, Arrowsy, Colonsy,
	  Rangesy, Becomessy, Labelsy, Constsy, Typesy, Varsy, Functionsy,
	  Proceduresy, Packedsy, Setsy, Arraysy, Recordsy, Filesy, Forwardsy,
	  Beginsy, Ifsy, Casesy, Repeatsy, Whilesy, Forsy, Withsy, Gotosy,
	  Endsy, Elsesy, Untilsy, Ofsy, Dosy, Tosy, Downtosy,
	  Programsy, Thensy, Nilsy,
	  Othersy, Eofsy,
	  Externsy, Modulesy, Otherwisesy, Includesy, Commentsy, Returnsy);
  Setofsys = set of Symbol;

  (***************************************************************************)
  (* Display								     *)
  (***************************************************************************)
  Disprange = 0..Displimit;		(* for subscripts and indexes to the *)
					(* display			     *)

  Where = (Blck,			(* this level of display represents  *)
					(* a proc/func			     *)
      Crec);				(* this level of display represents  *)
					(* a record			     *)


  (***************************************************************************)
  (* runtime procedures 						     *)
  (***************************************************************************)
  Supports = (
	  Allocate, Free,
	  Ifile,
	  Peekchar, Nextchar,
	  Readline, Readinteger, Readcardinal, Readintrange,
	  Readboolean, Readchar, Readcharrange,
	  Readreal, Readdouble, Readextended,
	  Readstring, Readenum, Readset,
	  Writeline, Writeinteger, Writecardinal,
	  Writeboolean, Writechar,
	  Writereal, Writedouble, Writeextended,
	  Writestring, Writeenum, Writeset,
	  Caseerror, Assertionfailure, Nloc_goto);

  (***************************************************************************)
  (* expressions							     *)
  (***************************************************************************)

  Indirtype = (Notind, Hind, Aind);     (* Hind for pointers to heap,        *)
					(* Aind for reference parameters     *)
  Attrkind = (Cnst, Varbl, Expr);

  Attr = record 			(* describes an expression	     *)
      Atypep : Strp;			(* pointer to the type descriptor    *)
      Adtype : Datatype;		(* data type. to save on indirection *)
      Asize : integer;
      Apacked : boolean;		(* expr is element of packed	     *)
					(* structure			     *)
      case Kind : Attrkind of		(* cnst: compile-time known value    *)
					(* varbl: variables, fields and      *)
					(* functions expr: the value is on   *)
					(* top of the stack		     *)
	Cnst : (
	  Cval : Valu);
	Varbl : (
	  Indexed : boolean;		(* true if part of the address is on *)
					(* top of the stack		     *)
	  (* address:							     *)
	  Amty : Memtype;		(* ucode memory type		     *)
	  Ablock : Blockrange;		(* ucode procedure number	     *)
	  Dplmt : Addrrange;		(* ucode offset 		     *)
	  Baseaddress : Addrrange;	(* base address of object	     *)
	  (* indirection: (var parameters, pointed objects)		     *)
	  Indirect : Indirtype;
	  (* address of the address:					     *)
	  Indexmt : Memtype;		(* ucode memory type		     *)
	  Indexr : Addrrange;		(* ucode offset 		     *)
	  Subkind : Strp;		(* ptr to original strp, if was      *)
					(* subrange			     *)
	  Aclass : Idclass);		(* to distinguish var, field,	     *)
					(* function			     *)

	Expr : ();
    end {record};

  (* nodes to represent expression trees; correspond to U-Code instructions;
     for calls, it is a left-weighted binary tree with CUP at the root *)
  pttreerec = ^treerec;
  treerec = record
      l, r : pttreerec;
      tmp: integer;			(* index into Treetemp table if this
					   expr is pre-evaluated and stored *)
      isbool: boolean;
      U : Bcrec;			(* holds one instruction             *)
    end {record};

  (* nodes to represent the stack that simulate the U-Code expression stack,
     for building trees *)
  ptstakrec = ^stakrec;
  stakrec = record
    tree: pttreerec;			(* point to the tree for this item *)
    prev,				{points to unused but allocated nodes} 
    next: ptstakrec;			{points to next node down the stack}
    end;

#if 0
  (* nodes to represent file stack for initializing basic types for each file *)
  pttypemap = ^typemapnode;
  typemapnode =
    record
      cppname: Filename;
      fileno: integer; (* dense number from calling st_filebegin *)
      auxnums : array[btNil..btMax] of integer;
      next, prev : pttypemap; (* linked 2 ways so that do not have to
			deallocate and re-allocate in stack operations; prev
			points to unused upper part of allocated stack *)
    end {record};
#endif

var					(* lexer			     *)
  Listname, Sourcename, Symname, 
#if 0
  Incfilename,
#endif
  Uname: Filename;
  cppfilename: Filename; (* Mips *)
  List, 
#if 0
  Incfile,
#endif
  Symtbl: text;

  (***************************************************************************)
  (* Values returned by source program scanner insymbol:		     *)
  (***************************************************************************)

  Sy : Symbol;				(* last symbol scanned		     *)
  Val : Valu;				(* value of last constant	     *)
  Lgth : integer;			(* length of last string constant    *)
  Id : Identname;			(* last identifier		     *)
  Symmarker : integer;			(* beginning of current token	     *)
  Errorpos : integer;			(* position of last error in source  *)
					(* line 			     *)

  Trickychars : Setofsys;
  Emptytargetset : Valu;		(* for initializing a set constant   *)
  Readingstring : boolean;		(* if true, don't uppercase          *)
#if 0
  InIncludefile : boolean;		(* if true, reading from Included    *)
					(* file 			     *)
#endif
  Efile : boolean;			(* in E (editor) file?		     *)
  Chcntmax : 0..Sbufmax;		(* max number of chars per line      *)
  Listrewritten : boolean;		(* list file has been started	     *)
  Headerneeded : boolean;		(* header for current page of	     *)
					(* listing has not yet been printed  *)

  Chcnt : integer;			(* number of chars in this line      *)
  Chptr : integer;			(* position of current character in  *)
					(* buffer			     *)
  Nextbuffer,				(* for temporary spilling	     *)
  Buffer : Srcline;			(* Contents of current line	     *)
  Nextchcnt : integer;			(* size of the next line	     *)
  fileNumber,				(* for generating LOC and STP instr. *)
  mainfileNumber,			{ the number for the main file }
  Linecnt,				(* current line 		     *)
  Pagecnt,				(* current page 		     *)
  Symcnt,				(* no. of tokens already scanned in  *)
					(* this line			     *)
  Tchcnt,				(* character counter for main file   *)
#if 0
  Symfcnt,				(* character counter for symbol file *)
#endif
  Tlinecnt : integer;			(* no. of lines in the file	     *)

  (***************************************************************************)
  (* all of the above need to be saved when inserting an INCLUDE file	     *)
  (***************************************************************************)
  OldChcnt : integer;			(* number of chars in this line      *)
  OldChptr : integer;			(* position of current character in  *)
					(* buffer			     *)
  OldNextbuffer, OldBuffer : Srcline;	(* contents of current line	     *)
  OldNextchcnt : integer;		(* size of lookahead		     *)
  OldLinecnt,				(* current line 		     *)
  OldPagecnt,				(* current page 		     *)
  OldSymcnt : integer;			(* no. of tokens already scanned in  *)
					(* this line			     *)

  Rw : array[1..Rswmax] of Identname;	(* reserved word names		     *)
  Frw : array[1..Identlength] of 1..Rswmaxp1; (* length dividers for rw      *)
  Rsy : array[1..Rswmax] of Symbol;	(* symbol associated to each	     *)
					(* reserved word		     *)
  Ssy : array[char] of Symbol;		(* symbols associated with single    *)
					(* character tokens		     *)
  Lookahead : array[char] of boolean;	(* characters requiring lookahead    *)

  (***************************************************************************)
  (* error messages:							     *)
  (***************************************************************************)

  Currname : Identname; 		(* idname of the current	     *)
					(* procedure/function		     *)
  Needsaneoln : boolean;		(* something printed to the monitor  *)
					(* since last writeln?		     *)
  Errinx : 0..Maxerr;			(* number of errors in current	     *)
					(* source line			     *)
  Errorcount : integer; 		(* total number of errors detected   *)
					(* in program			     *)

  Errlist : array[1..Maxerr] of record
      Errno : 1..600;			(* error number 		     *)
      Errpos : 0..Sbufsize;		(* position in source line	     *)
      Warning : boolean;		(* if warning			     *)
      Varname : Identname;		(* id associated with error,if any   *)
    end {record};

  (***************************************************************************)
  (* error messages, by length						     *)
  (***************************************************************************)
  Errmess15 : array[1..31] of packed array[1..15] of char;
  Errmess20 : array[1..18] of packed array[1..20] of char;
  Errmess25 : array[1..19] of packed array[1..25] of char;
  Errmess30 : array[1..30] of packed array[1..30] of char;
  Errmess35 : array[1..23] of packed array[1..35] of char;
  Errmess40 : array[1..09] of packed array[1..40] of char;
  Errmess45 : array[1..20] of packed array[1..45] of char;
  Errmess50 : array[1..10] of packed array[1..50] of char;
  Errmess55 : array[1..15] of packed array[1..55] of char;


  (***************************************************************************)
  (* user-settable switches:						     *)
  (***************************************************************************)

  Showsource,				(* put source lines in U-code file   *)
  Idwarning,				(* warn if variables, consts, etc.   *)
					(* not used			     *)
#if 0
  Commentwarning,			(* warn if nested comments	     *)
#endif
  Logfile,				(* error messages go to the list     *)
					(* file?			     *)
  Lptfile,				(* full listing in list file?	     *)
  Printucode,				(* generation of Ucode file	     *)
  Runtimecheck, 			(* if true, perform runtime bounds   *)
					(* checks			     *)
  Standrdonly, 				(* accept only standard pascal	     *)
  Doubleonly,  				(* make floating pt at least double  *)
#if 0
  Emitsyms,				(* emit symbol table		     *)
#endif
  Optimize,				(* emit code suitable for optimizer  *)
  Noruntimes,				(* don't emit runtime request        *)
  debugging_symbols,
  stdump : boolean;			(* symbol table dump at end	     *)
  Maxidlength : integer;		(* user identifiers unique to this   *)
					(* many chars			     *)
  glevel: integer;			{ the -g option in the command line  }

  Sw : integer; 			(* loop temporary		    *)

  (***************************************************************************)
  (* other vars parser: 						     *)
  (***************************************************************************)
  Resetpossible,			(* to ignore switches which must not *)
					(* be reset			     *)
  Searcherror,				(* used as parameter to Searchid --  *)
					(* suppresses error message	     *)
  Parseleft,				(* true while parsing left hand side *)
					(* of assignment		     *)
  Parseright,				(* true most of the rest of the time *)
  Firstsymbol : boolean;		(* true until the first symbol in    *)
					(* program processed		     *)
  Lastsign :				(* set by Constant for scanning neg  *)
					(* integers			     *)
    (None, Pos, Neg);

  (***************************************************************************)
  (* legal symbols to begin a certain construct: see Wirth's book            *)
  (***************************************************************************)
  Constbegsys, Simptypebegsys, Typebegsys, Blockbegsys, Selectsys, Facbegsys,
      Statbegsys, Typedels, Mulopsys, Addopsys, Relopsys : Setofsys;
#if 0
  Ismodule : boolean;			(* true if module rather than	     *)
					(* program			     *)

  (***************************************************************************)
  (* Memory allocation: 						     *)
  (***************************************************************************)
  Memcnt, GlobalMemcnt: Memsize;
#endif
  PmtMemcnt, MmtMemcnt, SmtMemcnt : Addrrange;
  Temps :				(* temporaries table		     *)
    array[1..Maxtemps] of record
      Free : boolean;
      Mty : Memtype;
      Offset : integer;
      Tsize : integer;
      Stdtype : Datatype;
      Stamp : integer;
      Vreg : boolean;		(* Mips: tells if vreg attribute applies *)
    end {record};
  Static_link_loc:	Addrrange; {address of location to store static link}
  Tempcount : 0..Maxtemps;
  Treetemps:				(* table of temporaries used in
					   prepass over expression trees *)
    array[1..Maxtemps] of record
      free: boolean;
      offset,
      align,
      size: integer;
      dtype: Datatype;
      end;
  Treetempcount : 0..Maxtemps;

  Lastuclabel : integer;		(* last ucode label number created   *)
  Stampctr : integer;			(* used for allocation of	     *)
					(* temporaries			     *)

  (***************************************************************************)
  (* pointers:								     *)
  (***************************************************************************)

  Progidp : Idp;			(* ptr to a descriptor of the	     *)
					(* program			     *)

  Intptr, Cardinalptr, Charptr,		(* for predefined types 	     *)
  Realptr, Doubleptr, Extendedptr,
  Addressptr, Heapptr, Boolptr, Nilptr, Textptr, Anyfileptr, Anytextptr,
      Anystringptr, Anyptr : Strp;

  Utypptr, Ucstptr, Uvarptr, Ufldptr, Uprocptr, Ufuncptr, (* pointers to     *)
					(* entries for undeclared ids	     *)

  Forwardpointertype : Idp;		(* head of chain of forw decl type   *)
					(* ids				     *)


  (***************************************************************************)
  (* symbol table							     *)
  (***************************************************************************)

  Level : Levrange;			(* current lexical level	     *)
  Disx, 				(* index in Display of last 	     *)
					(* id searched by searchid	     *)
  Top : Disprange;			(* current top of display	     *)
  Memblock : Blockrange;		(* proc block currently local      *)
#if 0
  Memblkctr : Blockrange;		(* number of last memory block	     *)
  Lastmarker : integer; 		(* used in printing out symbol table *)
  Localmarker : integer;		(* ditto			     *)
#endif

  Extnamcounter : integer;		(* used in generating unique names   *)

  Display : array[Disprange] of packed record
      Fname : Idp;			(* to the binary tree of Ids for     *)
					(* this level			     *)
      Mblock : integer; 		(* ucode memory block number for     *)
					(* this scope			     *)
      case Occur : Where of		(* describes a record for	     *)
					(* declarations and for with	     *)
					(* statements			     *)
	Blck : ();			(* proc or func 		     *)
	Crec :				(* record			     *)
	(
	  Cblock : Blockrange;		(* procedure where record is	     *)
					(* declared			     *)
	  Cindexed : boolean;		(* true if on top of the stack	     *)
	  Cmty : Memtype;		(* ucode mem type		     *)
	  Cdspl : Addrrange;		(* ucode offset 		     *)
	  (* indirection: var params and pointed records		     *)
	  Cindirect : Indirtype;
	  (* address of the indirect pointer:				     *)
	  Cindexmt : Memtype;		(* ucode memory type		     *)
	  Cindexr : Addrrange;		(* ucode offset 		     *)
	  CMmtMemcnt: Addrrange)        (* for use in With statement *)
#if 0
	  Cmemcnt : Memsize)		(* current lc (local counter)	     *)
#endif
    end {record};



  (***************************************************************************)
  (* runtimes:								     *)
  (***************************************************************************)

  Runtimesupport : record
#if 0
      Idname : packed array[Supports] of Identname; (* name of proc	     *)
#endif
      Symndx : array[Supports] of integer;
      Pop : packed array[Supports] of 0..15; (* number of params	     *)
      Dty : packed array[Supports] of Datatype; (* data type of result	     *)
    end {record};

  Writesupport :			(* table of procedures for read and  *)
					(* write			     *)
    array[Datatype] of Supports;
  Readsupport : array[Datatype, Scalar..Subrange] of Supports;
  Widthdefault :			(* default field widths 	     *)
    array[Datatype] of integer;

  Fdbsize : integer;
  Stdfileinitidp,			(* ptr to standard file 	     *)
					(* initialization routine	     *)
  Resetptr, Rewriteptr, Reviseptr,	(* ptrs to std procedures	     *)
  Bufvalptr, Getptr, Putptr, Closeptr, Inputptr, Outputptr : Idp; (* ptr to Input and  *)
					(* Output ids			     *)
  Sysoutptr : Idp;			(* standard file for system output   *)
  Argcptr : Idp;

  Opninput, Opnoutput : 		(* true if INPUT or OUTPUT appear in *)
					(* program header		     *)
    boolean;

  (***************************************************************************)
  (* expression compilation:						     *)
  (***************************************************************************)

  Gattr : Attr; 			(* describes the expression	     *)
					(* currently being compiled	     *)


  (***************************************************************************)
  (* Ucode:								     *)
  (***************************************************************************)

  U : Bcrec;				(* holds current instruction	     *)

  stakbot,				(* the bottom of the stack *)
  stak: ptstakrec;			(* the stack top *)

  (* for producing st file *)
  st_str: st_string;
#if 0
  maptop,			(* top of typemap stack 	     *)
  mapbottom: pttypemap;		(* bottom of stack *)
#endif
  veryfirstfile: boolean;       (* flag to tell whether to generate bgn ucode
			           when seeing a cpp line *)


var
    loop_break_label, loop_continue_label: integer;
    ContinueSeen: boolean;	(* true, if continue statement in loop    *)
    current_block: idp;
    do_expr: boolean;
    lsb_first: boolean;
    verbose: boolean;
    nowarn: boolean;
    GHeap: pointer;		(* for alloc_mark, alloc_release	*)
    useframeptr: boolean;
