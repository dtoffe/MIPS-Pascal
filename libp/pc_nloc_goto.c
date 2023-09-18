/* --------------------------------------------------- */
/* | Copyright (c) 1987 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: pc_nloc_goto.c,v 1030.2 88/03/02 13:45:52 bettina Exp $*/
/* Implement known-to-be-nonlocal GOTO */

#include "sym.h"
#include "exception.h"
#include <signal.h>
#include <stdio.h>

#define RA 31

void
__pc_nloc_goto(pc, fp)
  unsigned pc; /* Destination */
  unsigned fp; /* Destination */
  {
  struct sigcontext sc_temp;
  struct runtime_pdr *this_proc;
  unsigned this_frame, from_pc;

  exc_setjmp(&sc_temp); /* Here we are */
  from_pc = sc_temp.sc_regs[RA] - 2 * sizeof(unsigned); /* Our return address */
  unwind(&sc_temp, 0); /* Zap our frame */
  unwind(&sc_temp, 0); /* Zap our caller's frame */

  /* Unwind stack frame by frame till we find the right one */
  for(;;)
    {
    /* Ran out of stack? */
    if (sc_temp.sc_pc == 0)
      break;
    this_proc = find_rpd(sc_temp.sc_pc);
    this_frame = sc_temp.sc_regs[this_proc->framereg] + this_proc->frameoffset;
    if (fp == this_frame)
      {
      sc_temp.sc_pc = sc_temp.sc_regs[RA] = pc;
      if (exc_resume(&sc_temp) == -1)
	break; /* Sigreturn must have failed */
      }
    unwind(&sc_temp, this_proc);
    }

  /* Never found the right frame */
  fprintf(stderr, "Illegal nonlocal goto from %#08x to %#08x\n",
    from_pc, pc);
  exit(80);
  }

