# --------------------------------------------------- 
# | Copyright (c) 1986 MIPS Computer Systems, Inc.  | 
# | All Rights Reserved.                            | 
# --------------------------------------------------- 
# $Header: Makefile,v 1030.7 88/02/18 14:55:03 bettina Exp $
include ../Make.Common
REV = 1.30
RELREV=$(REL)$(REV)

TARGETS = upas
all: $(TARGETS)

DPFLAGS = -g
LIBS = $(LIBMLD) $(LIBU) 

OBJECTS = upasmain$(OSUFFIX) \
	upasinit$(OSUFFIX) \
	upasutil$(OSUFFIX) \
	upasuco$(OSUFFIX) \
	upaslex$(OSUFFIX) \
	upascase$(OSUFFIX) \
	upasbutil$(OSUFFIX) \
	upasstmt$(OSUFFIX) \
	upasdecl$(OSUFFIX) \
	upascall$(OSUFFIX) \
	upasexpr$(OSUFFIX) \
	upastree$(OSUFFIX) \
	upassym$(OSUFFIX) \
	upasfold$(OSUFFIX) \
	$(VERS)$(OSUFFIX) \
	$(ALLOC)

upas:	$(OBJECTS)
	$(PC) $(LDFLAGS) $(PFLAGS) -o $@ $(OBJECTS) $(LIBS)

linkupas:
	$(PC) $(LDFLAGS) -o upas $(OBJECTS) $(LIBS)

copy:
	$(INSTALL) upas $(ILIBDIR)/upas$(RELREV)

link:
#	cd $(ILIBDIR); \
#		$(RM) upas$(REL); $(LINK) upas$(RELREV) upas$(REL)

clobber:
	$(RM) $(OBJECTS) $(TARGETS) $(VERS).c

check:
	@echo "Checking boot strap of upas"
	$(CMP) $(TARGETS) $(CHECKDIR)
