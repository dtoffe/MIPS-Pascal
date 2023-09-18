# --------------------------------------------------- 
# | Copyright (c) 1986 MIPS Computer Systems, Inc.  | 
# | All Rights Reserved.                            | 
# --------------------------------------------------- 
# $Header: Makefile,v 1030.7 88/03/02 13:45:22 bettina Exp $
include ../Make.Common
REV = 1.30
RELREV= $(REL)$(REV)

DCFLAGS = -O
DPFLAGS = -O

LIBBASE = libp$(OPTION)
LIB = $(LIBBASE)$(LSUFFIX)
.PRECIOUS: $(LIB)

TARGETS=$(LIB)
OBJECTS=$(COBJECTS) $(SOBJECTS)

SOBJECTS = $(LIB)(alloc$(OSUFFIX))
COBJECTS = $(LIB)(new$(OSUFFIX)) \
	$(LIB)(textinput$(OSUFFIX)) \
	$(LIB)(textoutput$(OSUFFIX)) \
	$(LIB)(get$(OSUFFIX)) \
	$(LIB)(put$(OSUFFIX)) \
	$(LIB)(reset$(OSUFFIX)) \
	$(LIB)(rewrite$(OSUFFIX)) \
	$(LIB)(getbuf$(OSUFFIX)) \
	$(LIB)(exit$(OSUFFIX)) \
	$(LIB)(caseerror$(OSUFFIX)) \
	$(LIB)(get_arg$(OSUFFIX)) \
	$(LIB)(clock$(OSUFFIX)) \
	$(LIB)(input$(OSUFFIX)) \
	$(LIB)(output$(OSUFFIX)) \
	$(LIB)(err$(OSUFFIX)) \
	$(LIB)(allocator$(OSUFFIX)) \
	$(LIB)(data$(OSUFFIX)) \
	$(LIB)(date$(OSUFFIX)) \
	$(LIB)(time$(OSUFFIX)) \
	$(LIB)(rand$(OSUFFIX)) \
	$(LIB)(pc_nloc_goto$(OSUFFIX)) \
	$(LIB)($(VERS)$(OSUFFIX))

all: $(LIB)

$(LIBBASE).a: $(OBJECTS)
	@echo "building normal $(LIB)"
	$(AR) ts $(LIB)

$(LIBBASE).b: $(COBJECTS)
	@echo "building normal $(LIB)"
	$(AR) ts $(LIB)

copy:
	$(LIBINSTALL) $(LIB) $(ILIBDIR)/$(LIB)$(RELREV)

link:
	cd $(ILIBDIR); $(RM) $(LIB)$(REL); $(LINK) $(LIB)$(RELREV) $(LIB)$(REL)

clobber:
	$(RM) $(LIB) $(VERS).c $(LIBBASE).b

check:
	@echo "Checking boot strap of libp"
	$(CMPLIB) $(LIB) $(CHECKDIR)/$(LIB)$(CHECKVER)

.p.a:
	$(PC) $(PFLAGS) -c -j $<
	$(AR) rv $(@:.a=.b) $*.u
	$(LD) $(LDFLAGS) -r $*.o
	mv a.out $*.o
	$(AR) rv $@ $*.o
	$(RM) $*.o $*.u

.c.a:
	$(CC) $(CFLAGS) -c -j $<
	$(AR) rv $(@:.a=.b) $*.u
	$(LD) $(LDFLAGS) -r $*.o
	mv a.out $*.o
	$(AR) rv $@ $*.o
	$(RM) $*.o $*.u

$(LIB)(data.o):
	$(CC) $(CFLAGS) -G 512 -c -j $<
	$(AR) rv $(@:.a=.b) $*.u
	$(LD) $(LDFLAGS) -r $*.o
	mv a.out $*.o
	$(AR) rv $@ $*.o
	$(RM) $*.o $*.u
