# Generated automatically from Makefile.in by configure.

LVMPATH=/cygdrive/c/docs/helium/heliumNT/lib
COREASM=/cygdrive/c/docs/helium/heliumNT/../lvm/src/lib/coreasm
HELIUM=/cygdrive/c/docs/helium/heliumNT/bin/helium.exe

.PHONY : all
.SUFFIXES : .core .lvm .o

CORESRC = LvmLang.core LvmIO.core LvmException.core \
          HeliumLang.core PreludePrim.core

HELIUMSRC = Prelude.hs List.hs Maybe.hs

LIBRARIES = $(patsubst %.core,%.lvm,$(CORESRC)) \
            $(patsubst %.hs,%.o,$(HELIUMSRC))

all : $(LIBRARIES)
	echo $(LIBRARIES)

%.lvm : %.core
	$(COREASM) $<

%.o : %.hs
	$(HELIUM) -b $<

