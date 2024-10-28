.PHONY: coreasm

default: coreasm

#-----------------------------------------------------------------------
# Compilers and Tools
#-----------------------------------------------------------------------

HC      = ghc
HADDOCK = haddock
HLINT   = hlint

HC_OPTS = -Wall -odir $(OUTDIR) -hidir $(OUTDIR)

OUTDIR = out
DOCDIR = out

RM = rm -rf

coreasm:
	$(HC) --make $(HC_OPTS) -o coreasm Lvm/Core/Main

report:
	mkdir -p out
	$(HLINT) --report=$(DOCDIR)/report.html .

# Clean	up
clean:
	$(RM) out
	$(RM) *.hi *.o $(MAIN)$(EXE)
	$(RM) */*.hi */*.o
	$(RM) */*/*.hi */*/*.o