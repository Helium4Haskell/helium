#-----------------------------------------------------------------------
#  Compiling attribute grammar code for The Helium Compiler
#  This Makefile only needs to be invoked after modifying files with
#  extension .ag. Otherwise it suffices to use cabal install.
#-----------------------------------------------------------------------

# make		     - build Haskell sources out of AG code
# make cleanag - remove all .hs files that are derivatives of .ag files

default: all
all: ag

AG      = uuagc -P Helium/Syntax -P Helium/StaticAnalysis/StaticChecks -P Helium/StaticAnalysis/Inferencers -P Helium/CodeGeneration -P Helium/StaticAnalysis/Directives
AG_OPTS = -mscfrw --kennedywarren

# AG sources
AGSOURCES = \
     Helium/Syntax/UHA_Pretty.hs \
     Helium/Syntax/UHA_OneLine.hs \
     Helium/StaticAnalysis/StaticChecks/StaticChecks.hs \
     Helium/StaticAnalysis/Inferencers/TypeInferencing.hs \
     Helium/StaticAnalysis/Inferencers/KindInferencing.hs \
     Helium/CodeGeneration/CodeGeneration.hs \
     Helium/Syntax/UHA_Syntax.hs \
     Helium/ModuleSystem/ExtractImportDecls.hs \
     Helium/StaticAnalysis/Directives/TS_Syntax.hs \
     Helium/StaticAnalysis/Directives/TS_Apply.hs \
     Helium/StaticAnalysis/Directives/TS_Analyse.hs \
     Helium/StaticAnalysis/Directives/TS_CoreSyntax.hs \
     Helium/StaticAnalysis/Directives/TS_ToCore.hs \
     Helium/Parser/ResolveOperators.hs

libraries:
	@echo "****************************************************"
	@echo "  Libraries (with overloading)"
	@echo "****************************************************"
	cd ../lib; $(MAKE) 
	@echo "****************************************************"
	@echo "  Simple libraries (without overloading)"
	@echo "****************************************************"
	cd ../lib/simple; $(MAKE) 

# AG sources

ag : $(AGSOURCES)

cleanag : 
	$(RM) $(AGSOURCES)

ifdef AG
Helium/Parser/ResolveOperators.hs : \
		Helium/Parser/ResolveOperators.ag \
		Helium/Syntax/UHA_Syntax.ag
	# AG ResolveOperators
	$(AG) $(AG_OPTS) --self --module=Helium.Parser.ResolveOperators Helium/Parser/ResolveOperators.ag

Helium/Syntax/UHA_Pretty.hs : \
		Helium/Syntax/UHA_Pretty.ag Helium/Syntax/UHA_Syntax.ag
	# AG UHA_Pretty
	$(AG) $(AG_OPTS) --module=Syntax.UHA_Pretty Syntax/UHA_Pretty.ag

Helium/Syntax/UHA_OneLine.hs : \
		Helium/Syntax/UHA_OneLine.ag Helium/Syntax/UHA_Syntax.ag
	# AG UHA_OneLine
	$(AG) $(AG_OPTS) --self --module=Helium.Syntax.UHA_OneLine Helium/Syntax/UHA_OneLine.ag

Helium/StaticAnalysis/StaticChecks/StaticChecks.hs : \
		Helium/StaticAnalysis/StaticChecks/StaticChecks.ag \
		Helium/StaticAnalysis/StaticChecks/KindChecking.ag \
    Helium/StaticAnalysis/StaticChecks/TopLevelErrors.ag \
    Helium/StaticAnalysis/StaticChecks/MiscErrors.ag \
    Helium/StaticAnalysis/StaticChecks/Warnings.ag \
		Helium/StaticAnalysis/StaticChecks/ExportErrors.ag \
    Helium/StaticAnalysis/StaticChecks/Collect.ag \
    Helium/StaticAnalysis/StaticChecks/HeliumPartialSyntax.ag \
    Helium/StaticAnalysis/StaticChecks/Scope.ag \
    Helium/StaticAnalysis/StaticChecks/ScopeErrors.ag \
		Helium/Syntax/UHA_Syntax.ag 
                
	# AG StaticAnalysis
	$(AG) $(AG_OPTS) --self --module=Helium.StaticAnalysis.StaticChecks.StaticChecks Helium/StaticAnalysis/StaticChecks/StaticChecks.ag

Helium/StaticAnalysis/Inferencers/TypeInferencing.hs : \
		Helium/StaticAnalysis/Inferencers/TypeInferencing.ag \
    Helium/StaticAnalysis/Inferencers/TypeInferenceRules.ag \
    Helium/StaticAnalysis/Inferencers/TypeInferenceOverloading.ag \
    Helium/StaticAnalysis/Inferencers/TypeInferenceCollect.ag \
    Helium/StaticAnalysis/Inferencers/TypeInferenceInfo.ag \
    Helium/StaticAnalysis/Inferencers/PatternMatchWarnings.ag \
    Helium/StaticAnalysis/Inferencers/LocalInfo.ag \
    Helium/StaticAnalysis/Inferencers/GlobalInfo.ag \
    Helium/StaticAnalysis/StaticChecks/HeliumPartialSyntax.ag \
		Helium/Syntax/UHA_Syntax.ag \
    Helium/StaticAnalysis/StaticChecks/Scope.ag\
    Helium/StaticAnalysis/Directives/TS_PatternMatching.ag
                
	# AG TypeInferencing
	$(AG) $(AG_OPTS) --self --module=Helium.StaticAnalysis.Inferencers.TypeInferencing Helium/StaticAnalysis/Inferencers/TypeInferencing.ag

Helium/StaticAnalysis/Inferencers/KindInferencing.hs : \
		Helium/StaticAnalysis/Inferencers/KindInferencing.ag \
    Helium/Syntax/UHA_Syntax.ag \
                
	# AG TypeInferencing
	$(AG) $(AG_OPTS) --self --module=Helium.StaticAnalysis.Inferencers.KindInferencing Helium/StaticAnalysis/Inferencers/KindInferencing.ag

Helium/CodeGeneration/CodeGeneration.hs : \
		Helium/CodeGeneration/CodeGeneration.ag \
		Helium/Syntax/UHA_Syntax.ag \
		Helium/CodeGeneration/ToCoreModule.ag \
		Helium/CodeGeneration/ToCoreDecl.ag \
		Helium/CodeGeneration/ToCoreExpr.ag \
		Helium/CodeGeneration/ToCorePat.ag \
		Helium/CodeGeneration/ToCoreName.ag
	# AG CodeGeneration
	$(AG) $(AG_OPTS) --self --module=Helium.CodeGeneration.CodeGeneration Helium/CodeGeneration/CodeGeneration.ag

Helium/Syntax/UHA_Syntax.hs : Helium/Syntax/UHA_Syntax.ag
	# AG UHA_Syntax
	$(AG) -dmr --module=Helium.Syntax.UHA_Syntax Helium/Syntax/UHA_Syntax.ag

Helium/ModuleSystem/ExtractImportDecls.hs : \
		Helium/ModuleSystem/ExtractImportDecls.ag \
		Helium/CodeGeneration/ToCoreName.ag \
		Helium/Syntax/UHA_Syntax.ag
	# AG ExtractImportDecls
	$(AG) $(AG_OPTS) --self --module=Helium.ModuleSystem.ExtractImportDecls Helium/ModuleSystem/ExtractImportDecls.ag
        
Helium/StaticAnalysis/Directives/TS_Syntax.hs : \
	  Helium/StaticAnalysis/Directives/TS_Syntax.ag
	# AG TS_Syntax
	$(AG) -dmr --module=Helium.StaticAnalysis.Directives.TS_Syntax Helium/StaticAnalysis/Directives/TS_Syntax.ag

Helium/StaticAnalysis/Directives/TS_Analyse.hs : \
    Helium/StaticAnalysis/Directives/TS_Syntax.ag \
    Helium/StaticAnalysis/Directives/TS_Collect.ag \
    Helium/StaticAnalysis/Directives/TS_Analyse.ag \
    Helium/Syntax/UHA_Syntax.ag 
	# AG TS_Analyse
	$(AG) $(AG_OPTS) --self --module=Helium.StaticAnalysis.Directives.TS_Analyse Helium/StaticAnalysis/Directives/TS_Analyse.ag

Helium/StaticAnalysis/Directives/TS_Apply.hs : \
    Helium/StaticAnalysis/Directives/TS_Syntax.ag \
    Helium/StaticAnalysis/Directives/TS_Collect.ag \
    Helium/StaticAnalysis/Directives/TS_Apply.ag \
    Helium/StaticAnalysis/Directives/TS_CoreSyntax.ag \
    Helium/Syntax/UHA_Syntax.ag \
	# AG TS_Syntax
	$(AG) -mscfw --module=Helium.StaticAnalysis.Directives.TS_Apply Helium/StaticAnalysis/Directives/TS_Apply.ag

Helium/StaticAnalysis/Directives/TS_CoreSyntax.hs : \
	  Helium/StaticAnalysis/Directives/TS_CoreSyntax.ag \
	# AG TS_CoreSyntax
	$(AG) -md --module=Helium.StaticAnalysis.Directives.TS_CoreSyntax Helium/StaticAnalysis/Directives/TS_CoreSyntax.ag

Helium/StaticAnalysis/Directives/TS_ToCore.hs : \
    Helium/StaticAnalysis/Directives/TS_Syntax.ag \
    Helium/StaticAnalysis/Directives/TS_Collect.ag \
    Helium/StaticAnalysis/Directives/TS_ToCore.ag \
    Helium/Syntax/UHA_Syntax.ag \
    Helium/Syntax/UHA_OneLine.ag 
	# AG TS_Syntax
	$(AG) -mscrfw --self --module=Helium.StaticAnalysis.Directives.TS_ToCore Helium/StaticAnalysis/Directives/TS_ToCore.ag                 
endif

