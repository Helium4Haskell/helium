{-| Module      :  PhaseImport
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseImport(phaseImport) where

import Helium.ModuleSystem.GatherImports
import Helium.Main.CompileUtils
import Helium.ModuleSystem.CoreToImportEnv(getImportEnvironment)
import Helium.Syntax.UHA_Syntax
import qualified Lvm.Core.Expr as Core

{-
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Utils as Core
import Lvm.Common.Id(Id, stringFromId, idFromString, dummyId)
import Lvm.Common.IdSet(IdSet, elemSet)

import Helium.Syntax.UHA_Utils
import Lvm.Path(searchPath)
import qualified Helium.ModuleSystem.ExtractImportDecls as EID-}

phaseImport :: String -> Module -> [String] -> [Option] -> 
                    IO ([Core.CoreDecl], [(Name, ImportEnvironment, ModuleDecls)])
phaseImport fullName module_ lvmPath options = do
    enterNewPhase "Importing" options

    let (_, baseName, _) = splitFilePath fullName

    -- Add HeliumLang and Prelude import
    let moduleWithExtraImports = addImplicitImports module_
                    
    -- Chase imports
    chasedImpsList <- chaseImports lvmPath moduleWithExtraImports

    let indirectionDecls   = concatMap (\(_,x,_) -> x) chasedImpsList
        importEnvs = 
            map (\(name,decls,moddecls) -> (name, getImportEnvironment baseName decls, moddecls)) chasedImpsList
    
    return (indirectionDecls, importEnvs)