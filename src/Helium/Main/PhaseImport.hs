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
import Helium.Lvm.Common.Id
import qualified Helium.Lvm.Core.Expr as Core
import Text.PrettyPrint.Leijen (pretty)

phaseImport :: String -> Module -> (Id -> IO Core.CoreModule) -> [Option] -> 
                    IO ([Core.CoreDecl], [(Name, ImportEnvironment, ModuleDecls)])
phaseImport fullName module_ resolve options = do
    enterNewPhase "Importing" options

    let (_, baseName, _) = splitFilePath fullName

    -- Add HeliumLang and Prelude import
    let moduleWithExtraImports = addImplicitImports module_
                    
    -- Chase imports
    chasedImpsList <- chaseImports resolve moduleWithExtraImports

    let indirectionDecls = concatMap (\(_,x,_) -> x) chasedImpsList
        importEnvs = 
            map (\(name, decls, moddecls) -> (name, getImportEnvironment baseName decls, moddecls)) chasedImpsList
    
    return (indirectionDecls, importEnvs)
