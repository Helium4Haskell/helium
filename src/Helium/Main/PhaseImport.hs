{-| Module      :  PhaseImport
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}
{-# LANGUAGE BangPatterns #-}
module Helium.Main.PhaseImport(phaseImport) where

import Helium.Main.CompileUtils
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Utils as Core
import Lvm.Common.Id(Id, stringFromId)
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range(noRange)
import Lvm.Path(searchPath)
import Lvm.Import(lvmImportDecls)
import Helium.ModuleSystem.CoreToImportEnv(getImportEnvironment)
import qualified Helium.ModuleSystem.ExtractImportDecls as EID
import Data.List(isPrefixOf)

phaseImport :: String -> Module -> [String] -> [Option] -> 
                    IO ([Core.CoreDecl], [ImportEnvironment])
phaseImport fullName module_ lvmPath options = do
    enterNewPhase "Importing" options

    let (_, baseName, _) = splitFilePath fullName

    -- Add HeliumLang and Prelude import
    let moduleWithExtraImports = addImplicitImports module_
                    
    -- Chase imports
    chasedImpsList <- chaseImports lvmPath moduleWithExtraImports

    let indirectionDecls   = concat chasedImpsList

    let importEnvs = 
            map (getImportEnvironment baseName) chasedImpsList
    
    return (indirectionDecls, importEnvs)

chaseImports :: [String] -> Module -> IO [[Core.CoreDecl]]
chaseImports lvmPath fromModule = 
    let coreImports   = EID.coreImportDecls_Syn_Module $ EID.wrap_Module (EID.sem_Module fromModule) EID.Inh_Module -- Expand imports
        findModule    = searchPath lvmPath ".lvm" . stringFromId
        doImport :: (Core.CoreDecl,[Id]) -> IO [Core.CoreDecl]
        doImport (importDecl,hidings)
          = do decls <- lvmImportDecls findModule [importDecl]
               return [ d
                      | d <- concat decls
                      , let name = Core.declName d
                      , "show" `isPrefixOf` stringFromId name || name `notElem` hidings
                      ]

    in mapM doImport coreImports
        -- zipWith ($) filterImports (lvmImportDecls findModule coreImportDecls)

-- Add "import Prelude" if
--   the currently compiled module is not the Prelude and
--   the Prelude is not explicitly imported
-- Always add "import HeliumLang
addImplicitImports :: Module -> Module
addImplicitImports (Module_Module moduleRange maybeName exports
                   (Body_Body bodyRange explicitImportDecls decls)) =
    Module_Module
        moduleRange
        maybeName
        exports
        (Body_Body
            bodyRange
            ( case maybeName of
                MaybeName_Just n
                    | getNameName n == "Prelude" -> []
                _ -> if "Prelude" `elem` map stringFromImportDeclaration explicitImportDecls
                     then []
                     else [ implicitImportDecl "Prelude" ]
            ++ [ implicitImportDecl "HeliumLang" ]
            ++ explicitImportDecls
            ) decls
        )
  where
    -- Artificial import declaration for implicit Prelude import
    implicitImportDecl :: String -> ImportDeclaration
    implicitImportDecl moduleName =
        ImportDeclaration_Import
            noRange
            False
            (Name_Identifier noRange [] moduleName) -- !!!Name
            MaybeName_Nothing
            MaybeImportSpecification_Nothing
addImplicitImports (Module_Module _ _ _ (Body_Hole _ _)) = error "not supported"
