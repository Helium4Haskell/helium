{-| Module      :  GatherImports
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.ModuleSystem.GatherImports(chaseImports, ModuleDecls, ImportList, addImplicitImports) where

--import Helium.Main.CompileUtils
import qualified Helium.Lvm.Core.Expr as Core
import qualified Helium.Lvm.Core.Utils as Core
import Helium.Lvm.Common.Id(stringFromId, idFromString, dummyId, Id)
import Helium.Lvm.Common.IdSet(IdSet, elemSet)
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range(noRange)
import Helium.Utils.Utils (internalError)
import Helium.Lvm.Path(searchPath)
import Helium.Lvm.Import(lvmImportDecls)
import qualified Helium.ModuleSystem.ExtractImportDecls as EID
import Data.List(isPrefixOf, intercalate)

type ImportList = ( Maybe Bool    -- Nothing if there is no import specification. Then True if hiding, false if not.
                  , Bool          -- True if qualified
                  , Name          -- How the imports should be qualified (normally the module name)
                  , IdSet         -- Values
                  , IdSet         -- Constructors, records fields or class methods
                  , IdSet         -- Complete types or classes
                  , IdSet         -- Only the type constructor or class name
                  , Name          -- The imported module name
                  )

type ModuleDecls = ( [Name]         -- normal values
                    , [Name]         -- type constructors
                    , [(Name, Name)] -- (value constructor, parent)
                    )

chaseImports :: (Id -> IO Core.CoreModule) -> Module -> IO [(Name, [Core.CoreDecl], ModuleDecls)]
chaseImports resolve fromModule = 
    let coreImports   = EID.coreImportDecls_Syn_Module $ EID.wrap_Module (EID.sem_Module fromModule) EID.Inh_Module -- Expand imports
        -- findModule    = searchPath lvmPath ".iridium" . stringFromId
        doImport :: ImportList -> IO (Name, [Core.CoreDecl], ModuleDecls)
        doImport (importspec, qualified, asName, values, confieldormethods, typeorclassesCompl, typeorclasses, modl)
            = do decls <- lvmImportDecls resolve [idFromName modl]
                 let rightd = getRightImports importspec qualified asName (values, confieldormethods, typeorclassesCompl, typeorclasses) decls
                     moduledecls = getAllModuleDecl decls
                 return (modl, rightd, moduledecls)
    in mapM doImport coreImports
        -- zipWith ($) filterImports (lvmImportDecls' findModule coreImportDecls)

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
                _ -> if "Prelude" `elem` map (getNameName . nameFromImportDeclaration) explicitImportDecls
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
            (Name_Identifier noRange [] [] moduleName) -- !!!Name
            MaybeName_Nothing
            MaybeImportSpecification_Nothing
addImplicitImports (Module_Module _ _ _ (Body_Hole _ _)) = internalError "PhaseImport" "addImplicitImports" "Not supported Body_Hole"

getRightImports :: Maybe Bool -> Bool -> Name -> (IdSet,IdSet,IdSet,IdSet) -> [Core.CoreDecl] -> [Core.CoreDecl]
getRightImports importspec qualified asName (values, confieldormethods, typeorclassesCompl, typeorclasses)
    = {-case importspec of
        Nothing -> id
        Just hiding ->  filter (isImported hiding)
                -}
    case importspec of
        Nothing     -> {-foldr (localAddQualified qualified asName) []-} id
        Just hiding -> {-foldr (localAddQualified qualified asName) [] .-} filter (isImported hiding)

    where
    intErr = internalError "PhaseImport" "getRightImports"

    conParentName Core.DeclCon{Core.declCustoms=(_:Core.CustomLink x _:_)} = x
    conParentName _ = dummyId
    
    -- Very weird. Had to add stictness everywhere where the oldname is used ($! and seq)
    -- I really have no clue why, but if you remove it, helium will loop and crash.
    localAddQualified :: Bool -> Name -> Core.CoreDecl -> [Core.CoreDecl] -> [Core.CoreDecl]
    localAddQualified qual as decl decls = 
        let oldname    = case Core.declAccess decl of 
                Core.Export n -> stringFromId n
                Core.Private  -> intErr "Expected an exported declaration"
            -- stringFromId $ (Core.declAccess decl)
            newnameid  = idFromString $! (toQualified as oldname)
            newdecl    = decl {Core.declAccess = Core.Export newnameid }
            isReserved = any (`isPrefixOf` oldname) ["Dict$", "$dict", "$Dict", "default$"]
        in decl : decls -- if isReserved then decl : decls else if qual then newdecl : decls else decl : newdecl : decls

    toQualified :: Name -> String -> String
    toQualified (Name_Identifier _ qs _ n) declname = seq declname $ intercalate "." $ qs ++ [n, declname]
    toQualified _ _ = intErr "Can only qualify module names"

    isImported :: Bool -> Core.CoreDecl -> Bool  
    isImported hiding decl = 
        let name  = Core.declName decl
            -- if it is hiding, we do not want to import if it is specified in the list
            willImport elemIdSet = if hiding then not elemIdSet else elemIdSet
        in                         
        case decl of 
            -- functions, record vield names or class functions
            Core.DeclAbstract { } -> "show" `isPrefixOf` stringFromId name ||
                willImport (elemSet name values || elemSet name confieldormethods)
            -- functions from non-core/non-lvm libraries and lvm-instructions
            Core.DeclExtern { }   -> willImport $
                elemSet name values
            -- constructors
            Core.DeclCon { } -> willImport $
                elemSet name confieldormethods || elemSet (conParentName decl) typeorclassesCompl
            -- type constructor import
            Core.DeclCustom { Core.declKind    = Core.DeclKindCustom ident }
            -- Type decl can never be hiden
                        | stringFromId ident == "typedecl"  -> True
                        | stringFromId ident == "data" || stringFromId ident == "typedecl" 
                            -> willImport $
                                elemSet name typeorclasses || elemSet name typeorclassesCompl
            -- infix decls
            Core.DeclCustom { Core.declKind    = Core.DeclKindCustom ident } 
                        | stringFromId ident == "infix" -> willImport $ elemSet name values
            -- typing strategies
            Core.DeclCustom { Core.declKind    = Core.DeclKindCustom ident }
                        | stringFromId ident == "strategy" -> True
            Core.DeclCustom  { } ->
                intErr  ("don't know how to handle DeclCustom: "       ++ stringFromId name)
            Core.DeclValue   { } ->
                intErr  ("don't know how to handle DeclValue: "        ++ stringFromId name) 


getAllModuleDecl :: [Core.CoreDecl] -> ModuleDecls
getAllModuleDecl = foldr addToResult ([], [], [])
    where
        intErr = internalError "PhaseImport" "getAllModuleDecl"

        getParent :: Core.CoreDecl -> Name
        getParent Core.DeclCon{Core.declCustoms=(_:Core.CustomLink x _:_)} = nameFromId x
        getParent decl = intErr ("Can't get parent from constructor " ++ stringFromId (Core.declName decl))

        addToResult :: Core.CoreDecl -> ModuleDecls -> ModuleDecls
        addToResult decl imports@(values, tycons, valcons) = 
            let id' = Core.declName decl
                name = nameFromId id'
            in
            case decl of
                -- functions, record vield names or class functions
                Core.DeclAbstract { } -> if "show" `isPrefixOf` stringFromId id' then imports
                                            else (name:values, tycons, valcons)
                -- functions from non-core/non-lvm libraries and lvm-instructions
                Core.DeclExtern { }   -> (name:values, tycons, valcons)
                -- constructors
                d@Core.DeclCon { } -> let pair = (name, getParent d) in (values, tycons, pair:valcons)
                -- type constructor import
                Core.DeclCustom { Core.declKind    = Core.DeclKindCustom ident } 
                            | stringFromId ident == "data" || stringFromId ident == "typedecl" 
                                -> (values, name:tycons, valcons)
                --We don't care about others
                _ -> imports
