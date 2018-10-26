{-| Module      :  GatherImports
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.ModuleSystem.GatherImports(chaseImports, ModuleDecls, ImportList, addImplicitImports) where
    
    --import Helium.Main.CompileUtils
    import qualified Lvm.Core.Expr as Core
    import qualified Lvm.Core.Utils as Core
    import Lvm.Common.Id(Id, stringFromId, idFromString, dummyId)
    import Lvm.Common.IdSet(IdSet, elemSet)
    import Helium.Syntax.UHA_Syntax
    import Helium.Syntax.UHA_Utils
    import Helium.Syntax.UHA_Range(noRange)
    import Helium.Utils.Utils (internalError)
    import Lvm.Path(searchPath)
    import Lvm.Import(lvmImportDecls)
    --import Helium.ModuleSystem.CoreToImportEnv(getImportEnvironment)
    import qualified Helium.ModuleSystem.ExtractImportDecls as EID
    import Data.List(isPrefixOf)

    type ImportList = ( Core.CoreDecl -- The import declaration
                      , Maybe Bool    -- Nothing if there is no import specification. Then True if hiding, false if not.
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

    chaseImports :: [String] -> Module -> IO [(Name, [Core.CoreDecl], ModuleDecls)]
    chaseImports lvmPath fromModule = 
        let coreImports   = EID.coreImportDecls_Syn_Module $ EID.wrap_Module (EID.sem_Module fromModule) EID.Inh_Module -- Expand imports
            findModule    = searchPath lvmPath ".lvm" . stringFromId
            doImport :: ImportList -> IO (Name, [Core.CoreDecl], ModuleDecls)
            doImport (importDecl, importspec, values, confieldormethods, typeorclassesCompl, typeorclasses, mod)
              = do decls_ <- lvmImportDecls findModule [importDecl]
                   let decls = concat decls_
                       rightd = getRightImports importspec (values, confieldormethods, typeorclassesCompl, typeorclasses) decls
                       fixedorigs = map (fixOrigininDecl mod) rightd
                       moduledecls = getAllModuleDecl decls
                   return (mod, fixedorigs, moduledecls)
    
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
                (Name_Identifier noRange [] [] moduleName) -- !!!Name
                MaybeName_Nothing
                MaybeImportSpecification_Nothing
    addImplicitImports (Module_Module _ _ _ (Body_Hole _ _)) = error "not supported"
    
    fixOrigininDecl :: Name -> Core.CoreDecl -> Core.CoreDecl
    fixOrigininDecl originalmod decl = let cs = Core.declCustoms decl
                                           access = Core.declAccess decl
                                           makeOrigin = [Core.CustomDecl (Core.DeclKindCustom (idFromString "origin")) [Core.CustomName (idFromName originalmod)]]
                                       in if hasOrigin cs then decl
                                            else decl {Core.declCustoms = cs ++ makeOrigin}
    
    hasOrigin :: [Core.Custom] -> Bool
    hasOrigin [] = False
    hasOrigin ( Core.CustomDecl (Core.DeclKindCustom ident) [Core.CustomName _] : cs)
        | stringFromId ident == "origin" = True
        | otherwise                      = hasOrigin cs
    hasOrigin (_ : cs) = hasOrigin cs

    
    getRightImports :: Maybe Bool -> (IdSet,IdSet,IdSet,IdSet) -> [Core.CoreDecl] -> [Core.CoreDecl]
    getRightImports importspec (values, confieldormethods, typeorclassesCompl, typeorclasses) decls
      = maybe decls (\hiding -> filter (isImported hiding) decls) importspec
      where
        intErr = internalError "PhaseImport" "getRightImports"
    
        conParentName Core.DeclCon{Core.declCustoms=(_:Core.CustomLink x _:_)} = x
        conParentName _ = dummyId
    
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
                Core.DeclCon { Core.declCustoms = cs } -> willImport $
                    elemSet name confieldormethods || elemSet (conParentName decl) typeorclassesCompl
                -- type constructor import
                Core.DeclCustom { Core.declKind    = Core.DeclKindCustom ident } 
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
                Core.DeclImport  { } ->
                    intErr  ("don't know how to handle DeclImport: "       ++ stringFromId name) 
 
    
    getAllModuleDecl :: [Core.CoreDecl] -> ModuleDecls
    getAllModuleDecl = foldr addToResult ([], [], [])
        where
            intErr = internalError "PhaseImport" "getAllModuleDecl"
    
            getParent :: Core.CoreDecl -> Name
            getParent Core.DeclCon{Core.declCustoms=(_:Core.CustomLink x _:_)} = nameFromId x
            getParent decl = intErr ("Can't get parent from constructor " ++ stringFromId (Core.declName decl))
    
            addToResult :: Core.CoreDecl -> ModuleDecls -> ModuleDecls
            addToResult decl imports@(values, tycons, valcons) = 
                let id  = Core.declName decl
                    name = nameFromId id
                in
                case decl of
                    -- functions, record vield names or class functions
                    Core.DeclAbstract { } -> if "show" `isPrefixOf` stringFromId id then imports
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