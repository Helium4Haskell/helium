--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

-- | This module performs import resolution for lazy virtual machine files.
--
--     * Requires a function that, given a module 'Id', load a 'Module'.
--     * Lets the caller determine the choice of monad. This is useful
--       for testing and integration.
--
module Helium.Lvm.Import
  ( lvmImport
  , lvmImportDecls
  , lvmImportRenameMap
  , lvmImportQualifyModule
  )
where


import           Data.List
import           Data.Maybe
import           Helium.Lvm.Common.Id
import           Helium.Lvm.Common.IdSet
import           Helium.Lvm.Common.IdMap
import           Helium.Lvm.Data
import           Helium.Lvm.Constants

import           Helium.Lvm.Core.Type
import           Helium.Lvm.Core.Expr



-- | Adds abstract declarations for all exported definitions of the imported
-- modules
lvmImport :: Monad m => (Id -> m (CoreModule)) -> CoreModule -> m (CoreModule)
lvmImport findModule m = do
  exported <- lvmImportDecls findModule $ moduleImports m
  let (valuesMap, typesMap) = lvmImportRenameMap exported
  let imported = map (\d -> d{ declAccess = Private}) exported
  let m' = lvmImportQualifyModule (valuesMap, typesMap) m True
  return m'{ moduleDecls = imported ++ moduleDecls m' }

  {-
  mods <- lvmImportModules findModule m
  let mods0 = lvmExpandModule mods (moduleName m)
      mods1 = lvmResolveImports mods0
      mod1  = findMap (moduleName m) mods1
  return mod1 { moduleDecls = filter (not . isDeclImport) (moduleDecls mod1) } -}

-- Fetches all exported declarations in each of the modules
lvmImportDecls :: Monad m => (Id -> m (Module v)) -> [Id] -> m [Decl v]
lvmImportDecls findModule names = do
  modules <- mapM findModule $ nub names
  return $ modules >>= (filter 
    (\decl -> accessPublic (declAccess decl))
      . moduleDecls)

-- Constructs a map, converting unqualified names to fully qualified names,
-- for both the value namespace (first field) and the types name space (second field)
lvmImportRenameMap :: [Decl v] -> (IdMap Id, IdMap Id)
lvmImportRenameMap = foldl' (flip insert) (emptyMap, emptyMap)
  where
    insert decl (valuesMap, typesMap) = case declAccess decl of
      Export alias
        -- Fixity declarations are ignored, because the names need to be renamed 
        -- using the actual declaration
        | isDeclInfix decl -> (valuesMap, typesMap)
        | declaresValue decl ->
          let valuesMap' = insertAssertMap alias name valuesMap
          in valuesMap' `seq` (valuesMap', typesMap)
        | otherwise ->
          let typesMap' = insertAssertMap alias name typesMap
          in typesMap' `seq` (valuesMap, typesMap')
      where
        name = declName decl

insertAssertMap :: (Show a, Eq a) => Id -> a -> IdMap a -> IdMap a
insertAssertMap x a = insertMapWith x a f
  where
    f b
      | a == b = b
      | otherwise = error $ "insertAssertMap: current value " ++ show b ++ " for " ++ show x ++ " doesn't match new value " ++ show a

-- Makes variable names quantified.
lvmImportQualifyModule :: (IdMap Id, IdMap Id) -> CoreModule -> Bool -> CoreModule
lvmImportQualifyModule (valuesMap, typesMap) (Module modName modMajor modMinor modImports modDecls) shouldRenameOwn
  = Module modName modMajor modMinor modImports $ map travDecl modDecls
  where
    (valueDecls', typeDecls) = partition declaresValue modDecls
    (infixDecls, valueDecls) = partition isDeclInfix valueDecls'
    ownValues = setFromList $ map declName valueDecls
    ownTypes = setFromList $ map declName typeDecls

    -- The types in Helium.Utils.QualifiedTypes.Constants need to be excluded
    -- from qualification as they will map to the same id when using the type
    -- environment
    renameOwn :: Id -> Id
    renameOwn name = idFromString $ qualify $ stringFromId name
      where qualify s | not shouldRenameOwn || s `elem` constants = s
                      | otherwise = stringFromId modName ++ "." ++ s

    renameWith :: IdSet -> IdMap Id -> Id -> Id
    renameWith own importMap name
      | name `elemSet` own = renameOwn name
      | otherwise = fromMaybe name (lookupMap name importMap)

    renameValue', renameType :: Id -> Id
    renameValue' = renameWith ownValues valuesMap
    renameType   = renameWith ownTypes  typesMap

    renameValue :: IdSet -> Id -> Id
    renameValue locals name
      | name `elemSet` locals = name
      | otherwise = renameValue' name

    travDecl :: CoreDecl -> CoreDecl
    travDecl d = d'{ declName = rename d }
      where
        rename d | isDeclInfix d = declName d
                 | declaresValue d = renameValue' $ declName d
                 | otherwise = renameType $ declName d
        d' = travDecl' d

    travDecl' :: CoreDecl -> CoreDecl
    travDecl' d@DeclValue{} = d{ declType = travType $ declType d, valueValue = travExpr emptySet $ valueValue d }
    travDecl' d@DeclAbstract{} = d{ declType = travType $ declType d }
    travDecl' d@DeclCon{} = d{ declType = travType $ declType d }
    travDecl' d@DeclExtern{} = d{ declType = travType $ declType d }
    travDecl' d@DeclTypeSynonym{} = d{ declType = travType $ declType d }
    travDecl' d@DeclCustom{} | isDeclInfix d = d { declName = renameWith emptySet valuesMap (declName d) }
                             | otherwise     = d

    travType :: Type -> Type
    travType (TAp t1 t2) = travType t1 `TAp` travType t2
    travType (TForall quantor kind tp) = TForall quantor kind $ travType tp
    travType (TStrict tp) = TStrict $ travType tp
    travType (TVar idx) = TVar idx
    travType (TCon tcon) = TCon $ case tcon of
      TConDataType name            -> TConDataType $ renameType name
      TConTypeClassDictionary name -> TConTypeClassDictionary $ renameType name
      _                            -> tcon
    
    travExpr :: IdSet -> Expr -> Expr
    travExpr locals (Let (Rec bs) e) = Let (Rec [ Bind (travVariable var) $ trav expr | Bind var expr <- bs ]) (trav e)
      where
        trav = travExpr locals'
        boundLocals = [ variableName var | Bind var _ <- bs ]
        locals' = foldl' (flip insertSet) locals boundLocals
    travExpr locals (Let (NonRec (Bind v e1)) e2)
      = Let (NonRec (Bind (travVariable v) e1')) e2'
      where
        e1' = travExpr locals e1
        e2' = travExpr (insertSet (variableName v) locals) e2
    travExpr locals (Let (Strict (Bind v e1)) e2)
      = Let (Strict (Bind (travVariable v) e1')) e2'
      where
        e1' = travExpr locals e1
        e2' = travExpr (insertSet (variableName v) locals) e2
    travExpr locals (Match var alts) = Match (renameValue locals var) (map (travAlt locals) alts)
    travExpr locals (Ap e1 e2) = travExpr locals e1 `Ap` travExpr locals e2
    travExpr locals (ApType e t) = travExpr locals e `ApType` travType t
    travExpr locals (Lam strict var body) = Lam strict (travVariable var) $ travExpr locals' body
      where
        locals' = insertSet (variableName var) locals
    travExpr locals (Forall quantor kind expr) = Forall quantor kind $ travExpr locals expr
    travExpr locals (Con c) = Con $ travCon c
    travExpr locals (Var name) = Var $ renameValue locals name
    travExpr locals (Lit lit) = Lit lit

    travAlt :: IdSet -> Alt -> Alt
    travAlt locals (Alt pat expr) = Alt (travPat pat) (travExpr locals' expr)
      where
        locals' = case pat of
          PatCon _ _ names -> foldl' (flip insertSet) locals names
          _ -> locals
    
    travPat :: Pat -> Pat
    travPat (PatCon c tps fields) = PatCon (travCon c) (map travType tps) fields
    travPat p = p

    travCon :: Con -> Con
    travCon (ConId name) = ConId $ renameValue' name
    travCon c = c

    travVariable :: Variable -> Variable
    travVariable (Variable name tp) = Variable name $ travType tp
