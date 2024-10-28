-- Handles all declarations which are imported, during the conversion from Core to Iridium

module Helium.CodeGeneration.Iridium.FromCoreImports (fromCoreImports, visibility) where

import Data.List (find)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Either (isRight, partitionEithers)
import Helium.Lvm.Common.Id
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.FileCache
import qualified Helium.Lvm.Core.Expr as Core
import qualified Helium.Lvm.Core.Module as Core
import System.Exit

fromCoreImports :: FileCache -> [Core.CoreDecl] -> IO ([(Id, Declaration CustomDeclaration)], [(Id, Declaration DataType)], [(Id, Declaration TypeSynonym)], [(Id, Declaration AbstractMethod)])
fromCoreImports cache decls = do
  customs <- mapM (importCustom cache) decls
  datas' <- mapM (importData cache) decls
  let (datas, newtypes) = partitionEithers $ catMaybes datas'
  types <- mapM (importTypeSynonym cache) decls
  abstracts <- mapM (importAbstract cache) decls
  return (catMaybes customs, datas, catMaybes types ++ newtypes, catMaybes abstracts)

importCustom :: FileCache -> Core.CoreDecl -> IO (Maybe (Id, Declaration CustomDeclaration))
importCustom cache decl@Core.DeclCustom{}
  | Core.declKind decl /= Core.DeclKindCustom (idFromString "data") = Just <$> findDeclaration cache decl moduleCustoms
importCustom _ _ = return Nothing

importData :: FileCache -> Core.CoreDecl -> IO (Maybe (Either (Id, Declaration DataType) (Id, Declaration TypeSynonym)))
importData cache decl@Core.DeclCustom{}
  | Core.declKind decl == Core.DeclKindCustom (idFromString "data") = do
    d <- lookupDeclaration cache decl moduleDataTypes
    case d of
      Just d' -> return $ Just $ Left d'
      Nothing -> Just . Right <$> findDeclaration cache decl moduleTypeSynonyms
importData _ _ = return Nothing

importTypeSynonym :: FileCache -> Core.CoreDecl -> IO (Maybe (Id, Declaration TypeSynonym))
importTypeSynonym cache decl@Core.DeclTypeSynonym{} = Just <$> findDeclaration cache decl moduleTypeSynonyms
importTypeSynonym _ _ = return Nothing

importAbstract :: FileCache -> Core.CoreDecl -> IO (Maybe (Id, Declaration AbstractMethod))
importAbstract cache decl
  | isMethod = do
    method <- lookupDeclaration cache decl moduleMethods
    case method of
      Just (name, methodDecl) -> return $ Just (name, fmap toAbstract methodDecl)
      Nothing -> Just <$> findDeclaration cache decl moduleAbstractMethods
  where
    isMethod = case decl of
      Core.DeclValue{} -> True
      Core.DeclAbstract{} -> True
      _ -> False
    toAbstract :: Method -> AbstractMethod
    toAbstract method@(Method tp args _ annotations _ _) = AbstractMethod tp (methodFunctionType method) annotations
importAbstract _ _ = return Nothing

findDeclaration :: FileCache -> Core.CoreDecl -> (Module -> [Declaration a]) -> IO (Id, Declaration a)
findDeclaration cache decl getDeclarations = do
  maybeDecl <- lookupDeclaration cache decl getDeclarations
  case maybeDecl of
    Nothing -> reportError decl
    Just d -> return d

lookupDeclaration :: FileCache -> Core.CoreDecl -> (Module -> [Declaration a]) -> IO (Maybe (Id, Declaration a))
lookupDeclaration cache decl getDeclarations = do
  let moduleName = fromMaybe (error "fromCoreImports: expected an imported declaration, got a definition") $ Core.declModule decl
  importedModule <- readIridium cache moduleName
  return $ fmap (\d -> (Core.declName decl, setModule moduleName decl d)) $ find (\d -> declarationName d == Core.declName decl) $ getDeclarations importedModule

setModule :: Id -> Core.CoreDecl -> Declaration a -> Declaration a
setModule moduleName coreDecl decl = decl{ declarationModule = Just moduleName, declarationVisibility = visibility coreDecl }

reportError :: Core.CoreDecl -> IO a
reportError decl =  do
  putStrLn $ "Imported name " ++ stringFromId (Core.declName decl) ++ " was not found in module " ++ stringFromId moduleName
  exitWith (ExitFailure 1)
  where
    moduleName = case Core.declModule decl of
      Just mod -> mod
      _ -> error "fromCoreImports: expected an imported declaration, got a definition"

visibility :: Core.CoreDecl -> Visibility
visibility decl = case Core.declAccess decl of
  Core.Export name -> ExportedAs $ name
  Core.Private -> Private
