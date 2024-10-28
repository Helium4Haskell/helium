module Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule) where

import Data.Maybe(mapMaybe, catMaybes, isNothing)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.Lvm.Common.Id (Id, idFromString, stringFromId)
import qualified Helium.Lvm.Core.Module as Core
import qualified Helium.Lvm.Core.Type as Core

toAbstractModule :: Module -> Core.Module v
toAbstractModule (Module name imports customs datas synonyms abstracts methods) = Core.Module name 0 0 imports decls
  where
    decls = map (setModule name)
      $ mapMaybe convertCustom customs
      ++ (datas >>= convertData)
      ++ mapMaybe convertMethod methods
      ++ mapMaybe convertAbstractMethod abstracts
      ++ (synonyms >>= convertTypeSynonym)

setModule :: Id -> Core.Decl v -> Core.Decl v
setModule modName decl
  | isNothing $ Core.declModule decl = decl{ Core.declModule = Just modName }
  | otherwise = decl

convertCustom :: Declaration CustomDeclaration -> Maybe (Core.Decl v)
convertCustom (Declaration qname (ExportedAs name) mod customs (CustomDeclaration kind)) = Just $
  Core.DeclCustom qname (Core.Export name) mod kind customs
convertCustom _ = Nothing

convertData :: Declaration DataType -> [Core.Decl v]
convertData (Declaration qname (ExportedAs name) mod customs (DataType cons)) =
  Core.DeclCustom qname (Core.Export name) mod (Core.DeclKindCustom $ idFromString "data") customs
  : catMaybes (map convertConstructor cons)
convertData _ = []

-- TODO: Can the fields be exported, if the data type isn't exported?
convertConstructor :: Declaration DataTypeConstructorDeclaration -> Maybe (Core.Decl v)
convertConstructor (Declaration qname (ExportedAs name) mod customs (DataTypeConstructorDeclaration tp fs)) = Just $
  Core.DeclCon qname (Core.Export name) mod tp fs customs
convertConstructor _ = Nothing

convertMethod :: Declaration Method -> Maybe (Core.Decl v)
convertMethod (Declaration qname (ExportedAs name) mod customs method) = Just $
  Core.DeclAbstract qname (Core.Export name) mod (methodArity method) (methodSourceType method) customs
convertMethod _ = Nothing

convertAbstractMethod :: Declaration AbstractMethod -> Maybe (Core.Decl v)
convertAbstractMethod (Declaration qname (ExportedAs name) mod customs (AbstractMethod sourceType fnType _)) = Just $
  Core.DeclAbstract qname (Core.Export name) mod (functionArity fnType) sourceType customs
convertAbstractMethod _ = Nothing

convertTypeSynonym :: Declaration TypeSynonym -> [Core.Decl v]
convertTypeSynonym d@(Declaration qname (ExportedAs name) mod customs (TypeSynonym TypeSynonymAlias tp)) = return $
  Core.DeclTypeSynonym qname (Core.Export name) mod Core.TypeSynonymAlias tp customs
-- TODO: What if the data type is not exported, but the destructor is?
convertTypeSynonym d@(Declaration qname (ExportedAs name) mod customs (TypeSynonym (TypeSynonymNewtype constructor destructor) tp)) =
  Core.DeclTypeSynonym qname (Core.Export name) mod Core.TypeSynonymNewtype tp customs
    : constructorDecl
  where
    constructorDecl = case constructor of
      ExportedAs construct -> return $ Core.DeclCon (idFromString $ stringFromId qname ++ "." ++ stringFromId construct) (Core.Export construct) mod constructorType fields constructorCustom
      Private -> []
    constructorCustom = [Core.CustomLink qname (Core.DeclKindCustom (idFromString "data"))]
    fields = case destructor of
      ExportedAs destruct -> [Core.Field destruct]
      Private -> []
    (constructorType, _) = newtypeConstructorType d
convertTypeSynonym _ = []
