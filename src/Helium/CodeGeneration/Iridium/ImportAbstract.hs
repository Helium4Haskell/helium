module Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule) where

import Data.Maybe (catMaybes, isNothing, mapMaybe)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Lvm.Common.Id (Id, idFromString)
import qualified Lvm.Core.Module as Core
import qualified Lvm.Core.Type as Core

toAbstractModule :: Module -> Core.Module v
toAbstractModule (Module name imports customs datas synonyms abstracts methods) = Core.Module name 0 0 imports decls
  where
    decls =
      map (setModule name) $
        mapMaybe convertCustom customs
          ++ (datas >>= convertData)
          ++ mapMaybe convertMethod methods
          ++ mapMaybe convertAbstractMethod abstracts
          ++ mapMaybe convertTypeSynonym synonyms

setModule :: Id -> Core.Decl v -> Core.Decl v
setModule modName decl
  | isNothing $ Core.declModule decl = decl {Core.declModule = Just modName}
  | otherwise = decl

convertCustom :: Declaration CustomDeclaration -> Maybe (Core.Decl v)
convertCustom (Declaration qname (ExportedAs name) mod customs (CustomDeclaration kind)) =
  Just $
    Core.DeclCustom qname (Core.Export name) mod kind customs
convertCustom _ = Nothing

convertData :: Declaration DataType -> [Core.Decl v]
convertData (Declaration qname (ExportedAs name) mod customs (DataType cons)) =
  Core.DeclCustom qname (Core.Export name) mod (Core.DeclKindCustom $ idFromString "data") customs
    : catMaybes (map convertConstructor cons)
convertData _ = []

convertConstructor :: Declaration DataTypeConstructorDeclaration -> Maybe (Core.Decl v)
convertConstructor (Declaration qname (ExportedAs name) mod customs (DataTypeConstructorDeclaration tp fs)) =
  Just $
    Core.DeclCon qname (Core.Export name) mod tp fs customs
convertConstructor _ = Nothing

convertMethod :: Declaration Method -> Maybe (Core.Decl v)
convertMethod (Declaration qname (ExportedAs name) mod customs method) =
  Just $
    Core.DeclAbstract qname (Core.Export name) mod (methodArity method) (methodType method) customs
convertMethod _ = Nothing

convertAbstractMethod :: Declaration AbstractMethod -> Maybe (Core.Decl v)
convertAbstractMethod (Declaration qname (ExportedAs name) mod customs (AbstractMethod arity tp mat)) =
  Just $ Core.DeclAbstract qname (Core.Export name) mod arity tp customs
convertAbstractMethod _ = Nothing

convertTypeSynonym :: Declaration TypeSynonym -> Maybe (Core.Decl v)
convertTypeSynonym d@(Declaration qname (ExportedAs name) mod customs (TypeSynonym tp)) =
  Just $
    Core.DeclTypeSynonym qname (Core.Export name) mod tp customs
convertTypeSynonym _ = Nothing
