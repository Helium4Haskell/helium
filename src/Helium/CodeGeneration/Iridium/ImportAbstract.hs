module Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule) where

import Data.Maybe(mapMaybe)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Lvm.Common.Id (Id)
import qualified Lvm.Core.Module as Core

toAbstractModule :: Module -> Core.Module v
toAbstractModule (Module name _ customs datas abstracts methods) = Core.Module name 0 0 $ mapMaybe (convertMethod name) methods ++ mapMaybe (convertAbstractMethod name) abstracts

convertMethod :: Id -> Declaration Method -> Maybe (Core.Decl v)
convertMethod moduleName (Declaration name Exported mod customs (Method args _ _ _ _)) = Just $
  Core.DeclAbstract name (toAccess name mod) (length args) customs
convertMethod _ _ = Nothing

convertAbstractMethod :: Id -> Declaration AbstractMethod -> Maybe (Core.Decl v)
convertAbstractMethod moduleName (Declaration name Exported mod customs (AbstractMethod (FunctionType args _) _)) = Just $
  Core.DeclAbstract name (toAccess name mod) (length args) customs
convertAbstractMethod _ _ = Nothing

-- TODO: Convert other declarations

toAccess :: Id -> Maybe Id -> Core.Access
toAccess _ Nothing = Core.Defined True
toAccess name (Just mod) = Core.Imported True mod name Core.DeclKindValue 0 0
