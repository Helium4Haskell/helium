module Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule) where

import Data.Maybe(mapMaybe)
import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id (Id)
import qualified Lvm.Core.Module as Core

toAbstractModule :: Module -> Core.Module v
toAbstractModule (Module name _ customs datas abstracts methods) = Core.Module name 0 0 $ mapMaybe (convertMethod name) methods

convertMethod :: Id -> Declaration Method -> Maybe (Core.Decl v)
convertMethod moduleName (Declaration name Exported customs (Method args _ _ _ _)) = Just $
  Core.DeclAbstract name (Core.Defined True) (length args) customs
convertMethod _ _ = Nothing

-- TODO: Convert other methods
