module Helium.CodeGeneration.Iridium.RegionSize.Type
    ( rsShowType, typeRemoveQuants
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Lvm.Core.Type as Type

-- | Show a type with region size naming convention
rsShowType :: Type -> String
rsShowType = showType ((:) 't' <$> varNames)

-- | Remove quantifications
typeRemoveQuants :: Type -> Type
typeRemoveQuants (TForall _ _ t) = typeRemoveQuants t
typeRemoveQuants t = t