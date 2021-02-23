module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import qualified Data.Map as M

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

-- | Environment for sorting
type Gamma = M.Map Int Sort
data Sub = Sub Int Sort
type Subs = [Sub]

----------------------------------------------------------------
-- Sorting
----------------------------------------------------------------

-- | Fills in the sorts on the annotation
sort :: Annotation -> (Subs, Annotation, Sort)
sort = sort' M.empty
    where sort' :: Gamma -> Annotation -> (Subs, Annotation, Sort) 
          sort' gamma ann@(AVar a) = ([], ann, gamma M.! a)
          -- | TODO: More sorting
          sort' _ _ = error "Sorting not implemented"

----------------------------------------------------------------
-- Environment utilities
----------------------------------------------------------------

-- | Increase all env indexes by one
envWeaken :: Gamma -> Gamma
envWeaken = M.mapKeys $ (+) 1

-- | TODO: Perform substitutions on gamma
(=:) :: Subs -> Gamma -> Gamma
_ =: g = g 
