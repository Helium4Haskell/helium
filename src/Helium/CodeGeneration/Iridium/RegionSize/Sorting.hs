module Helium.CodeGeneration.Iridium.RegionSize.Sorting
where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import qualified Data.Map as M

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

-- | Environment for sorting
type Gamma = M.Map Int Sort

----------------------------------------------------------------
-- Sorting
----------------------------------------------------------------

-- | Fills in the sorts on the annotation
sort :: Annotation -> (Annotation, Sort)
sort = sort' M.empty
    where sort' :: Gamma -> Annotation -> (Annotation, Sort) 
          sort' gamma ann@(AVar a) = (ann, gamma M.! a)
          -- | TODO: More sorting
          sort' _ _ = error "Sorting not implemented"

