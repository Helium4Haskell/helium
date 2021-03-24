module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import qualified Data.Map as M

----------------------------------------------------------------
-- Sorting environment
----------------------------------------------------------------

-- | Environment for sorting
type Gamma = M.Map Int Sort

-- | Insert a new variable into the sorting environment
envInsert :: Sort -> Gamma -> Gamma
envInsert s = M.insert 0 s . envWeaken

-- | Increase all env indexes by one
envWeaken :: Gamma -> Gamma
envWeaken = M.mapKeys $ (+) 1 

----------------------------------------------------------------
-- Sorting
----------------------------------------------------------------

-- TODO: Replace the rsInfo with rsError again (when the regions are generated)
-- | Fills in the sorts on the annotation, returns sort of full annotation
sort :: Annotation -> Sort
sort = sort' M.empty
    where sort' :: Gamma -> Annotation -> Sort 
          -- Simple cases
          sort' gamma (AVar     a) = gamma M.! a
          sort' _     (AReg     _) = SortMonoRegion
          sort' _     (AConstr  _) = SortConstr
          sort' _     (AUnit     ) = SortUnit
          
          -- Lambdas & applications
          sort' gamma (ALam   s a) = 
              let sortR = sort' (envInsert s gamma) a
              in SortLam s $ sortStrengthen sortR
          sort' gamma (AApl   f x) = 
              case sort' gamma f of
                SortLam sortA sortR ->
                  let sortX = sort' gamma x 
                  in if sortA == sortX 
                     then sortR
                     else sortR --`rsInfo` ("Argument has different sort than is expected.\nArgument sort: " ++ show sortX ++ "\nExpected sort: " ++ show sortA ++ "\n")
                s -> rsError $ "Application to non function sort: " ++ show s

          -- Tuples & projections
          sort' gamma (ATuple  as) =
              let sortAS = map (sort' gamma) as
              in SortTuple sortAS
          sort' gamma (AProj  i t) = 
              let SortTuple ss = sort' gamma t
              in if i < length ss
                 then ss !! i
                 else rsError "sort: Projection out of bounds"   

          -- Operators
          sort' gamma (AAdd   a b) = 
              let sortA = sort' gamma a
                  sortB = sort' gamma b
              in if sortA == sortB && sortA == SortConstr
                 then SortConstr
                 else SortConstr `rsInfo` ("Addition of non constraint-sort annotations: \nSort A:" ++ show sortA ++ "\nSort B:" ++ show sortB) 
          sort' gamma (AMinus a _) = 
              let sortA = sort' gamma a
              in if sortA == SortConstr
                 then SortConstr
                 else SortConstr `rsInfo` ("Setminus on non constraint-sort annotation: \nSort:" ++ show sortA) 

          sort' gamma (AJoin  a _) = sort' gamma a

          -- Quantification and instantiation
          sort' gamma (AQuant   a) = SortQuant $ sort' (envWeaken gamma) a
          sort' gamma (AInstn a t) = sortInstantiate t $ sort' gamma a 

          -- Lattice stuff
          sort' _     (ATop   s _) = s
          sort' _     (ABot   s  ) = s
          sort' gamma (AFix   s a) =
              let sortA = SortTuple $ sort' (envInsert s gamma) <$> a
              in if sortA == s
                 then sortA
                 else s `rsInfo` ("Fixpoint has incorrect sort: " ++ "\nNoted sort:   " ++ show s 
                                                                  ++ "\nDerived sort: " ++ show sortA)   

