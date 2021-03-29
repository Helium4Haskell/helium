module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation

import qualified Data.Map as M
import Data.Either (lefts,rights)

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
sort :: Annotation -> Either String Sort
sort = sort' M.empty
    where sort' :: Gamma -> Annotation -> Either String Sort 
          -- Simple cases
          sort' gamma (AVar     a) = case M.lookup a gamma of
                                        Nothing -> Left $ "Not in gamma: " ++ show a
                                        Just s  -> Right s
          sort' _     (AReg     _) = Right SortMonoRegion
          sort' _     (AConstr  _) = Right SortConstr
          sort' _     (AUnit     ) = Right SortUnit
          
          -- Lambdas & applications
          sort' gamma (ALam   s a) = 
              let sortR = sort' (envInsert s gamma) a
              in SortLam s <$> sortStrengthen <$> sortR
          sort' gamma (AApl   f x) = 
              case sort' gamma f of
                Right (SortLam sortA sortR) ->
                  let sortX = sort' gamma x 
                  in if Right sortA == sortX 
                     then Right sortR
                     else sortX --sortR --`rsInfo` ("Argument has different sort than is expected.\nArgument sort: " ++ show sortX ++ "\nExpected sort: " ++ show sortA ++ "\n")
                Right s -> Left $ "Application to non function sort: " ++ show s
                err     -> err

          -- Tuples & projections
          sort' gamma (ATuple  as) =
              let sortAS = map (sort' gamma) as
                  errors = lefts sortAS  
              in if length errors == 0 
                 then Right . SortTuple $ rights sortAS
                 else Left (errors !! 0) 
          sort' gamma (AProj  i t) = 
              case sort' gamma t of
                  Right (SortTuple ss) -> if i < length ss
                                          then Right $ ss !! i
                                          else Left "sort: Projection out of bounds"   
                  Right s -> Left $ "Projection on non-tuple sort: " ++ show s
                  err     -> err

          -- Operators
          sort' gamma (AAdd   a b) = 
              let sortA = sort' gamma a
                  sortB = sort' gamma b
              in if sortA == sortB && sortA == Right SortConstr
                 then Right SortConstr
                 else Left ("Addition of non constraint-sort annotations: \nSort A:" ++ show sortA ++ "\nSort B:" ++ show sortB) 
          sort' gamma (AMinus a _) = 
              let sortA = sort' gamma a
              in if sortA == Right SortConstr
                 then Right SortConstr
                 else Left $ "Setminus on non constraint-sort annotation: \nSort:" ++ show sortA 

          sort' gamma (AJoin  a _) = sort' gamma a

          -- Quantification and instantiation
          sort' gamma (AQuant   a) = SortQuant <$> sort' (envWeaken gamma) a
          sort' gamma (AInstn a t) = 
              case sort' gamma a of
                  Right (SortQuant s) -> Right . sortInstantiate t $ SortQuant s 
                  Right s -> Left $ "Instantiation on non-quantified sort: " ++ show s
                  err     -> err

          -- Lattice stuff
          sort' _     (ATop   s _) = Right s
          sort' _     (ABot   s  ) = Right s
          sort' _     (AFix   s _) = Right s

