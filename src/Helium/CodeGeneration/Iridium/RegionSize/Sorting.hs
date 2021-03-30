module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort

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
envWeaken = M.mapKeys ((+) 1) . M.map (sortWeaken 1)

----------------------------------------------------------------
-- Sorting
----------------------------------------------------------------

-- TODO: Still some reindexing bug.. probs goes wrong at SortLam
-- | Fills in the sorts on the annotation, returns sort of full annotation
sort :: Annotation -> Either String Sort
sort = sort' (-1) M.empty
    where sort' :: Int -> Gamma -> Annotation -> Either String Sort 
          -- Simple cases
          sort' d gamma (AVar     a) = case M.lookup a gamma of
                                        Nothing -> Left $ "Not in gamma: " ++ (annShow d $ AVar a)
                                        Just s  -> Right s
          sort' _ _     (AReg     _) = Right SortMonoRegion
          sort' _ _     (AConstr  _) = Right SortConstr
          sort' _ _     (AUnit     ) = Right SortUnit
          
          -- Lambdas & applications
          sort' d gamma (ALam   s a) = 
              let sortR = sort' (d+1) (envInsert s gamma) a
              in SortLam s <$> sortStrengthen <$> sortR
          sort' d gamma (AApl   f x) = 
              case sort' d gamma f of
                Right (SortLam sortA sortR) ->
                  let sortX = sort' d gamma x 
                  in case sortX of
                        Right sX | sX == sortA -> Right sortR 
                                 | otherwise   -> Left $ "Argument has different sort than is expected.\nArgument sort: " ++ (showSort d sX) ++ "\nExpected sort: " ++ (showSort d sortA) ++ "\n"
                        err     -> err
                Right s -> Left $ "Application to non function sort:\nSort:     " ++ (showSort d s)
                err     -> err

          -- Tuples & projections
          sort' d gamma (ATuple  as) =
              let sortAS = map (sort' d gamma) as
                  errors = lefts sortAS  
              in if length errors == 0 
                 then Right . SortTuple $ rights sortAS
                 else Left (errors !! 0) 
          sort' d gamma (AProj  i t) = 
              case sort' d gamma t of
                  Right (SortTuple ss) -> if i < length ss
                                          then Right $ ss !! i
                                          else Left "sort: Projection out of bounds"   
                  Right s -> Left $ "Projection on non-tuple sort: " ++ show s
                  err     -> err

          -- Operators
          sort' d gamma (AAdd   a b) = 
              let sortA = sort' d gamma a
                  sortB = sort' d gamma b
              in if sortA == sortB && sortA == Right SortConstr
                 then Right SortConstr
                 else Left ("Addition of non constraint-sort annotations: \nSort A: " ++ show sortA ++ "\nSort B: " ++ show sortB) 
          sort' d gamma (AMinus a _) = 
              let sortA = sort' d gamma a
              in if sortA == Right SortConstr
                 then Right SortConstr
                 else Left $ "Setminus on non constraint-sort annotation: \nSort:" ++ show sortA 

          sort' d gamma (AJoin  a _) = sort' d gamma a

          -- Quantification and instantiation
          sort' d gamma (AQuant   a) = SortQuant <$> sort' (d+1) (envWeaken gamma) a
          sort' d gamma (AInstn a t) = 
              case sort' d gamma a of
                  Right (SortQuant s) -> Right . sortInstantiate t $ SortQuant s 
                  Right s -> Left $ "Instantiation on non-quantified sort: " ++ showSort d s
                  err     -> err

          -- Lattice stuff
          sort' _ _     (ATop   s _) = Right s
          sort' _ _     (ABot   s  ) = Right s
          sort' _ _     (AFix   s _) = Right s

