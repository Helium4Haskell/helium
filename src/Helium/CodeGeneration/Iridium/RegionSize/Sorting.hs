module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map.Strict as M
import Data.Either (lefts,rights,fromRight)
import Data.List (find)

----------------------------------------------------------------
-- Sorting environment
----------------------------------------------------------------

-- | Environment for sorting
type Gamma = M.Map Int Sort

-- | Insert a new variable into the sorting environment
envInsert :: Sort -> Gamma -> Gamma
envInsert s = M.insert 0 s . M.mapKeys ((+) 1)

-- | Increase all env indexes by one
envWeaken :: Gamma -> Gamma
envWeaken =  M.map (sortWeaken 0)

----------------------------------------------------------------
-- Sorting
----------------------------------------------------------------

-- | Fills in the sorts on the annotation, returns sort of full annotation
sort :: DataTypeEnv -> Annotation -> Either String Sort
sort dEnv = sort' (-1,-1) M.empty
    where sort' :: (Int,Int) -> Gamma -> Annotation -> Either String Sort 
          -- Simple cases
          sort' d gamma (AVar     a) = case M.lookup a gamma of
                                        Nothing -> Left $ "Sorting: Variable not in environment. " 
                                                       ++ "\n  Variable: " ++ (annShow' d $ AVar a)
                                        Just s  -> Right s
          sort' _ _     (AReg     _) = Right SortMonoRegion
          sort' _ _     (AUnit     ) = Right SortUnit
          sort' d _     (AConstr  c) = case checkConstr (fst d) c of
                                          Nothing -> Right SortConstr
                                          Just er -> Left er 
          -- Top and bot are annotated with their sort
          sort' d _ (ATop s c) = case checkConstr (fst d) c of
                                     Nothing -> Right s
                                     Just er -> Left er 
          sort' _ _ (ABot s  ) = Right s

          -- Check body of the fixpoint
          sort' d gamma (AFix s a) = 
              let fs = sort' d gamma (ALam (SortTuple s) (ATuple a))
              in case fs of
                   (Right (SortLam _ sR)) | fixSortEq (SortTuple s) sR -> Right sR
                                          | otherwise -> Left $ "Sorting: Sort does not match fixpoint sort." 
                                                             ++ "\n  Expected sort: " ++ (showSort (snd d) $ SortTuple s) 
                                                             ++ "\n  Actual sort:   " ++ (showSort (snd d) sR)
                                                             ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' d (AFix s a)) ++ "\n"
                   Left xs  -> Left xs
                   Right s' -> Left $ "Invalid fixpoint sort" 
                                   ++ "\n  Sort: " ++ showSort (snd d) s'
                                   ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' d (AFix s a)) ++ "\n"

          -- Check if both operands have the same sort
          sort' d gamma (AJoin  a b) = 
              let sortA = sort' d gamma a
                  sortB = sort' d gamma b
              in if sortA == sortB
                 then sortA
                 else case (sortA, sortB) of
                     (Left errA,_) -> Left errA
                     (_,Left errB) -> Left errB
                     (Right sa,Right sb) -> Left $ "Sorting: Join of annotations with different sort."
                                                ++ "\n  Sort A: " ++ showSort (snd d) sa 
                                                ++ "\n  Sort B: " ++ showSort (snd d) sb
                                                ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' d (AJoin  a b)) ++ "\n"

          -- Lambdas & applications
          sort' (dL,dQ) gamma (ALam   s a) = 
              let sortR = sort' (dL+1,dQ) (envInsert s gamma) a
              in SortLam s <$> sortR
          sort' (dL,dQ)  gamma (AApl   f x) = 
              case sort' (dL,dQ)  gamma f of
                Right (SortLam sortA sortR) ->
                  let sortX = sort' (dL,dQ)  gamma x 
                  in case sortX of
                        Right sX | checkArgSort sortA sX -> Right sortR
                                 | otherwise -> Left $ "Sorting: Argument has different sort than is expected."
                                                     ++ "\n  Argument sort: " ++ showSort dQ sX
                                                     ++ "\n  Expected sort: " ++ showSort dQ sortA
                                                     ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' (dL,dQ) (AApl f x)) ++ "\n"
                        err     -> err
                Right s -> Left $ "Sorting: Application to non function sort."
                               ++ "\n  Sort: " ++ (showSort dQ s)
                               ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' (dL,dQ) (AApl f x)) ++ "\n"
                err     -> err

          -- Tuples & projections
          sort' (dL,dQ) gamma (ATuple  as) =
              let sortAS = map (sort' (dL,dQ) gamma) as
                  errors = lefts sortAS  
              in if length errors == 0 
                 then Right . SortTuple $ rights sortAS
                 else Left (errors !! 0) 
          sort' (dL,dQ) gamma (AProj  i t) = 
              case sort' (dL,dQ) gamma t of
                  Right (SortTuple ss) -> if i < length ss
                                          then Right $ ss !! i
                                          else Left $ "Sorting: Projection out of bounds."
                                                   ++ "\n  Index: " ++ show i 
                                                   ++ "\n  Sort:  " ++ showSort dQ (SortTuple ss) 
                                                   ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' (dL,dQ) (AProj i t)) ++ "\n"
                  Right SortMonoRegion -> Right SortMonoRegion
                  Right s -> Left $ "Sorting: Projection on non-tuple sort:"
                                 ++ "\n  Sort: " ++ showSort dQ s 
                                 ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' (dL,dQ) (AProj i t)) ++ "\n"
                  err     -> err

          -- Operators
          sort' d gamma (AAdd   a b) = 
              let sortA = sort' d gamma a
                  sortB = sort' d gamma b
              in if sortA == sortB && sortA == Right SortConstr
                 then Right SortConstr
                 else case (sortA, sortB) of
                     (Left errA,_) -> Left errA
                     (_,Left errB) -> Left errB
                     (_,_) -> Left $ "Sorting: Addition of non constraint-sort annotations."
                                  ++ "\n  Sort A: " ++ showSort (snd d) (fromRight undefined sortA) 
                                  ++ "\n  Sort B: " ++ showSort (snd d) (fromRight undefined sortB)
                                  ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' d (AAdd a b)) ++ "\n"
          sort' d gamma (AMinus a r) = 
              let sortA = sort' d gamma a
              in case sortA of 
                    (Left _) -> sortA
                    (Right SortConstr) -> Right SortConstr
                    (Right sa) -> Left $ "Sorting: Setminus on non constraint-sort annotation."
                                      ++ "\n  Sort:" ++ showSort (snd d) sa
                                      ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' d (AMinus a r)) ++ "\n"

          -- Quantification and instantiation
          sort' (dL,dQ) gamma (AQuant   a) = SortQuant <$> sort' (dL,dQ+1) (envWeaken gamma) a
          sort' (dL,dQ) gamma (AInstn a t) = 
              case sort' (dL,dQ) gamma a of
                  Right (SortQuant s) -> Right . sortInstantiate dEnv t $ SortQuant s 
                  Right s -> Left $ "Sorting: Instantiation on non-quantified sort."
                                 ++ "\n  Sort: " ++ showSort dQ s
                                 ++ "\n  Annotation:\n\n" ++ (indent "    " $ annShow' (dL,dQ) (AInstn a t)) ++ "\n"
                  err     -> err


-- | Check if the indexes in a constraint set are bound
checkConstr :: Int -> Constr -> Maybe String
checkConstr depth c = find ((<) 0 . length) $ checkConstrIdx . fst <$> M.toList c
    where checkConstrIdx :: ConstrIdx -> String
          checkConstrIdx (Region _) = ""             
          checkConstrIdx (AnnVar a) = if a < 0
                                      then ("Sorting: Negative constraint set variable index."
                                           ++ "\n  Variable:" ++ annShow' (depth,0) (AVar a))
                                      else if a > depth
                                           then ("Sorting: Unbound constraint set variable index."
                                                 ++ "\n  Variable:" ++ annShow' (depth,0) (AVar a))
                                           else ""
          checkConstrIdx (CnProj _ x) = checkConstrIdx x             
                                      
{- | Check if two arguments are the same
    We allow a monoregion argument for a polyregion sort
-}
checkArgSort :: Sort -- Expected sort 
             -> Sort -- Argument
             -> Bool
-- Recurse into tuples
checkArgSort (SortTuple as) (SortTuple bs) =
    let sameLength = length as == length bs
        recurse    = and $ uncurry checkArgSort <$> zip as bs
    in sameLength && recurse
-- Allow application of monovariant region to polyvariant region
checkArgSort (SortPolyRegion _ _) SortMonoRegion = True
-- Allow application of monovariant region to polyvariant region
checkArgSort (SortUnit)           SortMonoRegion = True
-- Allow application of a unit to a quantified unit
checkArgSort (SortQuant a')       SortUnit       = checkArgSort a' SortUnit
checkArgSort a b = a == b 

-- | Check if sorts are equal
fixSortEq :: Sort -- Expected sort 
          -> Sort -- Computed sort
          -> Bool
fixSortEq (SortLam a1 a2) (SortLam b1 b2) = checkArgSort a1 b1 && fixSortEq a2 b2 
fixSortEq (SortQuant  a1) (SortQuant  b1) = fixSortEq a1 b1
fixSortEq (SortTuple  as) (SortTuple  bs) = and $ zipWith fixSortEq as bs
fixSortEq a b = a == b
