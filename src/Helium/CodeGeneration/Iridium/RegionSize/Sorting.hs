module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes

import qualified Data.Map as M
import Data.Either (lefts,rights)
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
                                        Nothing -> Left $ "Not in gamma: " ++ (annShow' d $ AVar a)
                                        Just s  -> Right s
          sort' _ _     (AReg     _) = Right SortMonoRegion
          sort' _ _     (AUnit     ) = Right SortUnit
          sort' d _     (AConstr  c) = case checkConstr (fst d) c of
                                          Nothing -> Right SortConstr
                                          Just er -> Left er 
          -- Top and bot are annotated with their sort
          sort' d _ (ATop   s c) = case checkConstr (fst d) c of
                                     Nothing -> Right s
                                     Just er -> Left er 
          sort' _ _ (ABot   s  ) = Right s

          -- Check body of the fixpoint
          sort' d gamma (AFix   s a) = 
              let fs = sort' d gamma (ALam (SortTuple s) (ATuple a))
              in case fs of
                   (Right (SortLam _ sR)) | SortTuple s == sR -> Right sR
                                          | otherwise -> Left "Invalid fixpoint sort"
                   Left xs -> Left xs
                   Right _ -> Left "Invalid fixpoint sort"
          -- Check if both operands have the same sort
          sort' d gamma (AJoin  a b) = 
              let sortA = sort' d gamma a
                  sortB = sort' d gamma b
              in if sortA == sortB
                 then sortA
                 else Left ("Join of annotations with different sort: \nSort A: " ++ show sortA ++ "\nSort B: " ++ show sortB) 

          -- Lambdas & applications
          sort' (dL,dQ) gamma (ALam   s a) = 
              let sortR = sort' (dL+1,dQ) (envInsert s gamma) a
              in SortLam s <$> sortR
          sort' (dL,dQ)  gamma (AApl   f x) = 
              case sort' (dL,dQ)  gamma f of
                Right (SortLam sortA sortR) ->
                  let sortX = sort' (dL,dQ)  gamma x 
                  in case sortX of
                        Right sX | checkArgs sortA sX -> Right sortR
                                 | otherwise -> Left $ "Argument has different sort than is expected.\nArgument sort: " ++ (showSort dQ sX) ++ "\nExpected sort: " ++ (showSort dQ sortA) ++ "\nResult of lambda:" ++ showSort dQ sortR ++ "\n"
                        err     -> err
                Right s -> Left $ "Application to non function sort:\nSort:     " ++ (showSort dQ s)
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
                                          else Left "sort: Projection out of bounds"   
                  Right s -> Left $ "Projection on non-tuple sort: " ++ showSort dQ s
                  err     -> err

          -- Operators
          sort' (dL,dQ) gamma (AAdd   a b) = 
              let sortA = sort' (dL,dQ) gamma a
                  sortB = sort' (dL,dQ) gamma b
              in if sortA == sortB && sortA == Right SortConstr
                 then Right SortConstr
                 else case (sortA, sortB) of
                     (Left errA,_) -> Left errA
                     (_,Left errB) -> Left errB
                     (_,_) -> Left ("Addition of non constraint-sort annotations: \nSort A: " ++ show sortA ++ "\nSort B: " ++ show sortB) 
        --   sort' (dL,dQ) gamma (AMinus a _) = 
        --       let sortA = sort' (dL,dQ) gamma a
        --       in if sortA == Right SortConstr
        --          then Right SortConstr
        --          else Left $ "Setminus on non constraint-sort annotation: \nSort:" ++ show sortA 

          -- Quantification and instantiation
          sort' (dL,dQ) gamma (AQuant   a) = SortQuant <$> sort' (dL,dQ+1) (envWeaken gamma) a
          sort' (dL,dQ) gamma (AInstn a t) = 
              case sort' (dL,dQ) gamma a of
                  Right (SortQuant s) -> Right . sortInstantiate dEnv t $ SortQuant s 
                  Right s -> Left $ "Instantiation on non-quantified sort: " ++ showSort dQ s
                  err     -> err


-- | Check if the indexes in a constraint set are bound
checkConstr :: Int -> Constr -> Maybe String
checkConstr depth c = find ((<) 0 . length) $ checkConstrIdx . fst <$> M.toList c
    where checkConstrIdx :: ConstrIdx -> String
          checkConstrIdx (Region _) = ""             
          checkConstrIdx (AnnVar a) = if a < 0
                                      then "Negative constraint index"
                                      else if a > depth
                                           then "Unbound index"
                                           else ""
          checkConstrIdx (CnProj _ x) = checkConstrIdx x             
                                      
{- | Check if two arguments are the same
    We allow a monoregion argument for a polyregion sort
-}
checkArgs :: Sort -- Expected sort 
          -> Sort -- Argument
          -> Bool
checkArgs (SortTuple as) (SortTuple bs) = (length as == length bs) && (and $ uncurry checkArgs <$> zip as bs)
checkArgs (SortPolyRegion _ _) SortMonoRegion = True
checkArgs a b = a == b 