module Helium.CodeGeneration.Iridium.RegionSize.Sorting
    ( sort
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes

import qualified Data.Map as M
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
                                                       ++ "\n\tVariable: " ++ (annShow' d $ AVar a)
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
                   (Right (SortLam _ sR)) | SortTuple s == sR -> Right sR
                                          | otherwise -> Left $ "Sorting: Sort does not match fixpoint sort." 
                                                             ++ "\n\tExpected sort: " ++ (showSort (snd d) $ SortTuple s) 
                                                             ++ "\n\tActual sort:   " ++ (showSort (snd d) sR)
                                                             ++ "\n\tAnnotation:   " ++ (annShow' d (AFix s a))
                                                                                                    
                   Left xs  -> Left xs
                   Right s' -> Left $ "Invalid fixpoint sort" 
                                   ++ "\nSort: " ++ showSort (snd d) s'
                                   ++ "\nAnnotation:   " ++ (annShow' d (AFix s a))
          -- Check if both operands have the same sort
          sort' d gamma (AJoin  a b) = 
              let sortA = sort' d gamma a
                  sortB = sort' d gamma b
              in if sortA == sortB
                 then sortA
                 else Left $ "Sorting: Join of annotations with different sort."
                          ++ "\n\tSort A: " ++ show sortA 
                          ++ "\n\tSort B: " ++ show sortB
                          ++ "\n\tAnnotation: " ++ annShow' d (AJoin  a b)

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
                                                     ++ "\n\tArgument sort: " ++ showSort dQ sX
                                                     ++ "\n\tExpected sort: " ++ showSort dQ sortA
                                                     ++ "\n\tAnnotation:" ++ annShow' (dL,dQ) (AApl f x)
                        err     -> err
                Right s -> Left $ "Sorting: Application to non function sort."
                               ++ "\n\tSort: " ++ (showSort dQ s)
                               ++ "\n\tAnnotation: " ++ annShow' (dL,dQ) (AApl f x)
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
                                                   ++ "\n\tIndex:" ++ show i 
                                                   ++ "\n\tSort" ++ showSort dQ (SortTuple ss) 
                                                   ++ "\n\tAnnotation:" ++ annShow' (dL,dQ) (AProj i t)  
                  Right s -> Left $ "Sorting: Projection on non-tuple sort:"
                                 ++ "\n\tSort: " ++ showSort dQ s 
                                 ++ "\n\tAnnotation: " ++ annShow' (dL,dQ) (AProj i t)
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
                                  ++ "\n\tSort A: " ++ showSort (snd d) (fromRight undefined sortA) 
                                  ++ "\n\tSort B: " ++ showSort (snd d) (fromRight undefined sortB)
                                  ++ "\n\tAnnotation: " ++ annShow' d (AAdd a b)
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
                  Right s -> Left $ "Sorting: Instantiation on non-quantified sort."
                                 ++ "\n\tSort: " ++ showSort dQ s
                                 ++ "\n\tAnnotation: " ++ annShow' (dL,dQ) (AInstn a t)
                  err     -> err


-- | Check if the indexes in a constraint set are bound
checkConstr :: Int -> Constr -> Maybe String
checkConstr depth c = find ((<) 0 . length) $ checkConstrIdx . fst <$> M.toList c
    where checkConstrIdx :: ConstrIdx -> String
          checkConstrIdx (Region _) = ""             
          checkConstrIdx (AnnVar a) = if a < 0
                                      then ("Sorting: Negative constraint set variable index."
                                           ++ "\n\tVariable:" ++ annShow' (depth,0) (AVar a))
                                      else if a > depth
                                           then ("Sorting: Unbound constraint set variable index."
                                                 ++ "\n\tVariable:" ++ annShow' (depth,0) (AVar a))
                                           else ""
          checkConstrIdx (CnProj _ x) = checkConstrIdx x             
                                      
{- | Check if two arguments are the same
    We allow a monoregion argument for a polyregion sort
-}
checkArgSort :: Sort -- Expected sort 
             -> Sort -- Argument
             -> Bool
checkArgSort (SortTuple as) (SortTuple bs) =
    let sameLength = length as == length bs
        recurse    = and $ uncurry checkArgSort <$> zip as bs
    in sameLength && recurse
checkArgSort (SortPolyRegion _ _) SortMonoRegion = True
checkArgSort a b = a == b 