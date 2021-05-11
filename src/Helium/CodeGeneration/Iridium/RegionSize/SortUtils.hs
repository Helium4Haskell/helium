
module Helium.CodeGeneration.Iridium.RegionSize.SortUtils
    (sortAssign, regionAssign,
     sortInstantiate, sortSubstitute, 
    sortReIndex, sortStrengthen, sortWeaken,
    sortIsRegion, sortIsAnnotation,
    indexSortTuple, sortDropLam,
    regionVarsToSort
  )
where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort

import Lvm.Common.Id
import Lvm.Core.Type
import Data.List

----------------------------------------------------------------
-- Sort assignment
----------------------------------------------------------------

-- | Sort assignment based on type
sortAssign :: DataTypeEnv -> Type -> Sort
sortAssign dEnv = sortAssign' dEnv []

-- | Sort assingment with type arguments
sortAssign' :: DataTypeEnv
            -> [Type] -- ^ Type arguments
            -> Type -> Sort
sortAssign' dEnv ts (TStrict a)     = sortAssign' dEnv ts a
sortAssign' dEnv ts (TForall _ _ a) = SortQuant $ sortAssign' dEnv ts a
sortAssign' dEnv ts (TVar a)        = SortPolySort a ts
-- Type constructors (functions, tuples, simple data types)
sortAssign' dEnv ts (TAp t1 t2)     = sortAssign' dEnv (t2:ts) t1
sortAssign' dEnv [t1,t2] (TCon TConFun)       = funSort dEnv t1 t2  
sortAssign' dEnv ts      (TCon (TConTuple n)) | length ts == n = SortTuple $ map (sortAssign dEnv) ts
                                         | otherwise      = rsError $ "sortAssign: Tuple with incorrect number of arguements: expected " ++ show n 
                                                                   ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
sortAssign' dEnv [a]     (TCon (TConTypeClassDictionary _)) = funSort dEnv (TCon (TConDataType $ idFromString "TODO: Dictionaries")) a
sortAssign' dEnv ts      (TCon (TConDataType name)) = foldl (flip $ sortInstantiate dEnv) (name `lookupDataType` dEnv) ts

-- | Sort for a function: t_1 -> t2 ===> SA(t_1) -> RA(t_2) -> (SA(t_2), C)
funSort :: DataTypeEnv -> Type -> Type -> Sort
funSort dEnv t1 t2 = SortLam (sortAssign dEnv t1) 
                   $ SortLam (regionAssign dEnv $ TStrict t2) 
                   $ SortTuple [sortAssign dEnv t2, SortConstr]

----------------------------------------------------------------
-- Region assignment
----------------------------------------------------------------

-- | Region assignment based on type
regionAssign :: DataTypeEnv -> Type -> Sort
regionAssign dEnv ty | typeIsStrict ty = SortTuple [SortMonoRegion                , regionAssign' dEnv [] ty]
                     | otherwise       = SortTuple [SortMonoRegion, SortMonoRegion, regionAssign' dEnv [] ty]

-- | Region assingment with type arguments
regionAssign' :: DataTypeEnv
              -> [Type] -- ^ Type arguments
              -> Type -> Sort
regionAssign' dEnv ts (TVar a)        = SortPolyRegion a ts
regionAssign' dEnv ts (TStrict a)     = regionAssign' dEnv ts a
regionAssign' dEnv ts (TForall _ _ a) = SortQuant $ regionAssign' dEnv ts a
-- Type constructors (functions, tuples, simple data types)
regionAssign' dEnv ts (TAp t1 t2)     = regionAssign' dEnv (t2:ts) t1
regionAssign' dEnv [_,_] (TCon TConFun      ) = SortUnit
regionAssign' dEnv ts    (TCon (TConTuple n)) | length ts == n = SortTuple . concat $ map (sortUnpackTuple.regionAssign dEnv) ts
                                         | otherwise      = rsError $ "regionAssign: Tuple with incorrect number of arguements: expected " ++ show n ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
regionAssign' dEnv []    (TCon (TConDataType _)) = SortUnit
regionAssign' dEnv [a]   (TCon (TConTypeClassDictionary _)) = regionAssign dEnv a
-- TODO: Data types
regionAssign' dEnv _     (TCon (TConDataType _)) = SortUnit `rsInfo` "regionAssign: Datatypes not yet supported"
-- Not implemented cases
regionAssign' dEnv ts t = rsError $ "regionAssign: No pattern match: " ++ showTypeN 0 t 
                                  ++ "\nArguments: " ++ (intercalate ", " $ map (showTypeN 0) ts)

----------------------------------------------------------------
-- Type substitution
----------------------------------------------------------------

-- | Instatiate a type argument, sort should start wit SortQuant
sortInstantiate :: DataTypeEnv -> Type -> Sort -> Sort
sortInstantiate dEnv t (SortQuant s) = sortSubstitute dEnv 0 t s
sortInstantiate dEnv _ s = rsError $ "Tried to instantiate a sort that does not start with SortQuant\nSort:" ++ show s

-- | Instatiate a quantified type in a sort
-- TODO: Check if type instantiate also strengthens indexes
sortSubstitute :: DataTypeEnv -> Int -> Type -> Sort -> Sort
sortSubstitute dEnv subD ty = foldSortAlgN subD instAlg
  where instTypeArgs d ts = map (typeInsantiate d ty) ts
        instAlg = idSortAlg {
          sortPolyRegion = \d idx ts -> if idx == d
                                        then regionAssign'  dEnv (instTypeArgs d ts) $ typeWeaken d ty
                                        else SortPolyRegion (strengthenIdx d idx) (instTypeArgs d ts),
          sortPolySort   = \d idx ts -> if idx == d
                                        then sortAssign'  dEnv (instTypeArgs d ts) $ typeWeaken d ty
                                        else SortPolySort (strengthenIdx d idx) (instTypeArgs d ts) 
        }


----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------

type Depth = Int

-- | Re-index the debruin indices of a sort
sortReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
            -> Int -- ^ Depth in annotation
            -> Sort -> Sort
sortReIndex f annD = foldSortAlgN annD reIdxAlg
  where reIdxAlg = idSortAlg {
    sortPolyRegion = \d idx ts -> SortPolyRegion (f d idx) $ map (typeReindex $ f d) ts,
    sortPolySort   = \d idx ts -> SortPolySort   (f d idx) $ map (typeReindex $ f d) ts 
  }

-- | Decrease all unbound indexes by 1
sortStrengthen :: Sort -> Sort
sortStrengthen = sortReIndex strengthenIdx (-1)

-- | Increase all unbound indexes by n
sortWeaken :: Int -> Sort -> Sort
sortWeaken n = sortReIndex (weakenIdx n) (-1)

----------------------------------------------------------------
-- Sort utilities
----------------------------------------------------------------

{-| Evaluate if a sort is a region
For sort tuples we recurse into the first element.
A sort unit is never a region (can only occur in last element of SortTuple, which we do not check)
-}
sortIsRegion :: Sort -> Bool
sortIsRegion SortMonoRegion       = True
sortIsRegion (SortPolyRegion _ _) = True
sortIsRegion (SortUnit)           = False -- TODO: Edge case, it is and is not a region...
sortIsRegion (SortTuple as)       = sortIsRegion $ as !! 0
sortIsRegion _ = False

-- | Check if a sort is an annotation sort
sortIsAnnotation :: Sort -> Bool
sortIsAnnotation = not . sortIsRegion


-- | Unpack a tuple sort
sortUnpackTuple :: Sort -> [Sort]
sortUnpackTuple (SortTuple ss) = ss
sortUnpackTuple _ = rsError "sortUnpackTuple called on non-tuple"

-- | Safely index a tuple sort
indexSortTuple :: Int -> Sort -> Sort
indexSortTuple _   SortUnit       = SortUnit -- TODO: Also has to do with region tuples
indexSortTuple idx (SortTuple ts) = if idx < length ts
                                    then ts !! idx
                                    else rsError "indexSortTuple: Sort index out of bounds"
indexSortTuple _ s = s

-- | Drop a lambda for a sort
sortDropLam :: Sort -> Sort
sortDropLam (SortLam _ s) = s
sortDropLam s = s-- error $ "Called droplam on non-sortlam: " ++ show s


-- | Convert region variables to a sort
regionVarsToSort :: RegionVars -> Sort
regionVarsToSort (RegionVarsSingle _) = SortMonoRegion
regionVarsToSort (RegionVarsTuple rs) = SortTuple $ regionVarsToSort <$> rs
