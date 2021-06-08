module Helium.CodeGeneration.Iridium.RegionSize.SortUtils
    (sortAssign, regionAssign,
    dataTypeSort, dataTypeRegions,
    sortInstantiate, sortSubstitute, 
    sortReIndex, sortWeaken,
    sortIsRegion, sortDropLam,
    regionVarsToSort,
    methodSortAssign) where

import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort

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
sortAssign' dEnv ts (TStrict t)     = sortAssign' dEnv ts t
sortAssign' _    ts (TVar idx)        = SortPolySort idx ts
sortAssign' dEnv ts (TAp t1 t2)     = sortAssign' dEnv (t2:ts) t1
sortAssign' dEnv []      (TForall _ _ t1) = SortQuant $ sortAssign' dEnv [] t1
sortAssign' dEnv (t2:ts) (TForall _ _ t1) = sortAssign' dEnv ts (typeSubstitute 0 t2 t1)
-- Type constructors (functions, tuples, simple data types)
sortAssign' dEnv [t1,t2] (TCon TConFun)       = funSort dEnv t1 t2  
sortAssign' dEnv ts      (TCon (TConTuple n)) | length ts == n = SortTuple $ map (sortAssign dEnv) ts
                                              | otherwise      = rsError $ "sortAssign: Tuple with incorrect number of arguements: expected " ++ show n 
                                                                        ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
sortAssign' dEnv ts      (TCon (TConTypeClassDictionary name)) = foldl (flip $ sortInstantiate dEnv) (dictionaryDataTypeName name `lookupDataType` dEnv) ts
sortAssign' dEnv ts      (TCon (TConDataType            name)) = foldl (flip $ sortInstantiate dEnv) (name `lookupDataType` dEnv) ts
sortAssign' _ ts t = rsError $ "sortAssign' - No pattern match: " ++ showType varNames t ++ "\n" ++ show (showType varNames <$> ts)

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
regionAssign' _    ts (TVar a)        = SortPolyRegion a ts
regionAssign' dEnv ts (TStrict a)     = regionAssign' dEnv ts a
regionAssign' dEnv ts (TAp t1 t2)     = regionAssign' dEnv (t2:ts) t1
regionAssign' dEnv []      (TForall _ _ t1) = SortQuant $ regionAssign' dEnv [] t1
regionAssign' dEnv (t2:ts) (TForall _ _ t1) = regionAssign' dEnv ts (typeSubstitute 0 t2 t1)
-- Type constructors (functions, tuples, simple data types)
regionAssign' _    [_,_] (TCon TConFun      ) = SortUnit
regionAssign' dEnv ts    (TCon (TConTuple n)) | length ts == n = SortTuple . concat $ sortUnpackTuple.regionAssign dEnv <$> ts
                                              | otherwise      = rsError $ "regionAssign: Tuple with incorrect number of arguements: expected " ++ show n ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
-- Data types & dictionaries
regionAssign' dEnv ts    (TCon (TConTypeClassDictionary name)) = foldl (flip $ sortInstantiate dEnv) (dictionaryDataTypeName name `lookupDataTypeRegs` dEnv) ts
regionAssign' dEnv ts    (TCon (TConDataType            name)) = foldl (flip $ sortInstantiate dEnv) (name `lookupDataTypeRegs` dEnv) ts
-- Not implemented cases
regionAssign' _    ts t = rsError $ "regionAssign: No pattern match: " ++ showTypeN 0 t 
                                  ++ "\nArguments: " ++ (intercalate ", " $ map (showTypeN 0) ts)

----------------------------------------------------------------
-- Data type sort discovery
----------------------------------------------------------------

-- | Find sort for datatype
dataTypeSort :: TypeEnvironment -> DataTypeEnv -> DataType -> Sort
dataTypeSort tEnv dEnv dt@(DataType structs) = foldr (const SortQuant) (SortTuple . concat $ dataStructSort tEnv dEnv <$> structs) (dataTypeQuantors dt)

dataStructSort :: TypeEnvironment -> DataTypeEnv -> Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructSort tEnv dEnv (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction $ typeRemoveQuants ty 
  in sortAssign dEnv . typeNormalize tEnv <$> args

-- | Find region assignment for datatype
dataTypeRegions :: TypeEnvironment -> DataTypeEnv -> DataType -> Sort
dataTypeRegions tEnv dEnv dt@(DataType structs) = foldr (const SortQuant) (SortTuple . concat $ dataStructRegions tEnv dEnv <$> structs) (dataTypeQuantors dt)

dataStructRegions :: TypeEnvironment -> DataTypeEnv -> Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructRegions tEnv dEnv (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction $ typeRemoveQuants ty 
  in regionAssign dEnv . typeNormalize tEnv <$> args

----------------------------------------------------------------
-- Mutually recursive data types
----------------------------------------------------------------

-- IDEA: Keeping expanding the datatype definition until we have seen all datatypes in de mutually recusive cluster once
-- solveMutRecDataTypes :: DataTypeEnv -> [Id] -> [DataType] -> [(Id, Sort)]
-- solveMutRecDataTypes dEnv names dataTypes = go names (mapFromList (zip ids dataTypes)) <$> dataTypes
--   where goDT rem dict (DataType structs)                    = goST rem dict . declarationValue <$> structs 
--         goST rem dict (DataTypeConstructorDeclaration ty _) =     
--           let (args, _) = typeExtractFunction $ typeRemoveQuants ty
--           in goTY <$> typeNormalize tEnv <$> args
--         goTY rem dict ty

----------------------------------------------------------------
-- Type substitution
----------------------------------------------------------------

-- | Instatiate a type argument, sort should start wit SortQuant
sortInstantiate :: DataTypeEnv -> Type -> Sort -> Sort
sortInstantiate dEnv t (SortQuant s) = sortSubstitute dEnv 0 t s
sortInstantiate _    _ s = rsError $ "Tried to instantiate a sort that does not start with SortQuant\nSort:" ++ show s

-- | Instatiate a quantified type in a sort
sortSubstitute :: DataTypeEnv -> Int -> Type -> Sort -> Sort
sortSubstitute dEnv subD ty = foldSortAlgN subD instAlg
  where instTypeArgs d ts = typeSubstitute d (typeWeaken d ty) <$> ts
        instAlg = idSortAlg {
          sortPolyRegion = \qD idx ts -> if idx == qD
                                         then regionAssign' dEnv (instTypeArgs qD ts) $ typeWeaken qD ty
                                         else SortPolyRegion (strengthenIdx qD idx) (instTypeArgs qD ts),
          sortPolySort   = \qD idx ts -> if idx == qD
                                         then sortAssign' dEnv (instTypeArgs qD ts) $ typeWeaken qD ty
                                         else SortPolySort (strengthenIdx qD idx) (instTypeArgs qD ts) 
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

-- | Unpack a tuple sort
sortUnpackTuple :: Sort -> [Sort]
sortUnpackTuple (SortTuple ss) = ss
sortUnpackTuple _ = rsError "sortUnpackTuple called on non-tuple"

-- | Drop a lambda for a sort
sortDropLam :: Sort -> Sort
sortDropLam (SortLam _ s) = s
sortDropLam s = error $ "Called droplam on non-sortlam: " ++ show s

-- | Convert region variables to a sort
regionVarsToSort :: RegionVars -> Sort
regionVarsToSort (RegionVarsSingle _) = SortMonoRegion
regionVarsToSort (RegionVarsTuple rs) = SortTuple $ regionVarsToSort <$> rs

-- | Assign a sort to a method  
methodSortAssign :: TypeEnvironment -> DataTypeEnv -> Method -> Sort  
methodSortAssign tEnv dEnv = SortLam SortUnit . sortAssign dEnv . typeNormalize tEnv . methodType   