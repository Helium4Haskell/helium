module Helium.CodeGeneration.Iridium.RegionSize.DataTypes
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type
import qualified Lvm.Core.Module as LVMModule

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Type

import GHC.Stack

import Data.Either (lefts, rights)

----------------------------------------------------------------
-- Data type environment
----------------------------------------------------------------

data DataTypeEnv = DataTypeEnv { 
  dtSorts     :: !(IdMap Sort),        -- ^ Datatype id -> sort, sort assignment
  dtRegions   :: !(IdMap Sort),        -- ^ Datatype id -> sort, region assignment
  dtStructs   :: !(IdMap Annotation),  -- ^ Constructor id -> constructor annotation
  dtDestructs :: !(IdMap [Annotation]) -- ^ Constructor id -> destructor annotation
}

emptyDEnv :: DataTypeEnv
emptyDEnv = DataTypeEnv emptyMap emptyMap emptyMap emptyMap

----------------------------------------------------------------
-- Data types lookup functions
----------------------------------------------------------------

-- | Lookup a datatype in the datatype environment
lookupDataType :: HasCallStack => Id -> DataTypeEnv -> Sort
lookupDataType name dEnv = case lookupMap name (dtSorts dEnv) of
                              Nothing -> rsError $ "lookupDataType: Datatype not in environment: " ++ show name
                              Just ds -> ds

-- | Lookup a datatype in the datatype environment
lookupDataTypeRegs :: HasCallStack => Id -> DataTypeEnv -> Sort
lookupDataTypeRegs name dEnv = case lookupMap name (dtRegions dEnv) of
                                 Nothing -> rsError $ "lookupDataType: Datatype not in environment: " ++ show name
                                 Just ds -> ds

-- | Lookup a datatype constructor in the datatype environment
lookupStruct :: HasCallStack => Id -> DataTypeEnv -> Annotation
lookupStruct name dEnv = case lookupMap name (dtStructs dEnv) of
                              Nothing -> rsError $ "lookupStruct: Datatype not in environment: " ++ show name
                              Just ds -> ds

-- | Lookup a datatype constructor in the datatype environment
lookupDestruct :: HasCallStack => Id -> DataTypeEnv -> [Annotation]
lookupDestruct name dEnv = case lookupMap name (dtDestructs dEnv) of
                              Nothing -> rsError $ "lookupDestruct: Datatype not in environment: " ++ show name
                              Just ds -> ds

----------------------------------------------------------------
-- Data types to annotations
----------------------------------------------------------------

-- | Make destructor annotations for record datatypes
makeDataTypeRecordFields :: Sort -> DataType -> [(Id, Annotation)]
makeDataTypeRecordFields dts (DataType structs) = 
    mapWithIndex makeRecordField (concat $ constrRecordFields <$> structs)
  where makeRecordField idx field = (field, ALam dts . AProj idx $ AVar 0)   

        constrRecordFields :: Declaration DataTypeConstructorDeclaration -> [Id]
        constrRecordFields (Declaration _ _ _ _ (DataTypeConstructorDeclaration _ fields)) = 
            LVMModule.fieldName <$> fields


-- | Make constructor annotations
makeDataTypeConstructors :: Sort -> DataType -> [(Id, Annotation)]
makeDataTypeConstructors dtSort dt@(DataType structs) = 
    snd $ foldl makeStructorAnn (0,[]) structs
  where dtTupSize = sum $ structorSize <$> structs
        SortTuple dtSorts = removeSortQuants dtSort
        
        makeStructorAnn :: (Int, [(Id,Annotation)])
                        -> Declaration DataTypeConstructorDeclaration  
                        -> (Int, [(Id,Annotation)])
        makeStructorAnn (start, stctsAnns) strctDecl =
          let size = structorSize strctDecl
              -- Tuple elements
              pre  = (\i -> ABot $ dtSorts !! i) <$> [0          .. start    -1]
              args = reverse $ (\i -> AVar i)    <$> [0          .. size     -1]
              post = (\i -> ABot $ dtSorts !! i) <$> [start+size .. dtTupSize-1]  
              -- Constructor tuple
              strctTup = ATuple (pre ++ args ++ post)
              -- Wrap with lambdas (TODO: Check if order is correct)
              strctLam = foldr (\i -> ALam (dtSorts !! i)) strctTup [start .. start+size-1]
              -- Wrap with quantifications
              strctAnn = foldr (const AQuant) strctLam (dataTypeQuantors dt)
          in (start+size, (declarationName strctDecl, strctAnn):stctsAnns)

-- | Remove sort quantifications
removeSortQuants :: Sort -> Sort
removeSortQuants (SortQuant s) = removeSortQuants s
removeSortQuants s = s

-- | Make destructor annotations
makeDataTypeDestructors :: Sort -> DataType -> [(Id, [Annotation])]
makeDataTypeDestructors dtSort (DataType structs) =
    snd $ foldl makeDestructorAnn (0,[]) structs
  where 
    makeDestructorAnn :: (Int, [(Id,[Annotation])])
                        -> Declaration DataTypeConstructorDeclaration  
                        -> (Int, [(Id,[Annotation])])
    makeDestructorAnn (start, stctsAnns) strctDecl =
        let size = structorSize strctDecl
            -- Project on elements of constructor
            destrctAnn = map (\i -> ALam dtSort $ AProj i (AVar 0)) [start .. start+size-1]  
        in (start+size, (declarationName strctDecl, destrctAnn):stctsAnns)

----------------------------------------------------------------
-- Data type utilitiy functions
----------------------------------------------------------------

structorSize :: Declaration DataTypeConstructorDeclaration -> Int
structorSize (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
    let (FunctionType args _) = extractFunctionTypeNoSynonyms ty 
    in length $ rights args
