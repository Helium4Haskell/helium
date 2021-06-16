module Helium.CodeGeneration.Iridium.RegionSize.DataTypes
where

import Lvm.Common.Id
import Lvm.Common.IdMap

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort

import GHC.Stack

import Data.Either (rights)

----------------------------------------------------------------
-- Data type environment
----------------------------------------------------------------

data DataTypeEnv = DataTypeEnv { 
  dtSorts     :: !(IdMap (Maybe Sort)),        -- ^ Datatype id -> sort, sort assignment
  dtRegions   :: !(IdMap (Maybe Sort)),        -- ^ Datatype id -> sort, region assignment
  dtStructs   :: !(IdMap Annotation),          -- ^ Constructor id -> constructor annotation
  dtDestructs :: !(IdMap [Annotation])         -- ^ Constructor id -> destructor annotation
}

emptyDEnv :: DataTypeEnv
emptyDEnv = DataTypeEnv emptyMap emptyMap emptyMap emptyMap

---------------------------------------------------------------
-- Data types lookup functions
----------------------------------------------------------------

-- | Lookup a datatype in the datatype environment
lookupDataType :: HasCallStack => Id -> DataTypeEnv -> Maybe Sort
lookupDataType name dEnv = case lookupMap name (dtSorts dEnv) of
                              Nothing -> rsError $ "lookupDataType: Datatype not in environment: " ++ show name
                              Just ds -> ds

-- | Lookup a datatype in the datatype environment
lookupDataTypeRegs :: HasCallStack => Id -> DataTypeEnv -> Maybe Sort
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

-- | Make constructor annotations
makeDataTypeConstructors :: Maybe Sort -> DataType -> [(Id, Annotation)]
makeDataTypeConstructors Nothing (DataType _) = [] 
makeDataTypeConstructors (Just dtSort) dt@(DataType structs) = mapWithIndex makeStructorAnn structs
  where dtTupSize = length structs
        SortTuple dtSrts = sortRemoveQuants dtSort
        
        makeStructorAnn :: Int -> Declaration DataTypeConstructorDeclaration -> (Id,Annotation)
        makeStructorAnn structIdx strctDecl =
          let size = structorSize strctDecl
              SortTuple structSrt = dtSrts !! structIdx
              -- Tuple elements
              pre  = (\i -> ABot $ dtSrts !! i)        <$> [0          ..structIdx-1]
              args = ATuple . reverse $ (\i -> AVar i) <$> [0          ..size     -1]
              post = (\i -> ABot $ dtSrts !! i)        <$> [structIdx+1..dtTupSize-1]  
              -- Constructor tuple
              strctTup = ATuple (pre ++ [args] ++ post)
              -- Wrap with lambdas
              strctLam = foldr (\i -> ALam (structSrt !! i)) strctTup [0 .. size-1]
              -- Wrap with quantifications
              strctAnn = wrapDataTypeQuants dt strctLam
          in (declarationName strctDecl, strctAnn)

-- | Remove sort quantifications
sortRemoveQuants :: Sort -> Sort
sortRemoveQuants (SortQuant s) = sortRemoveQuants s
sortRemoveQuants s = s


-- | Make destructor annotations
makeDataTypeDestructors :: Maybe Sort -> DataType -> [(Id, [Annotation])]
makeDataTypeDestructors Nothing (DataType _) = [] 
makeDataTypeDestructors (Just dtSort) dt@(DataType structs) =
    mapWithIndex makeDestructorAnn structs
  where 
    dtSort' = sortRemoveQuants dtSort

    makeDestructorAnn :: Int -> Declaration DataTypeConstructorDeclaration -> (Id,[Annotation])
    makeDestructorAnn idx strctDecl =
        let size = structorSize strctDecl
            -- Project on elements of constructor
            destrctAnn = (\i -> ALam dtSort' . AProj i . AProj idx $ AVar 0) <$> [0 .. size-1]  
            destrctQnt = wrapDataTypeQuants dt <$> destrctAnn
        in (declarationName strctDecl, destrctQnt)

----------------------------------------------------------------
-- Data type utilitiy functions
----------------------------------------------------------------

structorSize :: Declaration DataTypeConstructorDeclaration -> Int
structorSize (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
    let (FunctionType args _) = extractFunctionTypeNoSynonyms ty 
    in length $ rights args

-- | Wrap an annotation in the quantifications for the corresponding datatype
wrapDataTypeQuants :: DataType -> Annotation -> Annotation 
wrapDataTypeQuants dt strctLam = foldr (const AQuant) strctLam (dataTypeQuantors dt)