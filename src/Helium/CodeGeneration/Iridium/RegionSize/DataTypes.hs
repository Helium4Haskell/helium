module Helium.CodeGeneration.Iridium.RegionSize.DataTypes
where

import Lvm.Common.Id
import Lvm.Core.Type
import qualified Lvm.Core.Module as LVMModule

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort

import Data.Either (lefts)

----------------------------------------------------------------
-- Data type sort discovery
----------------------------------------------------------------

-- | Find sort for datatype
dataTypeSort :: DataType -> Sort
dataTypeSort (DataType structs) = SortTuple . concat $ dataStructSort <$> structs

dataStructSort :: Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructSort (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction ty
  in sortAssign <$> args

----------------------------------------------------------------
-- Data types to annotations
----------------------------------------------------------------

-- | Make destructor annotations for record datatypes
-- TODO: Fill in data type sort
makeDataTypeRecordFields :: Sort -> DataType -> [(Id, Annotation)]
makeDataTypeRecordFields dts (DataType structs) = 
    mapWithIndex makeRecordField (concat $ constrRecordFields <$> structs)
  where makeRecordField idx field = (field, ALam dts . AProj idx $ AVar 0)   

        constrRecordFields :: Declaration DataTypeConstructorDeclaration -> [Id]
        constrRecordFields (Declaration _ _ _ _ (DataTypeConstructorDeclaration _ fields)) = 
            LVMModule.fieldName <$> fields


-- | Make constructor annotations
makeDataTypeConstructors :: Sort -> DataType -> [(Id, Annotation)]
makeDataTypeConstructors dtSort (DataType structs) = 
    snd $ foldl makeStructorAnn (0,[]) structs
  where dtTupSize = sum $ structorSize <$> structs
        SortTuple dtSorts = dtSort
        
        makeStructorAnn :: (Int, [(Id,Annotation)])
                        -> Declaration DataTypeConstructorDeclaration  
                        -> (Int, [(Id,Annotation)])
        makeStructorAnn (start, stctsAnns) strctDecl =
          let size = structorSize strctDecl
              -- Tuple elements
              pre  = (\i -> ABot $ dtSorts !! i) <$> [0          .. start    -1]
              post = (\i -> ABot $ dtSorts !! i) <$> [start+size .. dtTupSize-1]  
              args = reverse $ (\i -> AVar i)    <$> [0          .. size     -1]
              -- Constructor tuple
              strctTup = ATuple (pre ++ args ++ post)
              -- Wrap with lambdas (TODO: Check if order is correct)
              strctLam = foldr (\i -> ALam (dtSorts !! i)) strctTup [start .. start+size-1]
              -- Wrap with quantifications
              strctAnn = annNQuants (stuctorQuants strctDecl) strctLam
          in (start+size, (declarationName strctDecl, strctAnn):stctsAnns)

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
structorSize (Declaration _ _ _ _ (DataTypeConstructorDeclaration _ fs)) = length fs

stuctorQuants :: Declaration DataTypeConstructorDeclaration -> Int
stuctorQuants (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) = 
    let (FunctionType args _) = extractFunctionTypeNoSynonyms ty 
    in length $ lefts args