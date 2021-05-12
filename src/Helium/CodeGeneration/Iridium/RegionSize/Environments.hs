module Helium.CodeGeneration.Iridium.RegionSize.Environments
where

import qualified Data.Map as M

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Type

import GHC.Stack

----------------------------------------------------------------
-- Type definitions
----------------------------------------------------------------

type GlobFuncEnv = (IdMap Annotation)

data GlobalEnv   = GlobalEnv {
  globTypeEnv :: !TypeEnvironment,
  globFuncEnv :: !GlobFuncEnv,
  globDataEnv :: !DataTypeEnv
}

type RegionEnv   = M.Map RegionVar ConstrIdx

type BlockEnv    = IdMap Annotation

data LocalEnv    = LocalEnv { 
  lEnvAnns     :: IdMap Annotation, -- ^ Map from local id to annotation
  lEnvSrts     :: IdMap Sort        -- ^ Map from local id to sort
}

data Envs = Envs GlobalEnv RegionEnv LocalEnv

----------------------------------------------------------------
-- Data type sort discovery
----------------------------------------------------------------

-- | Find sort for datatype
dataTypeSort :: TypeEnvironment -> DataTypeEnv -> DataType -> Sort
dataTypeSort tEnv dEnv dt@(DataType structs) = foldr (const SortQuant) (SortTuple . concat $ dataStructSort tEnv dEnv <$> structs) (dataTypeQuantors dt)

dataStructSort :: TypeEnvironment -> DataTypeEnv -> Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructSort tEnv dEnv (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction $ typeRemoveQuants ty
  in sortAssign dEnv <$> typeNormalize tEnv <$> args

----------------------------------------------------------------
-- Global environment
----------------------------------------------------------------

-- | Initial analysis environment
initialGEnv :: Module -> GlobalEnv
initialGEnv m = GlobalEnv typeEnv functionEnv dataTypeEnv
  where
    -- Environment is only used for type synonyms
    typeEnv = TypeEnvironment synonyms emptyMap emptyMap

    -- Type synonims
    synonyms :: IdMap Type
    synonyms = mapFromList [(name, tp) | Declaration name _ _ _ (TypeSynonym _ tp) <- moduleTypeSynonyms m]

    -- Functions
    functionEnv :: IdMap Annotation
    functionEnv = mapFromList abstracts

    abstracts :: [(Id, Annotation)]
    abstracts = abstract <$> moduleAbstractMethods m
    abstract (Declaration name _ _ _ (AbstractMethod tp _ _ anns)) = (name, regionSizeAnn tp anns)

    regionSizeAnn :: Type -> [MethodAnnotation] -> Annotation
    regionSizeAnn _ (MethodAnnotateRegionSize a:_) = a
    regionSizeAnn tp (_:xs) = regionSizeAnn tp xs
    regionSizeAnn tp []     = top tp

    -- Top of type
    top :: Type -> Annotation
    top = flip ATop constrBot . SortLam SortUnit . sortAssign dataTypeEnv . typeNormalize typeEnv

    -- ~~~~~~~~~
    -- Datatypes
    -- ~~~~~~~~~

    dataTypeEnv :: DataTypeEnv
    dataTypeEnv = DataTypeEnv declDataTypeSorts dataTypeConstructors dataTypeDestructors

    -- Data type sorts
    declDataTypeSorts :: IdMap Sort
    declDataTypeSorts = mapFromList . concat $ map declDataTypeSorts' (dataTypeBindingGroups $ moduleDataTypes m)

    declDataTypeSorts' :: BindingGroup DataType -> [(Id, Sort)]
    declDataTypeSorts' (BindingNonRecursive decl) = [(declarationName decl, dataTypeSort typeEnv recDEnv $ declarationValue decl)]
    declDataTypeSorts' (BindingRecursive decls) = concat $ declDataTypeSorts' <$> BindingNonRecursive <$> decls

    -- Constructor annotations
    dataTypeConstructors :: IdMap Annotation
    dataTypeConstructors = mapFromList (concat $ dataTypeConstructors' <$> moduleDataTypes m)
    
    dataTypeConstructors' :: Declaration DataType -> [(Id, Annotation)]
    dataTypeConstructors' dt = makeDataTypeConstructors (declarationName dt `findMap` declDataTypeSorts) (declarationValue dt)
    
    -- Destructor annotations
    dataTypeDestructors :: IdMap [Annotation]
    dataTypeDestructors = mapFromList $ concat $ dataTypeDestructors' <$> moduleDataTypes m
    
    dataTypeDestructors' :: Declaration DataType -> [(Id, [Annotation])]
    dataTypeDestructors' dt = makeDataTypeDestructors (declarationName dt `findMap` declDataTypeSorts) (declarationValue dt)


    -- Environment used for the recursive positions of data types
    recDEnv :: DataTypeEnv
    recDEnv = DataTypeEnv (mapFromList (map makeRecDataTypeSort $ moduleDataTypes m)) emptyMap emptyMap

    makeRecDataTypeSort ::  Declaration DataType -> (Id, Sort)
    makeRecDataTypeSort decl = (declarationName decl, foldr (const SortQuant) SortUnit . dataTypeQuantors $ declarationValue decl)

----------------------------------------------------------------
-- Environment interface functions
----------------------------------------------------------------

-- | Look up a local variable in the local environment
lookupGlobal :: HasCallStack => Id -> GlobalEnv -> Annotation
lookupGlobal name (GlobalEnv _ vars _) = 
  case lookupMap name vars of
    Nothing -> rsError $ "lookupGlobal - Global environment did not contain: " ++ stringFromId name
    Just a  -> a 

-- | Look up a local variable in the local environment
lookupBlock :: BlockName -> BlockEnv -> Annotation
lookupBlock name bEnv = 
  case lookupMap name bEnv of
    Nothing -> rsError $ "lookupBlock -Block variable missing: " ++ stringFromId name
    Just a  -> a 

-- | Look up a local variable in the local environment
lookupLocalAnn :: HasCallStack => Local -> LocalEnv -> Annotation
lookupLocalAnn local (LocalEnv lAnnEnv _) = 
  case lookupMap (localName local) lAnnEnv of
    Nothing -> rsError $ "lookupLocalAnn - ID not in map: " ++ (stringFromId $ localName local) 
    Just a  -> a

-- | Look up a local variable in the local environment
lookupLocalSrt :: HasCallStack => Local -> LocalEnv -> Sort
lookupLocalSrt local (LocalEnv _ lSrtEnv) = 
  case lookupMap (localName local) lSrtEnv of
    Nothing -> rsError $ "lookupLocalAnn - ID not in map: " ++ (stringFromId $ localName local) 
    Just a  -> a

-- | Lookup a global or local variable
lookupVar :: HasCallStack => Variable -> Envs -> Annotation
lookupVar (VarLocal local) (Envs _ _ lEnv) = lookupLocalAnn local lEnv
lookupVar global           (Envs gEnv _ _) = AApl (lookupGlobal (variableName global) gEnv) AUnit

-- | Lookup a region in the region environment, retuns the region if not in env
lookupReg :: HasCallStack => RegionVar -> RegionEnv -> ConstrIdx
lookupReg r rEnv = case M.lookup r rEnv of
                      Nothing -> Region r
                      Just ci -> ci

-- | Insert a function into the global environment
insertGlobal :: HasCallStack => Id -> Annotation -> GlobalEnv -> GlobalEnv
insertGlobal name ann (GlobalEnv syns fs ds) =
  case lookupMap name fs of
    Nothing -> GlobalEnv syns (insertMap name ann fs) ds  
    Just a  -> rsError $ "insertGlobal - Value already present: " ++ show name

-- | Insert a local variable
insertLocal :: Id -> Annotation -> LocalEnv -> LocalEnv
insertLocal name ann (LocalEnv lAnnEnv lSrtEnv) = LocalEnv (insertMap name ann lAnnEnv) lSrtEnv

-- | Insert a local variable
updateLocal :: Id -> Annotation -> LocalEnv -> LocalEnv
updateLocal name ann (LocalEnv lAnnEnv lSrtEnv) = LocalEnv (updateMap name ann lAnnEnv) lSrtEnv

-- | Alter a value in the global map
updateGlobal :: HasCallStack => Id -> Annotation -> GlobalEnv -> GlobalEnv
updateGlobal name ann (GlobalEnv syns fs ds) = GlobalEnv syns (updateMap name ann fs) ds
