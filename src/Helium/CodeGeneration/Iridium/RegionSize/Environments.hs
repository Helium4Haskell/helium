module Helium.CodeGeneration.Iridium.RegionSize.Environments
where

import qualified Data.Map as M

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes

import GHC.Stack

----------------------------------------------------------------
-- Type definitions
----------------------------------------------------------------

type GlobFuncEnv = (IdMap Annotation)

data DataTypeEnv = DataTypeEnv { 
  dtSorts     :: !(IdMap Sort),        -- ^ Datatype id -> sort
  dtStructs   :: !(IdMap Annotation),  -- ^ Constructor id -> constructor annotation
  dtDestructs :: !(IdMap [Annotation]) -- ^ Constructor id -> destructor annotation
}

data GlobalEnv   = GlobalEnv {
  globTypeEnv :: !TypeEnvironment,
  globFuncEnv :: !GlobFuncEnv,
  globDataEnv :: !DataTypeEnv
}

type RegionEnv   = M.Map RegionVar ConstrIdx

type BlockEnv    = IdMap Annotation

data LocalEnv    = LocalEnv { 
  lEnvLamCount :: Int,              -- ^ Number of lambdas wrapping the function body
  lEnvAnns     :: IdMap Annotation, -- ^ Map from local id to annotation
  lEnvSrts     :: IdMap Sort        -- ^ Map from local id to sort
}

data Envs = Envs GlobalEnv RegionEnv LocalEnv

----------------------------------------------------------------
-- Global environment
----------------------------------------------------------------

-- | Initial analysis environment, sets all functions to top
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
    functionEnv = mapFromList (abstracts)-- ++ dataTypeRecordFuncs)

    abstracts :: [(Id, Annotation)]
    abstracts = abstract <$> moduleAbstractMethods m
    abstract (Declaration name _ _ _ (AbstractMethod tp _ _ anns)) = (name, regionSizeAnn tp anns)

    regionSizeAnn :: Type -> [MethodAnnotation] -> Annotation
    regionSizeAnn _ (MethodAnnotateRegionSize a:_) = a
    regionSizeAnn tp (_:xs) = regionSizeAnn tp xs
    regionSizeAnn tp []     = top tp

    -- Top of type
    top :: Type -> Annotation
    top = flip ATop constrBot . sortAssign

    -- ~~~~~~~~~
    -- Datatypes
    -- ~~~~~~~~~
    -- Sorts
    dataTypeEnv :: DataTypeEnv
    dataTypeEnv = DataTypeEnv (mapFromList $ map declDataTypeSort $ moduleDataTypes m)
                              (mapFromList dataTypeConstructors)
                              (mapFromList dataTypeDestructors)

    declDataTypeSort :: Declaration DataType -> (Id, Sort)
    declDataTypeSort decl = (declarationName decl, dataTypeSort $ declarationValue decl)
    
    -- Record field functions (extract field by name)
    dataTypeRecordFuncs :: [(Id, Annotation)]
    dataTypeRecordFuncs = concat $ dataTypeRecordFuncs' <$> moduleDataTypes m
    
    dataTypeRecordFuncs' :: Declaration DataType -> [(Id, Annotation)]
    dataTypeRecordFuncs' dt = makeDataTypeRecordFields (declarationName dt `lookupDataType` dataTypeEnv) (declarationValue dt)
    
    -- Constructor annotations
    dataTypeConstructors :: [(Id, Annotation)]
    dataTypeConstructors = concat $ dataTypeConstructors' <$> moduleDataTypes m
    
    dataTypeConstructors' :: Declaration DataType -> [(Id, Annotation)]
    dataTypeConstructors' dt = makeDataTypeConstructors (declarationName dt `lookupDataType` dataTypeEnv) (declarationValue dt)
    
   -- Destructor annotations
    dataTypeDestructors :: [(Id, [Annotation])]
    dataTypeDestructors = concat $ dataTypeDestructors' <$> moduleDataTypes m
    
    dataTypeDestructors' :: Declaration DataType -> [(Id, [Annotation])]
    dataTypeDestructors' dt = makeDataTypeDestructors (declarationName dt `lookupDataType` dataTypeEnv) (declarationValue dt)

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
lookupLocalAnn local (LocalEnv _ lAnnEnv _) = 
  case lookupMap (localName local) lAnnEnv of
    Nothing -> rsError $ "lookupLocalAnn - ID not in map: " ++ (stringFromId $ localName local) 
    Just a  -> a

-- | Look up a local variable in the local environment
lookupLocalSrt :: HasCallStack => Local -> LocalEnv -> Sort
lookupLocalSrt local (LocalEnv _ _ lSrtEnv) = 
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

-- | Lookup a datatype in the datatype environment
lookupDataType :: HasCallStack => Id -> DataTypeEnv -> Sort
lookupDataType name dEnv = case lookupMap name (dtSorts dEnv) of
                              Nothing -> SortUnit -- TODO: Error?
                              Just ds -> ds

-- | Lookup a datatype constructor in the datatype environment
lookupStruct :: HasCallStack => Id -> DataTypeEnv -> Annotation
lookupStruct name dEnv = case lookupMap name (dtStructs dEnv) of
                              Nothing -> AUnit -- TODO: Error?
                              Just ds -> ds

-- | Lookup a datatype constructor in the datatype environment
lookupDestruct :: HasCallStack => Id -> DataTypeEnv -> [Annotation]
lookupDestruct name dEnv = case lookupMap name (dtDestructs dEnv) of
                              Nothing -> repeat AUnit -- TODO: Error?
                              Just ds -> ds


-- | Insert a function into the global environment
-- TODO: Get rid of the case
insertGlobal :: HasCallStack => Id -> Annotation -> GlobalEnv -> GlobalEnv
insertGlobal name ann (GlobalEnv syns fs ds) =
  case lookupMap name fs of
    Nothing -> GlobalEnv syns (insertMap name ann fs) ds  
    Just a  -> GlobalEnv syns (insertMap name (AJoin a ann) $ deleteMap name fs) ds

-- | Insert a local variable
insertLocal :: Id -> Annotation -> LocalEnv -> LocalEnv
insertLocal name ann (LocalEnv argC lAnnEnv lSrtEnv) = LocalEnv argC (insertMap name ann lAnnEnv) lSrtEnv

-- | Insert a local variable
updateLocal :: Id -> Annotation -> LocalEnv -> LocalEnv
updateLocal name ann (LocalEnv argC lAnnEnv lSrtEnv) = LocalEnv argC (updateMap name ann lAnnEnv) lSrtEnv

-- | Alter a value in the global map
updateGlobal :: HasCallStack => Id -> Annotation -> GlobalEnv -> GlobalEnv
updateGlobal name ann (GlobalEnv syns fs ds) = GlobalEnv syns (updateMap name ann fs) ds
