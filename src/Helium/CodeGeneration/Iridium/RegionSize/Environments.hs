module Helium.CodeGeneration.Iridium.RegionSize.Environments
where

import qualified Data.Map.Strict as M

import Lvm.Common.Id
import Lvm.Common.IdMap

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

data Envs = Envs !GlobalEnv !RegionEnv !LocalEnv

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
    Just _  -> rsError $ "insertGlobal - Value already present: " ++ show name

-- | Insert a local variable
insertLocal :: Id -> Annotation -> LocalEnv -> LocalEnv
insertLocal name ann (LocalEnv lAnnEnv lSrtEnv) = LocalEnv (insertMap name ann lAnnEnv) lSrtEnv

-- | Insert a local variable
updateLocal :: Id -> Annotation -> LocalEnv -> LocalEnv 
updateLocal name ann (LocalEnv lAnnEnv lSrtEnv) = LocalEnv (updateMap name ann lAnnEnv) lSrtEnv

-- | Alter a value in the global map
updateGlobal :: HasCallStack => Id -> Annotation -> GlobalEnv -> GlobalEnv
updateGlobal name ann (GlobalEnv syns fs ds) = GlobalEnv syns (updateMap name ann fs) ds
