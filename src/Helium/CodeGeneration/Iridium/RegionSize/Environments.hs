module Helium.CodeGeneration.Iridium.RegionSize.Environments
where

import qualified Data.Map as M

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Sort

import GHC.Stack

----------------------------------------------------------------
-- Type definitions
----------------------------------------------------------------

data GlobalEnv = GlobalEnv !(IdMap Type) !(IdMap (Annotation))
type RegionEnv = M.Map RegionVar ConstrIdx
type BlockEnv  = IdMap Annotation
type LocalEnv  = IdMap Annotation
data Envs = Envs GlobalEnv RegionEnv LocalEnv

-- | The effect is an annotation, but always of sort C
type Effect = Annotation

----------------------------------------------------------------
-- Global environment
----------------------------------------------------------------

-- | Initial analysis environment, sets all functions to top
initialGEnv :: Module -> GlobalEnv
initialGEnv m = GlobalEnv synonyms emptyMap--functionEnv
  where
    -- Type synonims
    synonyms :: IdMap Type
    synonyms = mapFromList [(name, tp) | Declaration name _ _ _ (TypeSynonym _ tp) <- moduleTypeSynonyms m]

    -- Functions
    functionEnv :: IdMap Annotation
    functionEnv = mapFromList $ methods ++ abstracts

    abstracts :: [(Id, Annotation)]
    abstracts = abstract <$> moduleAbstractMethods m
    abstract (Declaration name _ _ _ (AbstractMethod tp _ _)) = (name, top tp)

    methods :: [(Id, Annotation)]
    methods = method <$> moduleMethods m
    method (Declaration name _ _ _ (Method tp _ _ _ _ _ _ _)) = (name, top tp)

    -- Top of type
    top :: Type -> Annotation
    top = ATop . sortAssign

----------------------------------------------------------------
-- Block environment
----------------------------------------------------------------

-- | Look up a local variable in the local environment
lookupGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation
lookupGlobal (GlobalEnv _ vars) id = 
  case lookupMap id vars of
    Nothing -> rsError $ "Global environment did not contain: " ++ stringFromId id
    Just a  -> a 

-- | Insert a function into the global environment
insertGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation -> GlobalEnv
insertGlobal (GlobalEnv syns fs) id ann =
  case lookupMap id fs of
    Nothing -> GlobalEnv syns $ insertMap id ann fs 
    Just a  -> GlobalEnv syns $ insertMap id (AJoin a ann) $ deleteMap id fs 


-- | Look up a local variable in the local environment
lookupBlock :: BlockEnv -> BlockName -> Annotation
lookupBlock bEnv id = 
  case lookupMap id bEnv of
    Nothing -> rsError $ "Recursive block definition: " ++ stringFromId id
    Just a  -> a 

-- | Look up a local variable in the local environment
lookupLocal :: HasCallStack => LocalEnv -> Local -> Annotation
lookupLocal lEnv local = case lookupMap (localName local) lEnv of
                            Nothing -> rsError $ "lookupLocal - ID not in map: " ++ (stringFromId $ localName local) 
                            Just a  -> a

-- | Lookup a global or local variable
lookupVar :: HasCallStack => Envs -> Variable -> Annotation
lookupVar (Envs _ _ lEnv) (VarLocal local) = lookupLocal  lEnv local
lookupVar (Envs gEnv _ _) global           = lookupGlobal gEnv $ variableName global


-- | Lookup a region in the region environment, retuns the region if not in env
lookupReg :: HasCallStack => RegionEnv -> RegionVar -> ConstrIdx
lookupReg rEnv r = case M.lookup r rEnv of
                      Nothing -> Region r
                      Just ci -> ci


-- | Alter a value in the global map
updateGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation -> GlobalEnv
updateGlobal (GlobalEnv syns fs) id ann = GlobalEnv syns $ updateMap id ann fs
