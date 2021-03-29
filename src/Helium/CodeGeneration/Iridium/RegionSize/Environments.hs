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

import GHC.Stack

----------------------------------------------------------------
-- Type definitions
----------------------------------------------------------------

data GlobalEnv = GlobalEnv !TypeEnvironment !(IdMap (Annotation))
type RegionEnv = M.Map RegionVar ConstrIdx
type BlockEnv  = IdMap Annotation
type LocalEnv  = IdMap Annotation
data Envs = Envs GlobalEnv RegionEnv LocalEnv

----------------------------------------------------------------
-- Global environment
----------------------------------------------------------------

-- | Initial analysis environment, sets all functions to top
initialGEnv :: Module -> GlobalEnv
initialGEnv m = GlobalEnv typeEnv functionEnv
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
    top = flip ATop constrBot . sortAssign

----------------------------------------------------------------
-- Block environment
----------------------------------------------------------------

-- | Look up a local variable in the local environment
lookupGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation
lookupGlobal (GlobalEnv _ vars) name = 
  case lookupMap name vars of
    Nothing -> rsError $ "lookupGlobal - Global environment did not contain: " ++ stringFromId name
    Just a  -> a 

-- | Insert a function into the global environment
insertGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation -> GlobalEnv
insertGlobal (GlobalEnv syns fs) name ann =
  case lookupMap name fs of
    Nothing -> GlobalEnv syns $ insertMap name ann fs 
    Just a  -> GlobalEnv syns $ insertMap name (AJoin a ann) $ deleteMap name fs 


-- | Look up a local variable in the local environment
lookupBlock :: BlockEnv -> BlockName -> Annotation
lookupBlock bEnv name = 
  case lookupMap name bEnv of
    Nothing -> rsError $ "lookupBlock -Block variable missing: " ++ stringFromId name
    Just a  -> a 

-- | Look up a local variable in the local environment
lookupLocal :: HasCallStack => LocalEnv -> Local -> Annotation
lookupLocal lEnv local = case lookupMap (localName local) lEnv of
                            Nothing -> rsError $ "lookupLocal - ID not in map: " ++ (stringFromId $ localName local) 
                            Just a  -> a

-- | Lookup a global or local variable
lookupVar :: HasCallStack => Envs -> Variable -> Annotation
lookupVar (Envs _ _ lEnv) (VarLocal local) = lookupLocal lEnv local
lookupVar (Envs gEnv _ _) global           = lookupGlobal gEnv $ variableName global


-- | Lookup a region in the region environment, retuns the region if not in env
lookupReg :: HasCallStack => RegionEnv -> RegionVar -> ConstrIdx
lookupReg rEnv r = case M.lookup r rEnv of
                      Nothing -> Region r
                      Just ci -> ci


-- | Alter a value in the global map
updateGlobal :: HasCallStack => GlobalEnv -> Id -> Annotation -> GlobalEnv
updateGlobal (GlobalEnv syns fs) name ann = GlobalEnv syns $ updateMap name ann fs
