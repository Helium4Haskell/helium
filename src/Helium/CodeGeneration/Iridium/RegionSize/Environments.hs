module Helium.CodeGeneration.Iridium.RegionSize.Environments
where

import Control.Monad.Reader

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

----------------------------------------------------------------
-- Type definitions
----------------------------------------------------------------

data GlobalEnv = GlobalEnv !(IdMap Type) !(IdMap (Annotation))
type BlockEnv  = IdMap (Annotation, Effect)
type LocalEnv  = IdMap Annotation
data Envs = Envs GlobalEnv LocalEnv
-- | The effect is an annotation, but always of sort C
type Effect = Annotation

type BlockMonad = Reader BlockEnv

----------------------------------------------------------------
-- Global environment
----------------------------------------------------------------

-- | Initial analysis environment, sets all functions to top
initialGEnv :: Module -> GlobalEnv
initialGEnv m = GlobalEnv synonyms functionEnv
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
    method (Declaration name _ _ _ (Method tp _ _ _ _ _)) = (name, top tp)

    -- Top of type
    top :: Type -> Annotation
    top _ = ATop -- . sortAssign . typeNormalize typeEnv

----------------------------------------------------------------
-- Block environment
----------------------------------------------------------------

-- | Look up a local variable in the local environment
lookupGlobal :: GlobalEnv -> Id -> Annotation
lookupGlobal (GlobalEnv _ vars) = flip findMap vars 

-- | Look up a local variable in the local environment
lookupBlock :: BlockEnv -> BlockName -> (Annotation, Effect)
lookupBlock = flip findMap

-- | Look up a local variable in the local environment
lookupLocal :: LocalEnv -> Local -> Annotation
lookupLocal lEnv local = case lookupMap (localName local) lEnv of
                            Nothing -> rsError $ "lookupLocal: ID not in map" 
                            Just a  -> a

-- | Lookup a global or local variable
lookupVar :: GlobalEnv -> LocalEnv -> Variable -> Annotation
lookupVar _ lEnv (VarLocal local) = lookupLocal  lEnv local
lookupVar gEnv _ global = lookupGlobal gEnv $ variableName global
lookupVar _ _ _ = error "Whut?"