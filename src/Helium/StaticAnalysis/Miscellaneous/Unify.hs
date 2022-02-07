{-# LANGUAGE DeriveFunctor #-}

module Helium.StaticAnalysis.Miscellaneous.Unify where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (
    MonoType (MonoType_Con, MonoType_Var, MonoType_App, MonoType_Fam),
    TyVar,
    fvToList, MonoTypes
    )

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Control.Monad (ap)
import Debug.Trace


type InjectiveEnv = Map String [Int]
type SubstitutionEnv = Map TyVar MonoType

data UnifyOptions = UO {
  injChecking :: Bool,
  matching :: Bool,
  unifying :: Bool
}

type UnifyResult = UnifyResultM SubstitutionEnv

data UnifyResultM a
  = SurelyApart
  | MaybeApart a
  | Unifiable a
  deriving (Show, Functor)

instance Applicative UnifyResultM where
  pure = Unifiable
  (<*>) = ap

instance Monad UnifyResultM where
  SurelyApart >>= _ = SurelyApart
  MaybeApart a >>= f = case f a of
    SurelyApart -> SurelyApart
    MaybeApart b -> MaybeApart b
    Unifiable b -> MaybeApart b
  Unifiable a >>= f = f a

------------------------------------
-- Util functions

-- Sets unify up for type family matching
matchTy :: InjectiveEnv
         -> MonoType -- Should be a MonoType_Fam representing the target
         -> MonoType -- Should be a MonoType_Fam representing the equation (instance)
         -> UnifyResult
matchTy ienv t1 t2 = let
  
  opts = UO {
    injChecking = False
  , matching = True 
  , unifying = False
  }

  in unify ienv opts t1 t2 M.empty

-- Set unify up for pre unification for injectivity check
preUnify :: InjectiveEnv
         -> MonoType -- RHS of type instance 1
         -> MonoType -- RHS of type instance 2
         -> UnifyResult
preUnify ienv t1 t2 = let
  
  opts = UO {
    injChecking = True
  , matching = False 
  , unifying = False
  }

  in unify ienv opts t1 t2 M.empty


unifyTy :: InjectiveEnv
        -> MonoType
        -> MonoType
        -> UnifyResult
unifyTy ienv t1 t2 = let
    
  opts = UO {
    injChecking = False
  , matching = False 
  , unifying = True
  }

  in unify ienv opts t1 t2 M.empty
------------------------------------
-- unify: main work horse for unification
-- Currently implemented for:
-- - Injectivity checking for type families
-- - Matching for type families
-- - Unification for type families (compatibility checks etc).

unify :: InjectiveEnv -- Whether a type fam is injective, important for pre-U for injectivity check
      -> UnifyOptions
      -> MonoType -- type 1
      -> MonoType -- type 2
      -> SubstitutionEnv -- the substitution environment
      -> UnifyResult-- Unification result in the form of perhaps a substitution environment.
-- Two type constructors unify when they are the same
unify _ _ (MonoType_Con cn1) (MonoType_Con cn2) subst
  | cn1 == cn2 = return subst
unify _ _ (MonoType_Var _ tv1) mv@(MonoType_Var _ tv2) subst
  | tv1 == tv2 = return subst
  | otherwise = Unifiable $ M.insert tv1 mv subst
-- If a tyvar is in the substitution, we apply the substitution and move on
unify ienv opts mtv@(MonoType_Var _ tv) t subst
  | M.member tv subst = unify ienv opts (applySubst subst mtv) t subst
-- If the tyvar is in `t`, we have two cases:
-- - 1: we are pre-unifying (inj check). We return MaybeApart with the substitution
-- - 2: we are matching or unifying: we FAIL (Occurs check).
-- If the tyvar is not in `t`, the types are unifiable under tv |-> `t`
unify _ opts (MonoType_Var _ tv) t subst
  | tv `elem` fvToList (applySubst subst t)
    = if injChecking opts
        then MaybeApart subst -- Not sure if apart or not but we return anyway
        else SurelyApart
  | tv `notElem` fvToList (applySubst subst t)
    = Unifiable $ M.insert tv (applySubst subst t) subst
-- We swap the var and a type if that is allowed (if we are not matching, which is one way).
unify ienv opts t mtv@(MonoType_Var _ _) subst
  | not $ matching opts = unify ienv opts mtv t subst
-- Two applications, match func and arg types accordingly
unify ienv opts (MonoType_App s1 s2) (MonoType_App t1 t2) subst
  = unify ienv opts s1 t1 subst >>= unify ienv opts s2 t2
-- Case of two equal type synonyms
unify _ _ (MonoType_Fam f []) (MonoType_Fam g []) subst
  | f == g = return subst
-- When unifying two type fams we have two options:
-- - If we are in an injectivity check, we unify all injective arguments
-- - If not, we are matching or unifying, in which case all arguments must unify.
-- Of course, only when f == g.
unify ienv opts (MonoType_Fam f fmts) (MonoType_Fam g gmts) subst
  | injChecking opts,
    g == f,
    Just iargs <- M.lookup f ienv,
    fargs <- map (fmts !!) iargs,
    gargs <- map (gmts !!) iargs
    = unifies ienv opts fargs gargs subst
  | g == f = unifies ienv opts fmts gmts subst
-- F a ~ t
-- In case of an injectivity check, we return the substitution.
-- In case of unifying or matching, we fail in this case.
unify _ opts (MonoType_Fam _ _) _ subst
  | injChecking opts = MaybeApart subst
  | otherwise = SurelyApart
-- t ~ F a
-- In case of an injectivity check, we return the substitution.
-- In case of unifying or matching, we fail in this case.
unify _ opts _ (MonoType_Fam _ _) subst
  | injChecking opts = MaybeApart subst
  | otherwise = SurelyApart
-- In all other cases, we fail
unify _ _ t1 t2 subst = trace (show subst ++ " " ++ show t1 ++ " " ++ show t2) SurelyApart 

-- Multiple types that are checked left to right with updated substitution
unifies :: InjectiveEnv -- Whether a type fam is injective, important for pre-U for injectivity check
        -> UnifyOptions
        -> MonoTypes -- types 1
        -> MonoTypes -- types 2
        -> SubstitutionEnv -- the substitution environment
        -> UnifyResult-- Unification result in the form of perhaps a substitution environment.
unifies ienv opts (t1:types1) (t2:types2) subst 
  = unify ienv opts t1 t2 subst >>= \newS -> unifies ienv opts types1 types2 newS
unifies _    _    []          []          subst = return subst
unifies _ _ _ _ _ = SurelyApart -- Should never be reached

-- Applies the substitution environment on a type
applySubst :: SubstitutionEnv -> MonoType -> MonoType
applySubst env mtv@(MonoType_Var _ tv) = fromMaybe mtv (M.lookup tv env)
applySubst _   mtc@(MonoType_Con _)    = mtc
applySubst env (MonoType_Fam f mts)    = MonoType_Fam f $ map (applySubst env) mts
applySubst env (MonoType_App mt1 mt2)  = MonoType_App (applySubst env mt1) (applySubst env mt2)