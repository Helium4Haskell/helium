{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# lANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes where

import Control.Monad.Trans.State

import Data.List
import Data.Maybe

import Rhodium.Core
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties

import qualified Unbound.Generics.LocallyNameless as UB
import qualified Unbound.Generics.LocallyNameless.Fresh as UB
import qualified Unbound.Generics.LocallyNameless.Alpha as UB
import qualified Unbound.Generics.LocallyNameless.Bind as UB
--import qualified Unbound.Generics.LocallyNameless.Types as UB
import qualified Unbound.Generics.LocallyNameless.Subst as UB
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.LocallyNameless hiding (Name)
import GHC.Generics

import Helium.Syntax.UHA_Syntax ()
import Helium.Syntax.UHA_Range ()
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree

import Debug.Trace
import Data.Typeable (Typeable)
import Helium.Utils.Utils (internalError)

data RType ci = PType (PolyType ci) | MType MonoType



fromMType :: RType ci -> MonoType
fromMType (MType m) = m

deriving instance (Subst MonoType ci, Alpha ci) => Eq (RType ci)
deriving instance (Subst MonoType ci, Alpha ci) => Ord (RType ci)
deriving instance (Subst MonoType ci, Alpha ci) => Show (RType ci)

type TyVar = UB.Name MonoType

class VariableInjection v where
    var :: TyVar -> v
  
instance VariableInjection (PolyType ci) where
    var = PolyType_Mono [] . var
  
instance VariableInjection MonoType where
    var v = MonoType_Var Nothing v Nothing

type MonoTypes = [MonoType]

type ReductionTrace = [(ReductionStep, Int)]
data ReductionStep = Step MonoType MonoType (Maybe (Constraint ())) ReductionType
    deriving (Ord, Eq)

instance Show ReductionStep where
    show (Step after before constr rt) 
        = "Reduction: " ++ show after ++ " reduced from: " ++ show before ++ " in constraint: " ++ show constr ++ ". Type: " ++ show rt

data ReductionType
  = LeftToRight MonoType
  | TopLevelImprovement
  | CanonReduction
  deriving (Generic, Ord, Eq, Show)

instance UB.Subst MonoType ReductionStep where
   substs _ = id
   isvar _ = Nothing
   subst _ _ = id

instance Alpha ReductionStep where
   fvAny' _ _ = pure 
   swaps' = error "swaps'"
   lfreshen' = error "lfreshen'"
   freshen' = error "freshen'"
   aeq' = error "aeq'"
   acompare' = error "acompare'"
   close _ _ x = x
   open _ _ x = x
   isPat = error "isPat"
   isTerm = error "isTerm"
   isEmbed = error "isEmbed"
   nthPatFind = error "nthPatFind"
   namePatFind _ = error "namePatFind"

insertReductionStepMaybe :: MonoType -> Maybe ReductionStep -> MonoType
insertReductionStepMaybe m (Just rs) = insertReductionStep m rs
insertReductionStepMaybe m Nothing   = m

insertReductionStep :: MonoType -> ReductionStep -> MonoType
insertReductionStep (MonoType_Var ms v _) rs  = MonoType_Var ms v (Just rs)
insertReductionStep (MonoType_Fam f mts _) rs = MonoType_Fam f mts (Just rs)
insertReductionStep (MonoType_Con s _) rs     = MonoType_Con s (Just rs)
insertReductionStep (MonoType_App m1 m2 _) rs = MonoType_App m1 m2 (Just rs)

getMaybeReductionStep :: MonoType -> Maybe ReductionStep
getMaybeReductionStep (MonoType_Var _ _ rs)  = rs
getMaybeReductionStep (MonoType_Fam _ _ rs)  = rs
getMaybeReductionStep (MonoType_Con _ rs)    = rs
getMaybeReductionStep (MonoType_App _ _ rs)  = rs

removeCI :: Constraint ci -> Constraint ()
removeCI (Constraint_Unify m1 m2 _) = Constraint_Unify m1 m2 Nothing
removeCI _ = internalError "RhodiumTypes.hs" "removeCI" "removeCI should only be performed over unify constraints!"

data MonoType 
    = MonoType_Fam   String [MonoType] (Maybe ReductionStep)
    | MonoType_Var   (Maybe String) TyVar (Maybe ReductionStep)
    | MonoType_Con   String (Maybe ReductionStep)
    | MonoType_App   MonoType MonoType (Maybe ReductionStep)
    deriving (Ord, Generic)

instance Eq MonoType where
    MonoType_Fam s1 ms1 _== MonoType_Fam s2 ms2 _= s1 == s2 && ms1 == ms2
    MonoType_Var _ v1 _ == MonoType_Var _ v2 _ = v1 == v2
    MonoType_Con s1 _ == MonoType_Con s2 _ = s1 == s2
    MonoType_App f1 a1 _ == MonoType_App f2 a2 _ = f1 == f2 && a1 == a2
    _ == _ = False

isFamilyFree :: MonoType -> Bool
isFamilyFree (MonoType_Con _ _)       = True
isFamilyFree (MonoType_Fam _ _ _)     = False
isFamilyFree (MonoType_Var _ _ _)     = True
isFamilyFree (MonoType_App a1 a2 _)   = isFamilyFree a1 && isFamilyFree a2

pattern s :-->: r        = MonoType_App (MonoType_App (MonoType_Con "->" Nothing) s Nothing) r Nothing
pattern MonoType_List t ri  = MonoType_App (MonoType_Con   "List" Nothing) t ri
pattern MonoType_Tuple a b ri = MonoType_App (MonoType_App (MonoType_Con "Tuple2" Nothing) a Nothing) b ri

instance Show MonoType where
    show = showMT []
showMT :: [(TyVar, String)] -> MonoType -> String
showMT mp (MonoType_List t _)      = "[" ++ showMT mp t ++ "]"
showMT mp (MonoType_App (MonoType_Con "[]" _) t _) = "[" ++ showMT mp t ++ "]"
showMT mp (MonoType_Tuple t1 t2 _) = "(" ++ showMT mp t1 ++ "," ++ showMT mp t2 ++ ")"
showMT mp (MonoType_Con c _)       = c 
showMT mp (MonoType_Fam c a _)     = c ++ concatMap (\x -> " " ++ doParens (showMT mp x)) a
showMT mp (s :-->: t)            = doParens (showMT mp s) ++ " -> " ++ showMT mp t
showMT mp (MonoType_Var s v _)     = let r = fromMaybe (fromMaybe (show v) s) (lookup v mp) in if r == "" then show v else r
showMT mp ma@(MonoType_App f a _)  = case separateMt ma of 
                                    (MonoType_Con s _, tp) | length s > 2 && head s == '(' && last s == ')' && all (==',') (tail (init s)) ->
                                       "(" ++ intercalate ", " (map show tp) ++ ")"
                                    _ -> showMT mp f ++ " " ++ showMT mp a

doParens :: String -> String
doParens s  | ' ' `elem` s = '(' : s ++ ")"
            | otherwise    = s


type InfoTrees = [InfoTree]
type InfoTree = DoublyLinkedTree LocalInfo
                            
data LocalInfo = 
        LocalInfo { self           :: UHA_Source  
                , assignedType   :: Maybe TyVar
                    }
    deriving (Show, Generic)

data Constraint ci
    = Constraint_Unify MonoType MonoType (Maybe ci)
    | Constraint_Inst  MonoType (PolyType ci) (Maybe ci)
    | Constraint_Class String [MonoType] (Maybe ci)
    | Constraint_Exists (UB.Bind [TyVar] ([Constraint ci],[Constraint ci])) (Maybe ci)
    deriving (Generic)

instance (Alpha ci, Subst MonoType ci) => Eq (Constraint ci) where
    Constraint_Unify m1 m2 _ == Constraint_Unify n1 n2 _ = m1 == n1 && m2 == n2
    Constraint_Inst  m1 m2 _ == Constraint_Inst  n1 n2 _ = m1 == n1 && m2 == n2
    Constraint_Class c1 a1 _ == Constraint_Class c2 a2 _ = c1 == c2 && a1 == a2
    Constraint_Exists b1   _ == Constraint_Exists b2   _ = UB.runFreshM $ do
        s <- UB.unbind2 b1 b2
        case s of
            Just (_,c1,_,c2) -> return $ c1 == c2
            Nothing          -> return False
    _ == _ = False

instance (Alpha ci, Subst MonoType ci) => Show (Constraint ci) where
    show = runFreshM . showConstraint

showConstraint :: (UB.Fresh m, Functor m, Alpha ci, Subst MonoType ci) => Constraint ci -> m String
showConstraint (Constraint_Unify t p s) = return $ show t ++ " ~ " ++ show p
showConstraint (Constraint_Inst  t p _) = do    p' <- showPolyType' [] p
                                                return $ show t ++ " > " ++ p'
showConstraint (Constraint_Class c t _) = do    let ps = map (doParens . show) t
                                                return $ c ++ " " ++ intercalate ", " ps
showConstraint (Constraint_Exists b _)  = do    (x, (q,c)) <- UB.unbind b
                                                q' <- showConstraintList' q
                                                c' <- showConstraintList' c
                                                return $ "∃" ++ show x ++ "(" ++ q' ++ " => " ++ c' ++ ")" 

data PolyType ci
    = PolyType_Bind String (UB.Bind TyVar (PolyType ci))
    | PolyType_Mono [Constraint ci] MonoType
    deriving (Generic)

instance (Alpha ci, Subst MonoType ci) => Eq (PolyType ci) where
    PolyType_Bind s1 b1   == PolyType_Bind s2 b2 = UB.runFreshM $ do
        s <- UB.unbind2 b1 b2
        case s of
            Just (_,p1,_,p2) -> return $ p1 == p2
            Nothing          -> return False
    PolyType_Mono c1 m1 == PolyType_Mono c2 m2 = c1 == c2 && m1 == m2
    _                   == _                   = False

instance (Alpha ci, Subst MonoType ci) => Ord (PolyType ci) where
    p1 <= p2 = UB.runFreshM (se p1 p2)
        where
        se :: UB.Fresh m => PolyType ci -> PolyType ci -> m Bool
        se (PolyType_Mono cs1 m1) (PolyType_Mono cs2 m2) = return $ cs1 <= cs2 && m1 <= m2
        se (PolyType_Mono _ _) _ = return True
        se (PolyType_Bind s1 b1) (PolyType_Bind s2 b2) = do
            s <- UB.unbind2 b1 b2
            case s of
                Just (_, p1, _, p2) -> se p1 p2
        se (PolyType_Bind _ _) _ = return True

instance (Alpha ci, Subst MonoType ci) => Show (PolyType ci) where
    show = UB.runFreshM . showPolyType' []
          
showPolyType' :: (Alpha ci, Subst MonoType ci, UB.Fresh m) => [(TyVar, String)] -> PolyType ci -> m String
showPolyType' mp (PolyType_Bind s b@(UB.B t p)) = do
    (x, r) <- UB.unbind b
    showR <- showPolyType' ((x, s) : mp) r
    return $ "{" ++ show x ++ "}" ++ showR
showPolyType' mp (PolyType_Mono [] m) = return $ showMT mp m
showPolyType' mp (PolyType_Mono cs m) = return $ showConstraintList (filter hasConstraintInformation cs) ++ " => " ++ showMT mp m


hasConstraintInformation :: Constraint ci -> Bool
hasConstraintInformation (Constraint_Class c ms Nothing) = False
hasConstraintInformation (Constraint_Class _ _ _) = True

showConstraintList :: (Alpha ci, Subst MonoType ci) => [Constraint ci] -> String
showConstraintList = UB.runFreshM . showConstraintList'

showConstraintList' :: (Alpha ci, Subst MonoType ci, UB.Fresh m, Functor m) => [Constraint ci] -> m String
showConstraintList' [] = return "∅"
showConstraintList' l  = intercalate " ∧ " <$> mapM showConstraint l

instance (Alpha ci, Subst MonoType ci) => Ord (Constraint ci) where
    Constraint_Unify m1 m2 _ <= Constraint_Unify n1 n2 _ = m1 <= n1 && m2 <= n2
    Constraint_Unify _ _ _ <= _ = True
    Constraint_Inst  m1 m2 _ <= Constraint_Inst  n1 n2 _ = m1 <= n1 && m2 <= n2
    Constraint_Inst _ _ _ <= _ = True
    Constraint_Class c1 a1 _ <= Constraint_Class c2 a2 _ = c1 <= c2 && a1 <= a2
    Constraint_Class _ _ _ <= _ = True
    Constraint_Exists b1 _   <= Constraint_Exists b2 _   = UB.runFreshM $ do
        s <- UB.unbind2 b1 b2
        case s of
            Just (_,c1,_,c2) -> return $ c1 <= c2
            Nothing          -> return False
    Constraint_Exists _ _ <= _ = True

data Axiom ci
    = Axiom_Unify (UB.Bind [TyVar] (MonoType, MonoType)) (Maybe [Int])
    | Axiom_Class (UB.Bind [TyVar] ([Constraint ci], String, [MonoType]))
    | Axiom_Injective String [Int] -- Injective type families with indx of injective arguments
    | Axiom_Defer     String  -- Deferred type families
    | Axiom_ClosedGroup String [Axiom ci] -- Closed type family group
    deriving (Generic)

instance (Alpha ci, Subst MonoType ci) => Show (Axiom ci) where
    show = runFreshM . showAxiom
    
showAxiom :: (Fresh m, Functor m, Alpha ci, Subst MonoType ci) => Axiom ci -> m String
showAxiom (Axiom_Unify b _) = do  
                                (xs, (lhs,rhs)) <- unbind b
                                return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs
showAxiom (Axiom_Class b) = do  (xs, (ctx,c,ms)) <- unbind b
                                let ps = map (doParens . show) ms
                                return $ "∀" ++ show xs ++ " " ++ show ctx ++
                                        " => $" ++ c ++ " " ++ unwords ps
showAxiom (Axiom_Injective f _) = return $ "injective ^" ++ f
showAxiom (Axiom_Defer f) = return $ "defer ^" ++ f
showAxiom (Axiom_ClosedGroup _ axs) = do 
                                        xs <- mapM showAxiom axs
                                        let concatted = "[" ++ intercalate ", " xs ++ "]"
                                        return $ "Closed ^ (" ++ concatted ++ ")"



instance (Alpha ci, Subst MonoType ci) => Alpha (PolyType ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (PolyType ci)

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var _ v _)  = Just (SubstName v)
  isvar _                   = Nothing

instance Alpha ReductionType
instance (Alpha ci, Subst MonoType ci) => Alpha (Constraint ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (Constraint ci)
instance Subst MonoType ReductionType
  
instance (Alpha ci, Subst MonoType ci) => Alpha (Axiom ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (Axiom ci)

conApply :: String -> [MonoType] -> MonoType
conApply s = foldl (\st l -> MonoType_App st l Nothing) (MonoType_Con s Nothing)

conApply' :: MonoType -> [MonoType] -> MonoType
conApply' = foldl (\st l -> MonoType_App st l Nothing)

separateMt :: MonoType -> (MonoType, [MonoType])
separateMt (MonoType_App m1 m2 _) = let
    (c, ms) = separateMt m1 in (c, ms ++ [m2])
separateMt c@(MonoType_Con _ _)   = (c, [])
separateMt v@(MonoType_Var _ _ _) = (v, [])
separateMt (MonoType_Fam f mts ri)   = (MonoType_Con f ri, mts)

-- conList :: MonoType -> (MonoType, [MonoType])
-- conList (MonoType_App m1 m2) = let ms = getMonotypeAppList m1 ++ getMonotypeAppList m2 in (head ms, tail ms)
-- conList (MonoType_Con s) = (MonoType_Con s, [])
-- conList v@(MonoType_Var _ _) = (v, [])
-- conList m = error $ "No conList possible for " ++ show m

-- getMonotypeAppList :: MonoType -> [MonoType]
-- getMonotypeAppList (MonoType_App f a) = getMonotypeAppList f ++ getMonotypeAppList a
-- getMonotypeAppList x = [x]


isClassConstraint :: Constraint a -> Bool
isClassConstraint (Constraint_Class _ [_] _) = True
isClassConstraint _ = False

isUnifyConstraint :: Constraint a -> Bool
isUnifyConstraint Constraint_Unify{} = True
isUnifyConstraint _ = False

isInstConstraint :: Constraint a -> Bool
isInstConstraint Constraint_Inst{} = True
isInstConstraint _ = False

firstConstraintElement :: Constraint a -> MonoType
firstConstraintElement (Constraint_Unify m1 _ _ ) = m1
firstConstraintElement (Constraint_Inst m1 _ _) = m1
firstConstraintElement c = error "No first constraint element"

fvToList :: (Alpha a, Typeable b) => a -> [UB.Name b]
fvToList = toListOf fv