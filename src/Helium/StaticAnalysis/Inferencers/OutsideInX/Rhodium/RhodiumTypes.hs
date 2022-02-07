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
    var = MonoType_Var Nothing

type MonoTypes = [MonoType]

data MonoType 
    = MonoType_Fam   String [MonoType]
    | MonoType_Var   (Maybe String) TyVar
    | MonoType_Con   String 
    | MonoType_App   MonoType MonoType
    deriving (Ord, Generic)

instance Eq MonoType where
    MonoType_Fam s1 ms1 == MonoType_Fam s2 ms2 = s1 == s2 && ms1 == ms2
    MonoType_Var _ v1 == MonoType_Var _ v2 = v1 == v2
    MonoType_Con s1 == MonoType_Con s2 = s1 == s2
    MonoType_App f1 a1 == MonoType_App f2 a2 = f1 == f2 && a1 == a2
    _ == _ = False

isFamilyFree :: MonoType -> Bool
isFamilyFree (MonoType_Con _)       = True
isFamilyFree (MonoType_Fam _ _)     = False
isFamilyFree (MonoType_Var _ _)     = True
isFamilyFree (MonoType_App a1 a2)   = isFamilyFree a1 && isFamilyFree a2

pattern s :-->: r          = MonoType_App   (MonoType_App (MonoType_Con "->") s) r
pattern MonoType_List  t   = MonoType_App   (MonoType_Con   "List") t
pattern MonoType_Tuple a b = MonoType_App   (MonoType_App (MonoType_Con "Tuple2") a) b

instance Show MonoType where
    show = showMT []
showMT :: [(TyVar, String)] -> MonoType -> String
showMT mp (MonoType_List t)      = "[" ++ showMT mp t ++ "]"
showMT mp (MonoType_App (MonoType_Con "[]") t) = "[" ++ showMT mp t ++ "]"
showMT mp (MonoType_Tuple t1 t2) = "(" ++ showMT mp t1 ++ "," ++ showMT mp t2 ++ ")"
showMT mp (MonoType_Con c)       = c 
showMT mp (MonoType_Fam c a)     = c ++ concatMap (\x -> " " ++ doParens (showMT mp x)) a
showMT mp (s :-->: t)            = doParens (showMT mp s) ++ " -> " ++ showMT mp t
showMT mp (MonoType_Var s v)     = let r = fromMaybe (fromMaybe (show v) s) (lookup v mp) in r ++ show v -- if r == "" then show v else r
showMT mp ma@(MonoType_App f a)  = case conList ma of 
                                    (MonoType_Con s, tp) | length s > 2 && head s == '(' && last s == ')' && all (==',') (tail (init s)) ->
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
    = Axiom_Unify (UB.Bind [TyVar] (MonoType, MonoType))
    | Axiom_Class (UB.Bind [TyVar] ([Constraint ci], String, [MonoType]))
    | Axiom_Injective String  -- Injective type families
    | Axiom_Defer     String  -- Deferred type families
    deriving (Generic)

instance (Alpha ci, Subst MonoType ci) => Show (Axiom ci) where
    show = runFreshM . showAxiom
    
showAxiom :: (Fresh m, Functor m, Alpha ci, Subst MonoType ci) => Axiom ci -> m String
showAxiom (Axiom_Unify b) = do  (xs, (lhs,rhs)) <- unbind b
                                return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs
showAxiom (Axiom_Class b) = do  (xs, (ctx,c,ms)) <- unbind b
                                let ps = map (doParens . show) ms
                                return $ "∀" ++ show xs ++ " " ++ show ctx ++
                                        " => $" ++ c ++ " " ++ unwords ps
showAxiom (Axiom_Injective f) = return $ "injective ^" ++ f
showAxiom (Axiom_Defer f) = return $ "defer ^" ++ f



instance (Alpha ci, Subst MonoType ci) => Alpha (PolyType ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (PolyType ci)

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var _ v)  = Just (SubstName v)
  isvar _                   = Nothing

instance (Alpha ci, Subst MonoType ci) => Alpha (Constraint ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (Constraint ci)
  
instance (Alpha ci, Subst MonoType ci) => Alpha (Axiom ci)
instance (Alpha ci, Subst MonoType ci) => Subst MonoType (Axiom ci) 




conApply :: String -> [MonoType] -> MonoType
conApply s = foldl MonoType_App (MonoType_Con s)

conApply' :: MonoType -> [MonoType] -> MonoType
conApply' = foldl MonoType_App

conList :: MonoType -> (MonoType, [MonoType])
conList (MonoType_App m1 m2) = let ms = getMonotypeAppList m1 ++ getMonotypeAppList m2 in (head ms, tail ms)
conList (MonoType_Con s) = (MonoType_Con s, [])
conList v@(MonoType_Var _ _) = (v, [])
conList m = error $ "No conList possible for " ++ show m

getMonotypeAppList :: MonoType -> [MonoType]
getMonotypeAppList (MonoType_App f a) = getMonotypeAppList f ++ getMonotypeAppList a
getMonotypeAppList x = [x]


isClassConstraint :: Constraint a -> Bool
isClassConstraint (Constraint_Class _ [_] _) = True
isClassConstraint _ = False

isUnifyConstraint :: Constraint a -> Bool
isUnifyConstraint (Constraint_Unify _ _ _) = True
isUnifyConstraint _ = False

isInstConstraint :: Constraint a -> Bool
isInstConstraint (Constraint_Inst _ _ _) = True
isInstConstraint _ = False

firstConstraintElement :: Constraint a -> MonoType
firstConstraintElement (Constraint_Unify m1 _ _) = m1
firstConstraintElement (Constraint_Inst m1 _ _) = m1
firstConstraintElement c = error "No first constraint element"

fvToList :: (Alpha a, Typeable b) => a -> [UB.Name b]
fvToList = toListOf fv