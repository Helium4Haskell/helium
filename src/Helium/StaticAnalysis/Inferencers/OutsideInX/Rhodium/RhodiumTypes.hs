{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes where

import Control.Monad.Trans.State

import Data.List
import Data.Maybe

import Rhodium.Core
import Rhodium.TypeGraphs.Graph

import qualified Unbound.LocallyNameless as UB
import qualified Unbound.LocallyNameless.Fresh as UB
import qualified Unbound.LocallyNameless.Alpha as UB
import qualified Unbound.LocallyNameless.Types as UB
import qualified Unbound.LocallyNameless.Subst as UB
import Unbound.LocallyNameless hiding (Name)

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Range
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages

type TyVar = UB.Name MonoType

class VariableInjection v where
    var :: TyVar -> v
  
instance VariableInjection PolyType where
    var = PolyType_Mono [] . var
  
instance VariableInjection MonoType where
    var = MonoType_Var Nothing

data MonoType 
    = MonoType_Fam   String [MonoType]
    | MonoType_Var   (Maybe String) TyVar
    | MonoType_Con   String 
    | MonoType_App   MonoType MonoType
    deriving (Eq, Ord)

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
showMT mp (MonoType_Fam c a)     = '^':c ++ concatMap (\x -> " " ++ doParens (showMT mp x)) a
showMT mp (s :-->: t)            = doParens (showMT mp s) ++ " -> " ++ showMT mp t
showMT mp (MonoType_Var s v)     = fromMaybe (fromMaybe (show v) s) (lookup v mp)
showMT mp (MonoType_App f a)     = showMT mp f ++ " " ++ showMT mp a
showMT mp _                      = error "Pattern matching check is not that good"

doParens :: String -> String
doParens s  | ' ' `elem` s = '(' : s ++ ")"
            | otherwise    = s

type Properties = [Property]
data Property   
    = FolkloreConstraint
    | ConstraintPhaseNumber Int
    | HasTrustFactor Float
    | FuntionBindingEdge Int{-number of patterns-}
    | InstantiatedTypeScheme PolyType
    | SkolemizedTypeScheme ([MonoType], PolyType)
    | IsUserConstraint Int{-user-constraint-group unique number-} Int{-constraint number within group-}
    | WithHint (String, MessageBlock)
    | ReductionErrorInfo Constraint
    | FromBindingGroup 
    | IsImported Name 
    | ApplicationEdge Bool{-is binary-} [LocalInfo]{-info about terms-}
    | ExplicitTypedBinding -- superfluous?
    | ExplicitTypedDefinition [MonoType]{- monos-} Name{- function name -}
    | Unifier TyVar{-type variable-} (String{-location-}, LocalInfo, String{-description-})
    | EscapedSkolems [Int]
    | PredicateArisingFrom (Constraint, ConstraintInfo)
    | TypeSignatureLocation Range
    | TypePair (MonoType, MonoType)
    | CustomError String
    | NeverDirectiveProperty (Constraint, ConstraintInfo)
    | CloseDirectiveProperty (String, ConstraintInfo)
    | DisjointDirectiveProperty (String, ConstraintInfo) (String, ConstraintInfo)
    | MissingConcreteInstance String MonoType
    | AddConstraintToTypeSignature (Maybe (Constraint, EdgeId, ConstraintInfo)) Constraint
    | RelevantFunctionBinding Constraint
    | ClassUsages [(Constraint, EdgeId, ConstraintInfo)]
    | AmbigiousClass Constraint
    | FromGADT
    | UnreachablePattern MonoType MonoType
    | GADTPatternApplication
    | PatternMatch TyVar Int {- Case index arm -} (Maybe Constraint)
    | PossibleTypeSignature PolyType
    

type InfoTrees = [InfoTree]
type InfoTree = DoublyLinkedTree LocalInfo
                            
data LocalInfo = 
        LocalInfo { self           :: UHA_Source  
                , assignedType   :: Maybe TyVar
                    }

data ConstraintInfo =
    CInfo_ { location      :: String
            , sources       :: (UHA_Source, Maybe UHA_Source{- term -})
            , localInfo     :: InfoTree
            , properties    :: Properties
            , errorMessage  :: Maybe TypeError
            }

type MCI = Maybe ConstraintInfo

data Constraint 
    = Constraint_Unify MonoType MonoType (Maybe ConstraintInfo)
    | Constraint_Inst  MonoType PolyType (Maybe ConstraintInfo)
    | Constraint_Class String [MonoType] (Maybe ConstraintInfo)
    | Constraint_Exists (UB.Bind [TyVar] ([Constraint],[Constraint])) (Maybe ConstraintInfo)

instance Eq Constraint where
    Constraint_Unify m1 m2 _ == Constraint_Unify n1 n2 _ = m1 == n1 && m2 == n2
    Constraint_Inst  m1 m2 _ == Constraint_Inst  n1 n2 _ = m1 == n1 && m2 == n2
    Constraint_Class c1 a1 _ == Constraint_Class c2 a2 _ = c1 == c2 && a1 == a2
    Constraint_Exists b1   _ == Constraint_Exists b2   _ = UB.runFreshM $ do
        s <- UB.unbind2 b1 b2
        case s of
            Just (_,c1,_,c2) -> return $ c1 == c2
            Nothing          -> return False
    _ == _ = False

instance Show Constraint where
    show = runFreshM . showConstraint

showConstraint :: (UB.Fresh m, Functor m) => Constraint -> m String
showConstraint (Constraint_Unify t p s) = return $ show t ++ " ~ " ++ show p
showConstraint (Constraint_Inst  t p _) = do    p' <- showPolyType' [] p
                                                return $ show t ++ " > " ++ p'
showConstraint (Constraint_Class c t _) = do    let ps = map (doParens . show) t
                                                return $ "$" ++ c ++ " |[" ++ intercalate ", " ps ++ "]|"
showConstraint (Constraint_Exists b _)  = do    (x, (q,c)) <- UB.unbind b
                                                q' <- showConstraintList' q
                                                c' <- showConstraintList' c
                                                return $ "∃" ++ show x ++ "(" ++ q' ++ " => " ++ c' ++ ")" 

data PolyType 
    = PolyType_Bind String (UB.Bind TyVar PolyType)
    | PolyType_Mono [Constraint] MonoType

instance Eq PolyType where
    PolyType_Bind s1 b1   == PolyType_Bind s2 b2 = UB.runFreshM $ do
        s <- UB.unbind2 b1 b2
        case s of
            Just (_,p1,_,p2) -> return $ p1 == p2
            Nothing          -> return False
    PolyType_Mono c1 m1 == PolyType_Mono c2 m2 = c1 == c2 && m1 == m2
    _                   == _                   = False

instance Ord PolyType where
    p1 <= p2 = UB.runFreshM (se p1 p2)
        where
        se :: UB.Fresh m => PolyType -> PolyType -> m Bool
        se (PolyType_Mono cs1 m1) (PolyType_Mono cs2 m2) = return $ cs1 <= cs2 && m1 <= m2
        se (PolyType_Mono _ _) _ = return True
        se (PolyType_Bind s1 b1) (PolyType_Bind s2 b2) = do
            s <- UB.unbind2 b1 b2
            case s of
                Just (_, p1, _, p2) -> se p1 p2
        se (PolyType_Bind _ _) _ = return True

instance Show PolyType where
    show = UB.runFreshM . showPolyType' []
          
showPolyType' :: UB.Fresh m => [(TyVar, String)] -> PolyType -> m String
showPolyType' mp (PolyType_Bind s b@(UB.B t p)) = do
    (x, r) <- UB.unbind b
    showR <- showPolyType' ((x, s) : mp) r
    return showR
showPolyType' mp (PolyType_Mono [] m) = return $ "[] => " ++ showMT mp m
showPolyType' mp (PolyType_Mono cs m) = return $ showConstraintList cs ++ " => " ++ showMT mp m


showConstraintList :: [Constraint] -> String
showConstraintList = UB.runFreshM . showConstraintList'

showConstraintList' :: (UB.Fresh m, Functor m) => [Constraint] -> m String
showConstraintList' [] = return "∅"
showConstraintList' l  = intercalate " ∧ " <$> mapM showConstraint l

instance Ord Constraint where
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
    _ <= _ = False

data Axiom
    = Axiom_Unify (UB.Bind [TyVar] (MonoType, MonoType))
    | Axiom_Class (UB.Bind [TyVar] ([Constraint], String, [MonoType]))
    | Axiom_Injective String  -- Injective type families
    | Axiom_Defer     String  -- Deferred type families

instance Show Axiom where
    show = runFreshM . showAxiom
    
showAxiom :: (Fresh m, Functor m) => Axiom -> m String
showAxiom (Axiom_Unify b) = do  (xs, (lhs,rhs)) <- unbind b
                                return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs
showAxiom (Axiom_Class b) = do  (xs, (ctx,c,ms)) <- unbind b
                                let ps = map (doParens . show) ms
                                return $ "∀" ++ show xs ++ " " ++ show ctx ++
                                        " => $" ++ c ++ " " ++ intercalate " " ps
showAxiom (Axiom_Injective f) = return $ "injective ^" ++ f
showAxiom (Axiom_Defer f) = return $ "defer ^" ++ f

$(UB.derive [''PolyType, ''MonoType, ''Constraint, ''Axiom])

instance Alpha PolyType
instance Subst MonoType PolyType

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var _ v)  = Just (SubstName v)
  isvar _                   = Nothing

instance Alpha Constraint
instance Subst MonoType Constraint
  
instance Alpha Axiom
instance Subst MonoType Axiom 

data RType = PType PolyType | MType MonoType

fromMType :: RType -> MonoType
fromMType (MType m) = m

deriving instance Eq RType
deriving instance Ord RType

instance UB.Alpha ConstraintInfo where
    fv' _ _ = UB.emptyC
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

instance UB.Rep ConstraintInfo

instance (UB.Rep1 UB.AlphaD ConstraintInfo)

instance UB.Subst MonoType ConstraintInfo where
    substs _ = id

instance UB.Rep1 (UB.SubstD MonoType) ConstraintInfo

instance Show RType where
    show (PType pt) = show pt
    show (MType mt) = show mt
         
instance Show ConstraintInfo where
    show x = location x ++ show (properties x) -- ++ fromMaybe [] (sortAndShowMessages . (:[]) <$> errorMessage x)

-------------------------------------------------------------------------
-- Properties


instance Show Property where
    show FolkloreConstraint = "FolkloreConstraint"
    show (ConstraintPhaseNumber _) = "ConstraintPhaseNumber"
    show (HasTrustFactor f) = "HasTrustFactor: " ++ show f
    show (FuntionBindingEdge _) = "FuntionBindingEdge"
    show (InstantiatedTypeScheme _) = "InstantiatedTypeScheme"
    show (SkolemizedTypeScheme _) = "SkolemizedTypeScheme"
    show (IsUserConstraint _ _) = "IsUserConstraint"
    show (WithHint (s, _) ) = "WithHint: " ++ s
    show (ReductionErrorInfo _) = "ReductionErrorInfo"
    show (FromBindingGroup) = "FromBindingGroup"
    show (IsImported _) = "IsImported"
    show (ApplicationEdge _ lc) = "ApplicationEdge" ++ show (map assignedType lc)
    show ExplicitTypedBinding = "ExplicitTypedBinding"
    show (ExplicitTypedDefinition _ _) = "ExplicitTypedDefinition"
    show (Unifier _ _) = "Unifier"
    show (EscapedSkolems _) = "EscapedSkolems"
    show (PredicateArisingFrom _) = "PredicateArisingFrom"
    show (TypeSignatureLocation _) = "TypeSignatureLocation"
    show (TypePair (t1, t2)) = "TypePair (" ++ show t1 ++ ", " ++ show t2 ++ ")" 
    show (MissingConcreteInstance n ms) = "MissingConcreteInstance(" ++ show n ++ " " ++ show ms ++ ")" 
    show (AddConstraintToTypeSignature ms cc) = "AddConstraintToTypeSignature " ++ show cc ++ " => " ++ show ms
    show (RelevantFunctionBinding fb) = "RelevantFunctionBinding: " ++ show fb
    show (ClassUsages cis) = "ClassUsages " ++ show cis
    show (AmbigiousClass c) = "AmbigiousClass " ++ show c
    show (FromGADT) = "FromGADT"
    show (UnreachablePattern m1 m2) = "UnreachablePattern(" ++ show m1 ++ ", " ++ show m2 ++ ")"
    show GADTPatternApplication = "GADTPatternApplication"
    show (PatternMatch v i mc) = "PatternMatch(" ++ show v ++ ", " ++ show i ++ "," ++ show mc ++ ")"
    show (PossibleTypeSignature ps) = "PossibleTypeSignature " ++ show ps


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