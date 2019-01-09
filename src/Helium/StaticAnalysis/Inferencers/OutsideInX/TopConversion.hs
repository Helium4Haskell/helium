{-# LANGUAGE BangPatterns #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion(
        monoTypeToTp
    ,   tpSchemeListDifference
    ,   typeToPolytype
    ,   typeToMonoType
    ,   getMonoFromPoly
    ,   getTypeVariablesFromMonoType
    ,   tpSchemeToMonoType
    ,   tpSchemeToPolyType
    ,   polyTypeToTypeScheme
    ,   classEnvironmentToAxioms
    ,   getTypeVariablesFromPolyType

) where

import Unbound.LocallyNameless hiding (Name, freshen)
import Unbound.LocallyNameless.Types (GenBind(..))
import Cobalt.Core.Types hiding (split)
import Top.Types.Classes
import Top.Types.Primitive
import Top.Types.Quantification
import Top.Types.Qualification
import Top.Types.Substitution
import Top.Types.Schemes
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import qualified Data.Map as M
import Control.Monad.State
import Control.Arrow
import Data.Maybe 
import Data.List
import Debug.Trace

deriving instance Show Type
deriving instance Show ContextItem 

bindVariables :: [TyVar] -> PolyType -> PolyType
bindVariables = flip (foldr ((PolyType_Bind .) . bind))


monoTypeToTp :: MonoType -> Tp
monoTypeToTp (MonoType_Var n) = TVar (fromInteger (name2Integer n))
monoTypeToTp (MonoType_Con n args) = foldl TApp (TCon n) (map monoTypeToTp args)
monoTypeToTp (MonoType_Arrow f a) = monoTypeToTp f .->. monoTypeToTp a

polyTypeToTypeScheme :: PolyType -> TpScheme
polyTypeToTypeScheme p = let
        (quant, preds, tp) = runFreshM (ptHelper p)
        qualifiedType = preds .=>. tp
        in bindTypeVariables quant qualifiedType
    where
        constraintToPredicate :: Constraint -> [Predicate]
        constraintToPredicate (Constraint_Class c mts) = map (\m -> Predicate c $ monoTypeToTp m) mts
        ptHelper :: PolyType -> FreshM ([Int], [Predicate], Tp)
        ptHelper (PolyType_Bind b) = do
            (t, p) <- unbind b
            (qs, ps, tp) <- ptHelper p
            return (fromInteger (name2Integer t) : qs, ps, tp)
        ptHelper (PolyType_Mono cs m) = do
            return ([], concatMap constraintToPredicate cs, monoTypeToTp m)



tpSchemeListDifference :: M.Map Name TpScheme -> M.Map Name TpScheme -> M.Map Name  ((Tp, String), (Tp, String))
tpSchemeListDifference m1 m2 = M.map fromJust $ M.filter isJust $ M.intersectionWith eqTpScheme m1 m2

eqTpScheme :: TpScheme -> TpScheme -> Maybe ((Tp, String), (Tp, String))
eqTpScheme t1@(Quantification (is1, qmap1, tp1)) t2@(Quantification (is2, qmap2, tp2)) = let
    subs = M.fromList $ zipWith (\orig rep -> (orig, TVar rep)) is2 is1
    tp2r = subs |-> unqualify tp2
    tp1r = unqualify tp1
    in if tp1r == tp2r  then Nothing else Just ((tp1r, "Orig"), (tp2r, "OutsideIn(X)"))

typeToPolytype :: Integer -> Type -> (PolyType, Integer)
typeToPolytype bu t = let
    (cs, tv, mt) = typeToMonoType t
    (mt', bu') = freshen bu mt 
    vars = getTypeVariablesFromMonoType mt'
    in (foldr (\b p -> PolyType_Bind (B b p)) (PolyType_Mono [] mt') vars, bu')

typeToMonoType :: Type -> ([Constraint], [TyVar], MonoType)
typeToMonoType = tpSchemeToMonoType . makeTpSchemeFromType

tpSchemeToPolyType :: TpScheme -> PolyType
tpSchemeToPolyType tps = let 
        (cs, tv, mt) = tpSchemeToMonoType tps
        pt' = PolyType_Mono cs mt
        pt = bindVariables tv pt'
    in pt 

tpSchemeToMonoType :: TpScheme -> ([Constraint], [TyVar], MonoType)
tpSchemeToMonoType tps = 
    let 
        tyvars = map (\x -> (TVar x, integer2Name (toInteger x))) $ quantifiers tps
        qs :: [Predicate]
        (qs, tp) = split $ unquantify tps
        monoType = tpToMonoType tp
        convertPred :: Predicate -> Constraint
        convertPred (Predicate c v) = case lookup v tyvars of
            Nothing -> internalError "TopConversion" "tpSchemeToMonoType" "Type variable not found"
            Just tv -> Constraint_Class c [var tv]
        in (map convertPred qs , map snd tyvars, monoType)

tpToMonoType :: Tp -> MonoType
tpToMonoType (TVar v) = MonoType_Var (integer2Name $ toInteger v)
tpToMonoType (TApp (TApp (TCon "->") f) t) = tpToMonoType f :-->: tpToMonoType t
tpToMonoType (TCon n) = MonoType_Con n []
tpToMonoType t@(TApp c a) = tConHelper [] t
    where
    tConHelper lst (TApp c a) = tConHelper (tpToMonoType a : lst) c
    tConHelper lst (TCon n) = MonoType_Con n lst
    tConHelper lst (TVar v) = MonoType_Con (show v) lst

getTypeVariablesFromPolyType :: PolyType -> [TyVar]
getTypeVariablesFromPolyType (PolyType_Bind (B p t)) = p : getTypeVariablesFromPolyType t
getTypeVariablesFromPolyType _ = []

getTypeVariablesFromMonoType :: MonoType -> [TyVar]
getTypeVariablesFromMonoType (MonoType_Var v) = [v]
getTypeVariablesFromMonoType (MonoType_Fam _ ms) = nub $ concatMap getTypeVariablesFromMonoType ms
getTypeVariablesFromMonoType (MonoType_Con _ ms) = nub $ concatMap getTypeVariablesFromMonoType ms
getTypeVariablesFromMonoType (MonoType_Arrow f a) = nub $ getTypeVariablesFromMonoType f ++ getTypeVariablesFromMonoType a

getMonoFromPoly :: PolyType -> MonoType
getMonoFromPoly (PolyType_Bind (B p t)) = getMonoFromPoly t
getMonoFromPoly (PolyType_Mono _ m) = m

classEnvironmentToAxioms :: ClassEnvironment -> [Axiom]
classEnvironmentToAxioms env = concatMap (uncurry classToAxioms) (M.toList env)
    where
        classToAxioms :: String -> Class -> [Axiom]
        classToAxioms s (superclasses, instances) = let 
            tv = integer2Name 0 
            superAxiom  | null superclasses = []
                        | otherwise = [Axiom_Class (bind [tv] (map (\sc -> Constraint_Class sc [var tv]) superclasses, s, [var tv]))]
            in
                map instanceToAxiom instances
        instanceToAxiom :: Instance -> Axiom
        instanceToAxiom ((Predicate cn v), supers) = let
                vars = map (integer2Name  . toInteger) (ftv v ++ concatMap (\(Predicate _ v) -> ftv v) supers)
                superCons = map (\(Predicate c v) -> Constraint_Class c [tpToMonoType v]) supers
            in Axiom_Class (bind vars (superCons, cn, [tpToMonoType v]))



instance Freshen MonoType Integer where
    freshenWithMapping mapping n mt = (\(mt', (n', m'))->(map (name2Integer *** name2Integer) m', (mt', n'))) $ 
        runState (freshenHelperMT mt) (n, map (integer2Name *** integer2Name) mapping) 
        
freshenHelperMT :: MonoType -> State (Integer, [(TyVar, TyVar)]) MonoType
freshenHelperMT (MonoType_Var v') =  
    do
        (uniq, mapping) <- get
        case lookup v' mapping of
            Just v -> return (var v)
            Nothing -> put (uniq + 1, (v', integer2Name uniq) : mapping) >> return (var $ integer2Name uniq)
freshenHelperMT (MonoType_Con n vs) = do
    vs' <- mapM freshenHelperMT vs
    return (MonoType_Con n vs')
freshenHelperMT  (f :-->: a) = do
    f' <- freshenHelperMT f
    a' <- freshenHelperMT a
    return $ f' :-->: a'

instance Freshen PolyType Integer where
    freshenWithMapping mapping n mt = (\(mt', (n', m'))->(map (name2Integer *** name2Integer) m', (mt', n'))) $ 
        runState (freshenHelper mt) (n, map (integer2Name *** integer2Name) mapping) 
        where
            freshenHelper :: PolyType -> State (Integer, [(TyVar, TyVar)]) PolyType
            freshenHelper (PolyType_Mono cs m) = do
                m' <- freshenHelperMT m
                return (PolyType_Mono cs m')
            freshenHelper (PolyType_Bind (B p t)) = do
                (uniq, mapping) <- get
                put (uniq, (p, p) : mapping)
                t' <- freshenHelper t
                return (PolyType_Bind (B p t'))
