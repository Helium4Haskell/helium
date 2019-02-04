{-| Module      :  BindingGroupAnalysis
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Binding groups (mutually recursive function definitions)
-}

-- To do: clean up this module. Also see BGA for kind inferencing

module Helium.StaticAnalysis.Inferencers.OutsideInX.BindingGroupAnalysis where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Range   
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils

import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Messages.HeliumMessages

import Cobalt.OutsideIn
import Cobalt.Core

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless hiding (Name, close)
import Unbound.LocallyNameless.Ops hiding (freshen)
import Unbound.LocallyNameless.Types hiding (Name)

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Tree as G
import Data.List
import Data.Maybe
import Data.Either
import Data.Foldable
import Data.Functor.Identity

import Control.Monad.State
import Control.Arrow hiding (left, right)

import Debug.Trace


type Assumptions = M.Map Name [(Name, TyVar)]
type Environment = M.Map Name TyVar

type TypeSignatures = M.Map Name (TyVar, PolyType)
type Monos = [TyVar]
type Touchables = [TyVar]
type Constraints = [Constraint]
type BindingGroup = (Environment, Assumptions, Constraints, Substitution)
type Substitution = [(TyVar, MonoType)]
type InheritedBDG  = [(Names, Monos)]


combineAssumptions :: Assumptions -> Assumptions -> Assumptions
combineAssumptions = M.unionWith (++)

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (M.empty, M.empty, [], [])

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1, s1) (e2,a2,c2, s2) = 
   (e1 `M.union` e2, a1 `combineAssumptions` a2, c1++c2, s1 ++ s2)

concatBindingGroups :: [BindingGroup] -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup


bindingGroupAnalysis ::   (Bool, [Axiom], TypeSignatures, Monos, Touchables, Maybe (Assumptions, Constraints, Substitution), TypeErrors, [Constraint], Integer, [(String, [String], [TyVar])]) -> 
                           [BindingGroup] -> 
                           (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints, InheritedBDG)
bindingGroupAnalysis input@(isTopLevel, axioms, typeSignatures, monos, touchables, body, errors, resolvedConstraints, betaUnique, classContexts) groups =
                  variableDependencies
                  where
                     bodyAssumptions = maybe M.empty (\(a, _, _) -> a) body
                     bindingGroupAnalysis :: [BindingGroup] -> [BindingGroup]
                     bindingGroupAnalysis cs =
                           let 
                              explicits = M.keys typeSignatures
                              indexMap = concat (zipWith f cs [0..])
                              f (env,_,_,_) i = [ (n,i) | n <- M.keys env, n `notElem` explicits ]
                              edges    = concat (zipWith f' cs [0..])
                              f' (_,ass,_,_) i = [ (i,j)| n <- M.keys ass, (n',j) <- indexMap, n==n' ]
                              list = topSort (length cs-1) edges
                           in 
                              (if isTopLevel then reverse else id) (map (concatBindingGroups . map (cs !!)) list) ++ (
                                 case body of
                                    Nothing -> []
                                    Just (a, c, s) -> [(M.empty, a, c, s)]
                                 )
                     sortedGroups = bindingGroupAnalysis groups
                     variableDependencies = foldr' op initial sortedGroups
                        where
                           instanceTS :: Integer -> Assumptions -> TypeSignatures -> (Integer, [Constraint], Touchables)
                           instanceTS bu ass ts = foldr combineTS (bu, [], []) $ concat $ M.elems $ M.intersectionWith (\a (_, t) -> [(a', t) | (_, a') <- a]) ass ts
                              where
                                 combineTS :: (TyVar, PolyType) -> (Integer, Constraints, Touchables) -> (Integer, [Constraint], Touchables)
                                 combineTS (a, t) (bu, cs, tc) = let
                                    (mapping, (t', bu')) = freshenWithMapping (map (name2Integer &&& name2Integer) monos) bu t
                                   
                                    in (bu', Constraint_Inst (var a) t' : cs, map (integer2Name . snd) mapping ++ getTypeVariablesFromPolyType t' ++ tc)
                           instanceTSE :: Integer -> Environment -> TypeSignatures -> (Integer, [Constraint], Touchables)
                           instanceTSE bu env1 ts = foldr (\(e, t) (cbu, cons, touchs) -> 
                                 let 
                                    hasConstraints :: PolyType -> Bool
                                    hasConstraints (PolyType_Bind (B _ t)) = hasConstraints t
                                    hasConstraints (PolyType_Mono cs _) = not $ null cs
                                    (bu', classFixConstraint, classFixConstraintTouchables) =
                                          if True || hasConstraints t
                                          then 
                                             let 
                                                (mapping, ((mt, cs), b')) = polytypeToMonoType [] cbu t
                                                mapping' :: [(TyVar, MonoType)]
                                                mapping' = map (\(x, y) -> (integer2Name x, var $ integer2Name y)) mapping
                                             in (b', Constraint_Unify (var e) mt : cs ++ cons, map (integer2Name . snd) mapping ++ touchs)
                                          else (cbu, Constraint_Inst (var e) t : cons, touchs)
                                 in (bu', classFixConstraint, classFixConstraintTouchables)
                              ) (bu, [], []) $ M.intersectionWith (\e (b, t) -> (e, t)) env1 ts
                           equalASENV :: Assumptions -> Environment -> Constraints
                           equalASENV ass env = concat $ M.elems $ M.intersectionWith (\a e -> [Constraint_Unify (var a') (var e) | (_, a') <- a]) ass env
                           initial :: (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints, InheritedBDG)
                           initial = (touchables, M.empty, typeSignatures, [], betaUnique, [], errors, resolvedConstraints, [])
                           op :: (Environment, Assumptions, Constraints, Substitution) -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints, InheritedBDG) -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints, InheritedBDG) 
                           op g@(env1, ass1, con1, subs1) (touchs, ass2, ts2, con2, bu, subsOrig, typeErrors, resolvedConstraints, iBDG) =
                              let
                                 (sbu1, c1, touchs1) = instanceTS bu ass1 ts2
                                 (sbu2, c2, touchs2) = instanceTSE sbu1 env1 ts2
                                 env1' = env1 M.\\ ts2
                                 c3 = equalASENV (ass1 M.\\ ts2) env1'
                                 c4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env1'
                                 (sbu3, c5, touchs3) = instanceTS sbu2 ass2 ts2                                
                                  {- Solving -}
                                 sBu = sbu2
                                 sAxioms = axioms
                                 sGiven = c1 ++ c2
                                 sWanted = (con1 ++ c3 ++ c4 ++ c5)
                                 sTouchables = touchs1 ++ touchs ++ touchs2 ++ touchs3
                                 ((solverResult, _), bu1)   | isTopLevel = contFreshMRes (solve sAxioms sGiven sWanted sTouchables) sBu
                                                            | otherwise = ((error "solve result needed", undefined), sBu) 
                                 {- Gathering -}
                                 ts' = resTypeSignatures M.\\ ts2
                                 (bu2, rc1, touchs4) = instanceTS bu1 ass1 ts'
                                 extractVariable :: TyVar -> MonoType -> TyVar
                                 extractVariable _ (MonoType_Var v) = v
                                 extractVariable def m = def
                                 env1s = M.map (\v -> maybe v (extractVariable v) $ lookup v resSubstitution ) env1'
                                 env' = env1s M.\\ ts'
                                 rc3 = equalASENV (ass1 M.\\ ts') env'
                                 rc4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env'
                                 (resBetaUnique, rc5, touchs5) = instanceTS bu2 ass2 ts'                                
                                 {- Results -}

                                 resTouchables  | isTopLevel   = touchs4 ++ touchs5 ++ right touchable [] solverResult
                                                | otherwise    = touchs4 ++ touchs5 ++ sTouchables 
                                 resAssumptions = ((ass1 M.\\ resTypeSignatures) M.\\ env') `combineAssumptions` (ass2 M.\\ resTypeSignatures M.\\ env')
                                 residualConstraints  | isTopLevel = con2 ++ (right residual [] solverResult \\ right smallGiven [] solverResult)
                                                      | otherwise = con2 ++ sGiven ++ sWanted 
                                 newTS = M.fromList (mapMaybe 
                                    (\(name, v) -> (\m -> 
                                          (name, (
                                             v, addConstraintsToMonoType residualConstraints m))
                                          ) <$> lookup v resSubstitution) 
                                    (M.toList (env1 M.\\ ts2)))
                                 resTypeSignatures | isTopLevel = ts2 `M.union` M.map (\(t, (p, _)) -> (t, replacePolytype (right smallGiven [] solverResult) p)) newTS
                                                   | otherwise =  ts2
                                 resConstraints = rc1 ++ rc3 ++ rc4 ++ rc5 ++ (residualConstraints \\ resResolvedConstraints) ++ right smallGiven [] solverResult -- ++ (c1 ++ c2 ++ c3 ++ c4 ++ c5)
                                 resSubstitution   | isTopLevel = nub $ right substitution [] solverResult ++ subs1 ++ subsOrig
                                                   | otherwise = [] 
                                 resResolvedConstraints = concatMap (snd . snd) (M.elems newTS) ++ resolvedConstraints
                                 resTypeErrors  | isTopLevel = checkTooGeneralSignature (right smallGiven [] solverResult) (M.intersectionWith (\(t1, pt) t2 -> (t1, pt, t2)) ts2 env1)
                                                                   ++ escapeVariableCheck (resAssumptions M.\\ bodyAssumptions) env1 ts2 ++ left createTypeError [] solverResult ++ typeErrors
                                                | otherwise = escapeVariableCheck (resAssumptions M.\\ bodyAssumptions) env1 ts2 ++ typeErrors
                                 resInheritedBDG = (M.keys env1, M.elems env') : iBDG
                                 printResidual | null residualConstraints = id
                                               | otherwise = id -- trace "Residual" $ traceShow residualConstraints
                              in printResidual (resTouchables, resAssumptions, resTypeSignatures, residualConstraints, resBetaUnique, resSubstitution, resTypeErrors, resResolvedConstraints, resInheritedBDG)


replacePolytype :: [Constraint] -> PolyType -> PolyType
replacePolytype [] p = p
replacePolytype (Constraint_Inst (MonoType_Var v) pt:cs) p  | var v == p = pt
                                                            | otherwise =  replacePolytype cs p
replacePolytype (_:cs) p = replacePolytype cs p

checkTooGeneralSignature :: [Constraint] -> M.Map Name (TyVar, PolyType, TyVar) -> [TypeError]
checkTooGeneralSignature cs ts = concatMap (flip checkTS cs) $ M.elems ts
                        where
                           check :: PolyType -> PolyType -> [TypeError]
                           check v1 v2@(PolyType_Mono _ m)  | clearConstraints v1 /= bindVariables (getTypeVariablesFromMonoType m) v2 = createTypeError $ "Type signature " ++ show v1 ++ " too general, more general than " ++ show (bindVariables (getTypeVariablesFromMonoType m) v2)
                                                            | otherwise = []
                           check v1 v2                      | v1 /= v2 = createTypeError $ "Type signature " ++ show v1 ++ " too general, more than " ++ show v2
                                                            | otherwise = []
                           checkTS :: (TyVar, PolyType, TyVar) -> [Constraint] -> [TypeError]
                           checkTS (tyvar, pt, tyvar2) ((Constraint_Unify v1 v2):cs)  | v1 == var tyvar2 = check pt (PolyType_Mono [] v2)
                                                                              | otherwise = checkTS (tyvar, pt, tyvar2) cs
                           checkTS (tyvar, pt, tyvar2) ((Constraint_Inst v1 v2):cs)   | v1 == var tyvar2 = check pt v2
                                                                              | otherwise = checkTS (tyvar, pt, tyvar2) cs
                           checkTS (tyvar, pt, tyvar2) (_:cs)                         = checkTS (tyvar, pt, tyvar2) cs
                           checkTS _ []                                       = []

escapeVariableCheck :: Assumptions -> Environment -> TypeSignatures -> [TypeError]
escapeVariableCheck ass env ts   | null ass = []
                                 | otherwise = let 
                                          ftv = concatMap (getTypeVariablesFromPolyType.snd) (M.intersection ts env)
                                       in traceShow ass $ traceShow env $ traceShow ass $ traceShowId $ concatMap (\v -> createTypeError $ "Variable " ++ show v ++ " is too general in " ++ show (M.intersection ts env) ) ftv

clearConstraints :: PolyType -> PolyType
clearConstraints (PolyType_Mono _ m) = PolyType_Mono [] m
clearConstraints (PolyType_Bind (B t p)) = PolyType_Bind (B t (clearConstraints p))

makeTypeError :: [TyVar] -> Constraint -> [TypeError]
makeTypeError _ (Constraint_Class s v ) = createTypeError ("Missing instance (" ++ s ++ " " ++ show (head v) ++ ")")
makeTypeError touchables (Constraint_Inst (MonoType_Var v) p) | v `notElem` touchables = createTypeError ("Variable " ++ show v ++ " should not be unified")
                                                               | otherwise = []
makeTypeError _ _ = [] 

bindVariables :: [TyVar] -> PolyType -> PolyType
bindVariables = flip (foldr ((PolyType_Bind .) . bind))

traceMessageId :: Show a => String -> a -> a
traceMessageId s x = traceMessage s x x

traceMessage :: Show a => String -> a -> b -> b
traceMessage s x y = trace ("-----BEGIN:" ++ s ++ "-----") $ traceShow x $ trace ("-----END:" ++ s ++ "-----") y

addConstraint :: Constraint -> PolyType -> PolyType
addConstraint c (PolyType_Mono cs mt) = PolyType_Mono (c:cs) mt
addConstraint c (PolyType_Bind b) = runFreshM $ do
   (t, p) <- unbind b
   let p' = addConstraint c p
   return (PolyType_Bind (bind t p'))

addConstraintsToMonoType :: [Constraint] -> MonoType -> (PolyType, [Constraint])
addConstraintsToMonoType cs mt = foldr check (PolyType_Mono [] mt, []) cs
      where
         replace :: TyVar -> PolyType -> PolyType -> FreshM PolyType
         replace v (PolyType_Bind b) orig = do 
            (t, p) <- unbind b
            p' <- replace v p orig
            return $ PolyType_Bind (bind t p')
         replace v (PolyType_Mono cs m) orig = do
            let p = foldr addConstraint orig cs
            let p' = substs [(v, m)] p
            return p'

         toVar :: MonoType -> TyVar
         toVar (MonoType_Var v) = v
         toVar _ = internalError "BindingGroupAnalysis" "toVar" "Monotype is not a var"

         check :: Constraint -> (PolyType, [Constraint]) -> (PolyType, [Constraint])
         check c@(Constraint_Class _ vs) (pt, cs)  | all (\v -> v `elem` map var (boundedVariables pt)) vs = (addConstraint c pt, c : cs)
                                                   | otherwise = (pt, cs)
         check c@(Constraint_Inst v p)  (pt, cs)   | v `elem` map var (boundedVariables pt) = (runFreshM $ replace (toVar v) p pt, c:cs)
                                                   | otherwise = (pt, cs)
         check _ pt = pt

         boundedVariables :: PolyType -> [TyVar]
         boundedVariables (PolyType_Bind (B t p)) = t : boundedVariables p
         boundedVariables (PolyType_Mono _ mt) = getTypeVariablesFromMonoType mt

substitutionToPolyType :: (MonoType, MonoType) -> [Constraint] -> (PolyType, [Constraint])
substitutionToPolyType (tv, mt) cs = let
   hasTV :: MonoType -> Constraint -> Bool
   hasTV tv (Constraint_Inst v1 _) = v1 == tv
   hasTV _ _ = False 
   extractType :: Constraint -> PolyType
   extractType (Constraint_Inst _ p) = p
   relevantConstraints = filter (hasTV tv) cs   
   
   in case relevantConstraints of 
         [] -> (close [] mt)
         (c:_) -> (extractType c, cs \\ relevantConstraints )



instance Show TypeError where
   show x = sortAndShowMessages [x]

topSort :: G.Vertex -> [G.Edge] -> [[G.Vertex]]
topSort n = map G.flatten . G.scc . G.buildG (0, n)

getMonos :: [Constraint] -> Monos
getMonos = concatMap fv

findMono :: Name -> InheritedBDG -> Monos
findMono n xs = 
            let 
               p = elem n . fst
               shead (x:_) = snd x
               shead [] = []
            in shead $ filter p xs

createTypeError :: Show a => a -> [TypeError]
createTypeError s = [TypeError [] [MessageOneLiner $ MessageString $ show s] [] []]

subsConstraints :: Substitution -> Constraints
subsConstraints = map (uncurry (Constraint_Unify . var))

runFreshMRes :: FreshM a -> (a, Integer)
runFreshMRes = runIdentity . runFreshMTRes

runFreshMTRes :: Monad m => FreshMT m a -> m (a, Integer)
runFreshMTRes m = contFreshMTRes m 0

contFreshMRes :: FreshM a -> Integer -> (a, Integer)
contFreshMRes i = runIdentity . contFreshMTRes i

contFreshMTRes :: Monad m => FreshMT m a -> Integer -> m (a, Integer)
contFreshMTRes (FreshMT m) = runStateT m

left :: (a -> c) -> c -> Either a b -> c
left f d (Left x) = f x
left f d (Right _) = d

right :: (b -> c) -> c -> Either a b -> c
right f d (Left _) = d
right f d (Right x) = f x
