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

import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Messages.HeliumMessages

import Cobalt.Core.Types
import Cobalt.OutsideIn.Solver
import Cobalt.Core.Errors

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless hiding (Name)
import Unbound.LocallyNameless.Ops hiding (freshen)

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Tree as G
import Data.List
import Data.Maybe
import Data.Either
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


bindingGroupAnalysis ::   (Bool, TypeSignatures, Monos, Touchables, Maybe (Assumptions, Constraints, Substitution), Integer) -> 
                           [BindingGroup] -> 
                           (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG)
bindingGroupAnalysis input@(isTopLevel, typeSignatures, monos, touchables, body, betaUnique) groups =
                  variableDependencies
                  where
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
                              map (concatBindingGroups . map (cs !!)) list ++ (
                                 case body of
                                    Nothing -> []
                                    Just (a, c, s) -> [(M.empty, a, c, s)]
                                 )
                     sortedGroups = bindingGroupAnalysis groups
                     variableDependencies = foldr op initial sortedGroups
                        where
                           instanceTS :: Integer -> Assumptions -> TypeSignatures -> (Integer, [Constraint], Touchables)
                           instanceTS bu ass ts = foldr combineTS (bu, [], []) $ concat $ M.elems $ M.intersectionWith (\a (_, t) -> [(a', t) | (_, a') <- a]) ass ts
                              where
                                 combineTS :: (TyVar, PolyType) -> (Integer, Constraints, Touchables) -> (Integer, [Constraint], Touchables)
                                 combineTS (a, t) (bu, cs, tc) = let
                                    (t', bu') = snd $ freshenWithMapping (map (name2Integer &&& name2Integer) monos) bu t
                                    in (bu', Constraint_Unify (var a) (getMonoFromPoly t') : cs, getTypeVariablesFromMonoType (getMonoFromPoly t') ++ tc)
                           instanceTSE :: Environment -> TypeSignatures -> Constraints
                           instanceTSE env1 ts = concatMap snd $ M.toList $ M.intersectionWith (\e (b, t) -> [Constraint_Unify (var b) $ getMonoFromPoly t, Constraint_Unify (var b) (var e)]) env1 ts
                           equalASENV :: Assumptions -> Environment -> Constraints
                           equalASENV ass env = concat $ M.elems $ M.intersectionWith (\a e -> [Constraint_Unify (var a') (var e) | (_, a') <- a]) ass env
                           initial :: (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG)
                           initial = (touchables, M.empty, typeSignatures, [], betaUnique, [], [], [])
                           op :: (Environment, Assumptions, Constraints, Substitution) -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG) -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG) 
                           op g@(env1, ass1, con1, subs1) (touchs, ass2, ts2, con2, bu, subsOrig, typeErrors, iBDG) =
                              let
                                  {- Solving -}
                                 sBu = bu
                                 sAxioms = []
                                 sGiven = []
                                 sWanted = subsConstraints subs1 ++ subsConstraints subsOrig ++ con1
                                 sTouchables = touchs ++ touchables ++ touchs1
                                 ((solverResult, _), bu1) = contFreshMRes (solve sAxioms sGiven sWanted sTouchables) sBu

                                 {- Gathering -}
                                 (bu2, c1, touchs1) = instanceTS bu1 ass1 resTypeSignatures
                                 c2 = instanceTSE env1 resTypeSignatures
                                 env' = env1 M.\\ resTypeSignatures
                                 c3 = equalASENV (ass1 M.\\ resTypeSignatures) env'
                                 c4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env'
                                 (resBetaUnique, c5, touchs2) = instanceTS bu2 ass2 resTypeSignatures                                
                                 {- Results -}
                                 resTouchables = touchs2 ++ touchs1 ++ right touchable [] solverResult
                                 resAssumptions = ((ass1 M.\\ resTypeSignatures) M.\\ env') `combineAssumptions` (ass2 M.\\ env')

                                 resTypeSignatures | isTopLevel = ts2 `M.union` M.fromList (mapMaybe (\(n, v) -> (\m -> (n, (v, PolyType_Mono [] m))) <$> lookup v resSubstitution) (M.toList env1))
                                                   | otherwise =  ts2
                                 resConstraints = c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ right residual [] solverResult ++ con2
                                 resSubstitution = right substitution [] solverResult
                                 resTypeErrors = left makeTypeError [] solverResult ++ typeErrors
                                 resInheritedBDG = (M.keys env1, M.elems env') : iBDG
                              in (resTouchables, resAssumptions, resTypeSignatures, resConstraints, resBetaUnique, resSubstitution, resTypeErrors, resInheritedBDG)

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

makeTypeError :: NamedSolverError -> [TypeError]
makeTypeError s = [TypeError [] [MessageOneLiner $ MessageString $ show s] [] []]

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
