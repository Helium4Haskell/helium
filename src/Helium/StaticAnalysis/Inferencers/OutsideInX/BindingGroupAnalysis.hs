{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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

import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Messages.HeliumMessages
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumSolver
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances
import Rhodium.Solver.SolveResult as SR
import Rhodium.TypeGraphs.GraphProperties
import Helium.ModuleSystem.ImportEnvironment 


import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless hiding (Name, close, freshen)

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Tree as G
import Data.List
import Data.Maybe
import Data.Foldable
import Data.Functor.Identity

import Control.Monad.State
import Control.Arrow hiding (left, right)

import Debug.Trace
import Helium.Main.Args (Option)


type Assumptions = M.Map Name [(Name, TyVar)]
type Environment = M.Map Name TyVar

type TypeSignatures = M.Map Name (TyVar, PolyType ConstraintInfo)
type Touchables = [TyVar]
type Constraints = [Constraint ConstraintInfo]
type BindingGroup = (Environment, Assumptions, Constraints, Constraints, GADTConstraints)
type Substitution = [(TyVar, MonoType)]

data GADTConstraint = GADTConstraint 
      {  caseArmIndex :: Int
      ,  gadtTouchables :: [TyVar]
      ,  gadtCondition :: [Constraint ConstraintInfo]
      ,  gadtImplication :: [Constraint ConstraintInfo]
      ,  gadtAssumptions :: Assumptions
      ,  gadtSubGADTConstraints :: GADTConstraints
      ,  gadtConstraintInfo :: ConstraintInfo
      }

instance Show GADTConstraint where
   show (GADTConstraint index touch cond imp ass sub _) = unlines $ map ("\t"++) [
      "GADT:[",
         show index,
         show touch,
         show cond,
         show imp,
         show ass,
         show sub,
      "]"
      ]

type GADTConstraints = [GADTConstraint]


combineAssumptions :: Assumptions -> Assumptions -> Assumptions
combineAssumptions = M.unionWith (++)

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (M.empty, M.empty, [], [], [])

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1, gCon1, gcs1) (e2,a2,c2, gCon2, gcs2) = 
   (e1 `M.union` e2, a1 `combineAssumptions` a2, c1++c2, gCon1 ++ gCon2, gcs1 ++ gcs2)

concatBindingGroups :: [BindingGroup] -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup

gadtConstraintsAssumptions :: [GADTConstraint] -> Assumptions
gadtConstraintsAssumptions = foldr (combineAssumptions . gadtAssumptions) M.empty

instanceTS :: ImportEnvironment -> Integer -> Environment -> Assumptions -> TypeSignatures -> (Integer, [Constraint ConstraintInfo])
instanceTS importenv bu env ass ts = foldr combineTS (bu, []) $ concat $ M.elems $ M.intersectionWith (\(n1, a) (n2, (_, t)) -> [(n1, n2, a', t) | (_, a') <- a]) 
      (M.mapWithKey (,) ass) 
      (M.mapWithKey (,) ts)
   where
      combineTS :: (Name, Name, TyVar, PolyType  ConstraintInfo) -> (Integer, Constraints) -> (Integer, [Constraint ConstraintInfo])
      combineTS (n1, _, a, t) (bu', cs) = let
         (_, (t', bu'')) = freshenWithMapping [] bu' t
         ci = Just (cinfoBindingGroupExplicit [] (M.keys env) n1 importenv)
         in (bu'', Constraint_Inst (var a) t' ci : cs)

equalASENV :: Assumptions -> Environment -> Constraints
equalASENV ass env = concat $ M.elems $ M.intersectionWithKey (\n a e -> [Constraint_Unify (var a') (var e) (Just $ cinfoSameBindingGroup n) | (_, a') <- a]) ass env

bindingGroupAnalysis ::   ([Option], ImportEnvironment, Bool, [Axiom ConstraintInfo], TypeSignatures, Touchables, Maybe (Assumptions, Constraints, GADTConstraints), TypeErrors, [Constraint ConstraintInfo], Integer) -> 
                           [BindingGroup] -> 
                           (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints)
bindingGroupAnalysis (options, importenv, isTopLevel, axioms, typeSignatures, touchables, body, ierrors, resolvedConstraints, betaUnique) groups =
                  variableDependencies
                  where
                     bodyAssumptions :: Assumptions
                     bodyAssumptions = maybe M.empty (\(ass, _, _) -> ass) body
                     bindingGroupAnalysis :: [BindingGroup] -> [BindingGroup]
                     bindingGroupAnalysis cs =
                           let 
                              explicits = M.keys typeSignatures
                              indexMap = concat (zipWith f cs [0..])
                              f (env,_,_,_, _) i = [ (n,i) | n <- M.keys env, n `notElem` explicits ]
                              edges    = concat (zipWith f' cs [0..])
                              f' (_,ass,_, _, gass) i = [ (i,j)| n <- M.keys (ass `combineAssumptions` gadtConstraintsAssumptions gass), (n',j) <- indexMap, n==n' ]
                              list = topSort (length cs-1) edges
                           in 
                              (if isTopLevel then reverse else id) (map (concatBindingGroups . map (cs !!)) list) ++ (
                                 case body of
                                    Nothing -> []
                                    Just (a, c, g) -> [(M.empty, a, c, [], g)]
                                 )
                     sortedGroups = bindingGroupAnalysis groups
                     variableDependencies = foldr' op initial sortedGroups
                        where
                           
                           instanceTSE :: Integer -> Environment -> TypeSignatures -> (Integer, [Constraint ConstraintInfo], [Constraint ConstraintInfo])
                           instanceTSE bu env1 ts = foldr (\(n1, n2, e, t) (cbu, gcons, wcons) -> 
                                 let 
                                    (bu', gClassFixConstraint, wClassFixConstraint) =
                                             let 
                                                ((cs, t'), b') = freshen cbu $ unbindPolyTypeSep t
                                                ci = Just (cinfoBindingGroupExplicitTypedBinding [] n2 n1 importenv)
                                             in (b', cs ++ gcons , Constraint_Inst (var e) t' ci : wcons)
                                 in (bu', gClassFixConstraint, wClassFixConstraint)
                              ) (bu, [], []) $ M.intersectionWith (\(n1, e) (n2, (_, t)) -> (n1, n2, e, t)) (M.mapWithKey (,) env1) (M.mapWithKey (,) ts)
                           extractVariable :: TyVar -> MonoType -> TyVar
                           extractVariable _ (MonoType_Var _ v _) = v
                           extractVariable def _ = def
                           
                           initial :: (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints)
                           initial = (touchables, M.empty, typeSignatures, [], betaUnique, [], ierrors, resolvedConstraints)
                           op :: BindingGroup -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints) -> 
                                 (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, Constraints) 
                           op (env1, ass1, con1, gCon1, gadtCons) (touchs, ass2, ts2, con2, bu, subsOrig, typeErrors, resolvedConstraints) =
                              let
                                 (sbu1, c1) = instanceTS importenv bu env1 ass1 ts2
                                 (sbu2, gc2, wc2) = instanceTSE sbu1 env1 ts2
                                 env1' = env1 M.\\ ts2
                                 c3 = equalASENV (ass1 M.\\ ts2) env1' 
                                 c4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) (Just emptyConstraintInfo) | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env1'
                                 (sbu3, c5) = instanceTS importenv sbu2 env1 ass2 ts2
                                 
                                 (sbu4, resGADTConstraints) = resolveGADTAssumptions importenv ts2 env1' sbu3 gadtCons

                                 gadtConstraints   | isTopLevel = map gadtConstraintToConstraint resGADTConstraints
                                                   | otherwise = []
                                 {- -}                                
                                  {- Solving -}
                                 sBu = sbu4
                                 sGiven = gCon1 ++ gc2
                                 -- con1 = body constraints, c2 is typesignature constraint
                                 sWanted = (if isTopLevel && not (null gadtConstraints) then map (appendGADTInfo resGADTConstraints) else id) (trace (show c1) c1 ++ wc2 ++ con1 ++ c3 ++ c4 ++ c5 ++ gadtConstraints)
                                 sTouchables = touchs
                                 sibblings = map (map (second (tpSchemeToPolyType (importEnvironmentToTypeFamilies importenv)))) $ getSiblings importenv
                                 (solverResult, bu1)     | isTopLevel = contFreshMRes (solveOU options sibblings axioms sGiven sWanted sTouchables) sBu
                                                         | otherwise = (error "solve result needed", sBu) 
                                 {- Gathering -}
                                 ts' = resTypeSignatures M.\\ ts2
                                 (bu2, _) = instanceTS importenv bu1 env1 ass1 ts'
                                 
                                 env1s = M.map (\v -> maybe v (extractVariable v) $ lookup v resSubstitution ) env1'
                                 env' = env1s M.\\ ts'
                                 --rc3 = equalASENV (ass1 M.\\ ts') env'
                                 --rc4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) undefined | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env'
                                 (resBetaUnique, _) = instanceTS importenv bu2 env1 ass2 ts'                                
                                 {- Results -}

                                 resTouchables  | isTopLevel   = SR.touchables solverResult
                                                | otherwise    = sTouchables 
                                 resAssumptions = ((ass1 M.\\ resTypeSignatures) M.\\ env') `combineAssumptions` (ass2 M.\\ resTypeSignatures M.\\ env')
                                 residualConstraints  | isTopLevel = con2
                                                      | otherwise = con2 ++ sGiven ++ sWanted 
                                 --newTS :: TypeSignatures
                                 newTS = M.fromList $ map (\(name, v) -> (name, (v, (maybe (var v) (PolyType_Mono []) (lookup v resSubstitution), [])))) $ M.toList (env1 M.\\ ts2)
                                 resTypeSignatures | isTopLevel = ts2 `M.union` M.map (\(t, (p, _)) -> (t, replacePolytype (smallGiven solverResult) p)) newTS
                                                   | otherwise =  ts2
                                 --resConstraints = rc1 ++ rc3 ++ rc4 ++ rc5 ++ (residualConstraints \\ resResolvedConstraints) ++ if isTopLevel then smallGiven solverResult else [] -- ++ (c1 ++ c2 ++ c3 ++ c4 ++ c5)
                                 resSubstitution   | isTopLevel = nub $ substitution solverResult ++ subsOrig
                                                   | otherwise = [] 
                                 resResolvedConstraints = concatMap (snd . snd) (M.elems newTS) ++ resolvedConstraints
                                 resTypeErrors  | isTopLevel = escapeVariableCheck (resAssumptions M.\\ bodyAssumptions) env1 ts2 ++ mapMaybe (errorMessage . (\(ci, _, _) -> ci)) (errors solverResult) ++ typeErrors
                                                | otherwise = escapeVariableCheck (resAssumptions M.\\ bodyAssumptions) env1 ts2 ++ typeErrors
                              in (resTouchables, resAssumptions, resTypeSignatures, residualConstraints, resBetaUnique, resSubstitution, resTypeErrors, resResolvedConstraints)

resolveGADTAssumptions :: ImportEnvironment -> TypeSignatures -> Environment -> Integer -> GADTConstraints -> (Integer, GADTConstraints)
resolveGADTAssumptions importenv ts env bu = foldr (\(GADTConstraint index gTouchs gCond gCons gAss subCons gci) (lbu, cs) -> 
                  let 
                     (rBu, lc1) = instanceTS importenv lbu env gAss ts
                     lc2 = equalASENV (gAss M.\\ ts) env
                     (rBU2, subCons') = resolveGADTAssumptions importenv ts env rBu subCons 
                  in (rBU2, GADTConstraint index gTouchs gCond (gCons ++ lc1 ++ lc2) (gAss M.\\ ts M.\\ env) subCons' gci: cs)
               ) (bu, [])

residualConstraintsCheck :: Environment -> Constraints -> [TypeError]
residualConstraintsCheck env = concatMap constraintCheck
                     where
                        constraintCheck :: Constraint  ConstraintInfo -> [TypeError]
                        constraintCheck (Constraint_Inst (MonoType_Var _ v _) p _) | v `elem` M.elems env = createTypeError $ "Type of " ++ show v ++ " should be " ++  show p
                        constraintCheck c = createTypeError $ "Residual constraint " ++ show c

replacePolytype :: [Constraint ConstraintInfo] -> PolyType ConstraintInfo -> PolyType ConstraintInfo
replacePolytype [] p = p
replacePolytype (Constraint_Inst (MonoType_Var _ v _) pt _:cs) p  | var v == p = pt
                                                            | otherwise =  replacePolytype cs p
replacePolytype (_:cs) p = replacePolytype cs p

escapeVariableCheck :: Assumptions -> Environment -> TypeSignatures -> [TypeError]
escapeVariableCheck ass env ts   | null ass = []
                                 | otherwise = let 
                                          ftv = concatMap (getTypeVariablesFromPolyType . snd) $ M.filter (\(_, pt) -> pt /= PolyType_Bind "" (bind (integer2Name 0) (var $ integer2Name 0))) $ M.intersection ts env
                                       in concatMap (\v -> createTypeError $ "Variable " ++ show v ++ " is too general in " ++ show (M.intersection ts env) ) ftv

makeTypeError :: [TyVar] -> Constraint ConstraintInfo -> [TypeError]
makeTypeError _ (Constraint_Class s v _) = createTypeError ("Missing instance (" ++ s ++ " " ++ show (head v) ++ ")")
makeTypeError touchables (Constraint_Inst (MonoType_Var _ v _) _ _) | v `notElem` touchables = createTypeError ("Variable " ++ show v ++ " should not be unified")
                                                               | otherwise = []
makeTypeError _ _ = [] 

instance Show TypeError where
   show x = sortAndShowMessages [x]

topSort :: G.Vertex -> [G.Edge] -> [[G.Vertex]]
topSort n = map G.flatten . G.scc . G.buildG (0, n)

createTypeError :: Show a => a -> [TypeError]
createTypeError s = [TypeError [] [MessageOneLiner $ MessageString $ show s] [] []]

subsConstraints :: Substitution -> Constraints
subsConstraints = map (\(v, m) -> Constraint_Unify (var v) m undefined)

runFreshMRes :: FreshM a -> (a, Integer)
runFreshMRes = runIdentity . runFreshMTRes

runFreshMTRes :: Monad m => FreshMT m a -> m (a, Integer)
runFreshMTRes m = contFreshMTRes m 0

contFreshMRes :: FreshM a -> Integer -> (a, Integer)
contFreshMRes i = runIdentity . contFreshMTRes i

contFreshMTRes :: Monad m => FreshMT m a -> Integer -> m (a, Integer)
contFreshMTRes (FreshMT m) = runStateT m

left :: (a -> c) -> c -> Either a b -> c
left f _ (Left x) = f x
left _ d (Right _) = d

right :: (b -> c) -> c -> Either a b -> c
right _ d (Left _) = d
right f _ (Right x) = f x

gadtConstraintToConstraint :: GADTConstraint -> Constraint ConstraintInfo
gadtConstraintToConstraint = gadtConstraintToConstraint' [] []

gadtConstraintToConstraint' :: [TyVar] -> [Constraint ConstraintInfo] -> GADTConstraint -> Constraint ConstraintInfo
gadtConstraintToConstraint' extraT extraC g  | not (null $ gadtAssumptions g) = error ("Unresolved assumptions" ++ show g)
                                             | otherwise = Constraint_Exists (bind 
                                                  (gadtTouchables g ++ extraT)
                                                   (
                                                      map (modCi (addProperty FromGADT)) (gadtCondition g ++ extraC), 
                                                      map (modCi (addProperty FromGADT)) $ gadtImplication g ++ 
                                                         map (gadtConstraintToConstraint' [] []) (gadtSubGADTConstraints g))) (Just $ gadtConstraintInfo g)


insertGADTTouchable :: [TyVar] -> GADTConstraint -> GADTConstraint
insertGADTTouchable tyvars gadtConstraint = gadtConstraint{
                                                gadtTouchables = gadtTouchables gadtConstraint ++ tyvars
                                                }

appendGADTInfo :: [GADTConstraint] -> Constraint ConstraintInfo -> Constraint ConstraintInfo
appendGADTInfo gadtCons c = let
   ci = fromMaybe (error "No constraint info present") (getConstraintInfo c)
   maybePM = maybePatternMatch ci
   Just (v, index, _) = maybePM
   gadtConstraint = find (\gc -> caseArmIndex gc == index) gadtCons
   
   ci' = ci{
      properties = PatternMatch v index (gadtConstraintToConstraint <$> gadtConstraint) : filter isPatternMatch (properties ci)
   }
   in if isJust maybePM then setConstraintInfo ci' c else c
