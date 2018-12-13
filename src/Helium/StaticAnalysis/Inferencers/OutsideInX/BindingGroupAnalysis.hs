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

import Unbound.LocallyNameless.Fresh

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Tree as G
import Data.List
import Data.Maybe


import Debug.Trace
{-}
type Assumptions        = M.Map Name [(Name,Tp)]
type PatternAssumptions = M.Map Name Tp
type Monos              = Tps

noAssumptions :: M.Map Name a
noAssumptions = M.empty

listToAssumptions :: [(Name, Tp)] -> Assumptions
listToAssumptions list =
   foldr combine noAssumptions [ M.fromList [(n, [tuple])] | tuple@(n, _) <- list ]

combine :: Assumptions -> Assumptions -> Assumptions
combine = M.unionWith (++)

single :: Name -> Tp -> Assumptions
single n t = M.singleton n [(n,t)]

type BindingGroups = [BindingGroup]
type BindingGroup  = (PatternAssumptions, Assumptions, ConstraintSets)
type InheritedBDG  = [(Names, (Monos, Int))]

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (noAssumptions, noAssumptions, [])

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1) (e2,a2,c2) = 
   (e1 `M.union` e2, a1 `combine` a2, c1++c2)

concatBindingGroups :: BindingGroups -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup



-- |Input for binding group analysis
type InputBDG     = (Bool, Int, Int, Monos, M.Map Name TpScheme, Maybe (Assumptions, ConstraintSets), Int)
type OutputBDG    = (Assumptions, ConstraintSet, InheritedBDG, Int, Int, M.Map Name (Sigma Predicates))

performBindingGroup :: InputBDG -> BindingGroups -> OutputBDG
performBindingGroup (topLevel, currentChunk, uniqueChunk, monoTypes, typeSignatures, chunkContext, unique) groups = 
   variableDependencies 

   where   
        bindingGroupAnalysis :: BindingGroups -> BindingGroups
        bindingGroupAnalysis cs =
           let explicits = M.keys typeSignatures
               indexMap = concat (zipWith f cs [0..])
               f (env,_,_) i = [ (n,i) | n <- M.keys env, n `notElem` explicits ]
               edges    = concat (zipWith f' cs [0..])
               f' (_,ass,_) i = [ (i,j)| n <- M.keys ass, (n',j) <- indexMap, n==n' ]
               list = topSort (length cs-1) edges
           in map (concatBindingGroups . map (cs !!)) list

        chunkedBindingGroups  :: [(Int, BindingGroup)]
        chunkedBindingGroups = 
           zip [uniqueChunk..] (bindingGroupAnalysis groups) ++ 
           case chunkContext of 
              Nothing     -> []
              Just (a, c) -> [(currentChunk, (M.empty, a, c))]
        
{-      monomorphicNames :: [Name]
        monomorphicNames = 
           let initial = let f (e, a, _) = if any (`elem` ftv monoTypes) (ftv $ map snd $ concat $ M.elems a)
                                             then M.keys e
                                             else []
                         in concatMap f groups
               expand [] _       = []
               expand (n:ns) gps = let (xs, ys)  = partition p gps
                                       p (_,a,_) = n `elem` M.keys a
                                       f (e,_,_) = M.keys e
                                   in n : expand (concatMap f xs ++ ns) ys
           in expand initial groups -}
                          
        variableDependencies :: OutputBDG
        variableDependencies = 
           let (aset, cset, mt, newUnique, fm) = foldr op initial chunkedBindingGroups
           in (aset, cset, mt, uniqueChunk + length groups, newUnique, fm)

          where        
            initial = (noAssumptions, emptyTree, [], unique, M.empty)
          
            op (cnr, (e, a, c)) (aset, cset, mt, un, fm) =
               let (cset1,e'   )  = (typeSignatures !:::! e) monoTypes cinfoBindingGroupExplicitTypedBinding                
                   (cset2,a'   )  = (typeSignatures .:::. a) (cinfoBindingGroupExplicit monoTypes (M.keys e))
                   (cset3,a''  )  = (e' .===. a')            cinfoSameBindingGroup
                   
                   implicits      = zip [un..] (M.assocs e')
                   implicitsFM    = M.fromList [ (name, SigmaVar sv) | (sv, (name, _)) <- implicits ]
                   cset4          = genConstraints monoTypes cinfoGeneralize implicits                   
                   (cset5, aset') = (implicitsFM .<==. aset) cinfoBindingGroupImplicit
                                    
                   monomorphic    = not topLevel -- simplification: was 
                                                 -- any (`elem` monomorphicNames) (keysFM e) || cnr == currentChunk

                   constraintTree =
                      StrictOrder 
                         ( (if monomorphic then id else Chunk cnr)
                         $ StrictOrder
                              ( (cset1 ++ cset2 ++ cset3) .>>. Node (reverse c) )
                              (listTree cset4))
                         (cset5 .>>. cset)
               in
                  ( a'' `combine` aset'
                  , constraintTree
                  , (M.keys e, (M.elems e', if monomorphic then currentChunk else cnr)) : mt
                  , un + M.size e'
                  , implicitsFM `M.union` fm
                  ) 

findMono :: Name -> InheritedBDG -> Monos
findMono n = let p = elem n . fst
             in fst . snd . head . filter p                  

getMonos :: TypeConstraints info -> Monos
getMonos tcs = [ TVar i | tc <- tcs, i <- ftv tc ]

findCurrentChunk :: Name -> InheritedBDG -> Int
findCurrentChunk n = let p = elem n . fst
                     in snd . snd . head . filter p

-- topological sort
topSort :: G.Vertex -> [G.Edge] -> [[G.Vertex]]
topSort n = map G.flatten . G.scc . G.buildG (0, n)

-}

type Assumptions = M.Map Name TyVar
type Environment = M.Map Name TyVar

type TypeSignatures = M.Map Name (TyVar, PolyType)
type Monos = [TyVar]
type Touchables = [TyVar]
type Constraints = [Constraint]
type BindingGroup = (Environment, Assumptions, Constraints)
type Substitution = [(TyVar, MonoType)]

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (M.empty, M.empty, [])

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1) (e2,a2,c2) = 
   (e1 `M.union` e2, a1 `M.union` a2, c1++c2)

concatBindingGroups :: [BindingGroup] -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup

bindingGroupAnalysis :: (Assumptions, Constraints, TypeSignatures, Monos, Touchables, Integer) -> 
                        [BindingGroup] -> 
                        (Touchables, Monos, Assumptions, Environment, TypeSignatures, Constraints, Integer, Substitution, TypeErrors)
bindingGroupAnalysis (assumptions, constraints, typeSignatures, monos, touchables, betaUnique) groups = variableDependencies
                  where
                     bindingGroupAnalysis :: [BindingGroup] -> [BindingGroup]
                     bindingGroupAnalysis cs =
                           let 
                              explicits = M.keys typeSignatures
                              indexMap = concat (zipWith f cs [0..])
                              f (env,_,_) i = [ (n,i) | n <- M.keys env, n `notElem` explicits ]
                              edges    = concat (zipWith f' cs [0..])
                              f' (_,ass,_) i = [ (i,j)| n <- M.keys ass, (n',j) <- indexMap, n==n' ]
                              list = topSort (length cs-1) edges
                           in map (concatBindingGroups . map (cs !!)) list
                     sortedGroups = reverse (bindingGroupAnalysis groups)
                     variableDependencies = foldr op initial sortedGroups
                        where
                           instanceTS :: Integer -> Assumptions -> TypeSignatures -> (Integer, [Constraint], Touchables)
                           instanceTS bu ass ts = M.foldr combineTS (bu, [], []) $ M.intersectionWith (\a (_, t) -> (a, t)) ass ts
                              where
                                 combineTS :: (TyVar, PolyType) -> (Integer, Constraints, Touchables) -> (Integer, [Constraint], Touchables)
                                 combineTS (a, t) (bu, cs, tc) = let
                                    (t', bu') = freshen bu t
                                    in (bu', Constraint_Unify (var a) (getMonoFromPoly t') : cs, getTypeVariablesFromMonoType (getMonoFromPoly t') ++ tc)
                           instanceTSE :: Environment -> TypeSignatures -> Constraints
                           instanceTSE env1 ts = concatMap snd $ M.toList $ M.intersectionWith (\e (b, t) -> [Constraint_Unify (var b) $ getMonoFromPoly t, Constraint_Unify (var b) (var e)]) env1 ts
                           equalASENV :: Assumptions -> Environment -> Constraints
                           equalASENV ass env = M.elems $ M.intersectionWith (\a e -> Constraint_Unify (var a) (var e)) ass env
                           initial :: (Touchables, Monos, Assumptions, Environment, TypeSignatures, Constraints, Integer, Substitution, TypeErrors)
                           initial = (touchables, monos, M.empty, M.empty, typeSignatures, [], betaUnique, [], [])
                           op :: (Environment, Assumptions, Constraints) -> 
                                 (Touchables, Monos, Assumptions, Environment, TypeSignatures, Constraints, Integer, Substitution, TypeErrors) -> 
                                 (Touchables, Monos, Assumptions, Environment, TypeSignatures, Constraints, Integer, Substitution, TypeErrors) 
                           op (env1, ass1, con1) (touchs, ms, ass2, _, ts2, con2, bu, subsOrig, typeErrors) =
                              let
                                 (buR, c1, touchs1) = instanceTS bu ass1 ts2
                                 c2 = instanceTSE env1 ts2
                                 env' = env1 M.\\ ts2
                                 c3 = equalASENV (ass1 M.\\ ts2) env'
                                 
                                 assR = (ass2 M.\\ env') `M.union` ((ass1 M.\\ ts2) M.\\ env')
                                 conR = c1 ++ c2 ++ c3 ++ con1 ++ con2
                                 touchablesW = touchs ++ touchs1
                                 (solverResult, _) = runFreshM $ solve [] [] conR touchablesW
                                 te = either (\e -> [TypeError [] [MessageOneLiner $ MessageString $ show e] [] []]) (const []) solverResult
                                 (touchablesR, resiualConstraints, subs) = either (const ([], [], [])) (\sol -> (touchable sol, residual sol, substitution sol)) solverResult
                                 envR = env1
                                 tsR = traceShowId $ M.fromList $ mapMaybe (\(n, v) -> (\m -> (n, (v, PolyType_Mono [] m))) <$> lookup v subs) (M.toList $ envR M.\\ typeSignatures M.\\assR)
                                 conTS =  mapMaybe (\(n, v) -> Constraint_Unify (var v) <$> lookup v subs) (M.toList $ envR M.\\ typeSignatures)
                              in trace (unlines $ map show conR) (nub touchablesR, ms, assR, M.empty, tsR `M.union` ts2, conTS, buR, [], typeErrors ++ te)
                           
instance Show TypeError where
   show x = sortAndShowMessages [x]

cleanSubs :: [(TyVar, MonoType)] -> [(TyVar, MonoType)]
cleanSubs subs = let
   sort :: (TyVar, MonoType) -> (TyVar, MonoType) -> Ordering
   sort (v1, m1) (v2, m2) = compare v1 v2
   sorted = nub $ sortBy sort subs
   group :: [(TyVar, MonoType)] -> [(TyVar, [MonoType])]
   group = map (\l@((v, _):_) -> (v, map snd l)) . groupHelper []
      where
         groupHelper lst [] = [lst]
         groupHelper lst ((v1, m1):vs) | null lst              = groupHelper [(v1, m1)] vs
                                       | fst (head lst) == v1  = groupHelper ((v1, m1) : lst) vs
                                       | otherwise             = lst : groupHelper [(v1, m1)] vs
   grouped = group sorted
   decide :: (TyVar, [MonoType]) -> (TyVar, MonoType)
   decide (v, []) = error "Invalid substitution"
   decide (v, [m]) = (v, m)
   decide (v, [m1, m2]) = let
         sf :: MonoType -> MonoType -> MonoType
         sf (MonoType_Var v1) (MonoType_Var v2) | v1 == v = var v2
                                                | v2 == v = var v1
                                                | v1 == v2 = var v1
                                                | applySubs sorted (var v1) == applySubs sorted (var v2) = applySubs sorted (var v1)
                                                | applySubs (reverse sorted) (var v1) == applySubs (reverse sorted) (var v2) = applySubs (reverse sorted) (var v1)
                                                | otherwise = error $ "Two distinct variables " ++ show v1 ++ show v2 ++ show sorted
         sf (MonoType_Var _) m2                 = m2
         sf m1 (MonoType_Var _)                 = m1
         sf m1 m2                               | eqSubs sorted m1 m2 = applySubs sorted m2
                                                | samePattern m1 m2 =   let
                                                                           diffVars = diffVariables m1 m2
                                                                           isUniq :: TyVar -> Bool
                                                                           isUniq v = 1 == length (filter ((v==).fst) sorted)
                                                                        in if all (\(v1, v2) -> isUniq v1 && isUniq v2) diffVars then
                                                                              m1
                                                                           else error "Incompattible types"
                                                | stricter sorted m1 m2     = m1
                                                | stricter sorted m2 m1     = m2
                                                |  otherwise = error $ show "Incompatiable types" ++ show sorted ++ " - " ++ show v ++ show m1  ++ " :-: " ++ show m2


         ms' = sf m1 m2
      in (v, ms')
   decided = map decide grouped
   in decided

applySubs :: [(TyVar, MonoType)] -> MonoType -> MonoType
applySubs subs (MonoType_Var v) = fromMaybe (var v) (lookup v subs)
applySubs subs (MonoType_Con n cs) = MonoType_Con n (map (applySubs subs) cs)
applySubs subs (f :-->: a) = applySubs subs f :-->: applySubs subs a

samePattern :: MonoType -> MonoType -> Bool
samePattern (MonoType_Var _) (MonoType_Var _) = True
samePattern (MonoType_Con n1 cs1) (MonoType_Con n2 cs2) = n1 == n2 && and (zipWith samePattern cs1 cs2)
samePattern (f1 :-->: a1) (f2 :-->: a2) = samePattern f1 f2 && samePattern a1 a2
samePattern _ _ = False

stricter :: [(TyVar, MonoType)] -> MonoType -> MonoType -> Bool
stricter subs (MonoType_Var v1) (MonoType_Var v2) = filter ((v2==).fst) subs == [(v2, var v2)]
stricter subs _ (MonoType_Var v2) = True
stricter subs (f1 :-->: a1) (f2 :-->: a2) = stricter subs f1 f2 && stricter subs a1 a2
stricter subs (MonoType_Con n1 c1) (MonoType_Con n2 c2) = n1 == n2 && and (zipWith (stricter subs) c1 c2)
stricter subs _ _ = False

diffVariables :: MonoType -> MonoType -> [(TyVar, TyVar)]
diffVariables (MonoType_Var v1) (MonoType_Var v2)  | v1 == v2 = []
                                                   | otherwise = [(v1, v2)]
diffVariables (MonoType_Con _ cs1) (MonoType_Con _ cs2) = nub (concat $ zipWith diffVariables cs1 cs2) 
diffVariables (f1 :-->: a1) (f2 :-->: a2) = nub (diffVariables f1 f2 ++ diffVariables a1 a2)

eqSubs :: [(TyVar, MonoType)] -> MonoType -> MonoType -> Bool
eqSubs subs m1 m2 | applySubs subs m1 == applySubs subs m2 = True
                  | applySubs (reverse subs) m1 == applySubs subs m2 = True
                  | applySubs subs m1 == applySubs (reverse subs) m2 = True
                  | applySubs (reverse subs) m1 == applySubs (reverse subs) m2 = True
                  | otherwise = False



topSort :: G.Vertex -> [G.Edge] -> [[G.Vertex]]
topSort n = map G.flatten . G.scc . G.buildG (0, n)
                              
