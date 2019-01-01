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

type Assumptions = M.Map Name [(Name, TyVar)]
type Environment = M.Map Name TyVar

type TypeSignatures = M.Map Name (TyVar, PolyType)
type Monos = [TyVar]
type Touchables = [(Maybe Name, TyVar)]
type Constraints = [Constraint]
type BindingGroup = (Environment, Assumptions, Constraints, Substitution)
type Substitution = [(TyVar, MonoType)]
type InheritedBDG  = [(Names, Monos)]


combineAssumptions :: Assumptions -> Assumptions -> Assumptions
combineAssumptions = M.unionWith (++)

emptyBindingGroup2 :: BindingGroup2
emptyBindingGroup2 = 
   (M.empty, M.empty, [])

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (M.empty, M.empty, [], [])

combineBindingGroup2 :: BindingGroup2 -> BindingGroup2 -> BindingGroup2
combineBindingGroup2 (e1,a1,c1) (e2,a2,c2) = 
   (e1 `M.union` e2, a1 `combineAssumptions` a2, c1++c2)

concatBindingGroups2 :: [BindingGroup2] -> BindingGroup2
concatBindingGroups2 = foldr combineBindingGroup2 emptyBindingGroup2

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1, s1) (e2,a2,c2, s2) = 
   (e1 `M.union` e2, a1 `combineAssumptions` a2, c1++c2, s1 ++ s2)

concatBindingGroups :: [BindingGroup] -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup

type BindingGroup2 = (Environment, Assumptions, Constraints)

bindingGroupAnalysis2 :: (Bool, TypeSignatures, Monos, Touchables, Maybe (Assumptions, Constraints, Substitution), Integer) -> 
                        
   
   
   
   
   
   
   [BindingGroup] -> 
                       
      
      
      
      
      (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG)
bindingGroupAnalysis2 input@(isTopLevel, typeSignatures, monos, touchables, body, betaUnique) groups = --trace ("Variable dependencies" ++ show variableDependencies) 
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
                              (map (concatBindingGroups . map (cs !!)) list) ++ (
                                 case body of
                                    Nothing -> []
                                    Just (a, c, s) -> [(M.empty, a, c, s)]
                                 )
                     sortedGroups = bindingGroupAnalysis groups
                     variableDependencies = foldr op initial sortedGroups
                        where
                           instanceTS :: Integer -> Assumptions -> TypeSignatures -> (Integer, [Constraint], Touchables)
                           instanceTS bu ass ts = trace "InstanceTS: " $ traceShowId $ foldr combineTS (bu, [], []) $ concat $ M.elems $ M.intersectionWith (\a (_, t) -> [(a', t) | (_, a') <- a]) ass ts
                              where
                                 combineTS :: (TyVar, PolyType) -> (Integer, Constraints, Touchables) -> (Integer, [Constraint], Touchables)
                                 combineTS (a, t) (bu, cs, tc) = let
                                    (t', bu') = snd $ trace "FreshenWithMapping" traceShowId $ freshenWithMapping (map (\x -> (name2Integer x, name2Integer x)) monos) bu t
                                    in (bu', Constraint_Unify (var a) (getMonoFromPoly t') : cs, map (\x -> (Nothing ,x)) (getTypeVariablesFromMonoType (getMonoFromPoly t')) ++ tc)
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
                                 sTouchables = map snd (touchs ++ touchables ++ touchs1)
                                 ((solverResult, _), bu1) = contFreshMRes (solve sAxioms sGiven sWanted sTouchables) sBu

                                 {- Gathering -}
                                 (bu2, c1, touchs1) = instanceTS bu1 ass1 (trace "Input" $ traceShowId resTypeSignatures)
                                 c2 = instanceTSE env1 resTypeSignatures
                                 env' = env1 M.\\ resTypeSignatures
                                 c3 = equalASENV (ass1 M.\\ resTypeSignatures) env'
                                 c4 = concatMap (\(a', e) -> [Constraint_Unify (var a) (var e) | (_, a) <- a']) $ M.elems $ M.intersectionWith (,) ass2 env'
                                 (resBetaUnique, c5, touchs2) = instanceTS bu2 ass2 resTypeSignatures
                                 --(bu2, c4) = foldr (\(a, e) (b, cs)-> (b, [Constraint_Unify (var e) (var a') | (_, a') <- a ] ++ cs)) (bu1, []) $ M.intersectionWith (,) ass2 env'
                                
                                 {- Results -}
                                 resTouchables = touchs2 ++ touchs1 ++ map (\x -> (Nothing, x)) (right touchable [] solverResult)
                                 resAssumptions = ((ass1 M.\\ resTypeSignatures) M.\\ env') `combineAssumptions` (ass2 M.\\ env')

                                 resTypeSignatures | isTopLevel = ts2 `M.union` M.fromList (mapMaybe (\(n, v) -> (\m -> (n, (v, PolyType_Mono [] m))) <$> lookup v resSubstitution) (M.toList env1))
                                                   | otherwise =  ts2
                                 resConstraints = con2 ++ right residual [] solverResult ++ c1 ++ c2 ++ c3 ++ c4 ++ c5
                                 resSubstitution = right substitution [] solverResult
                                 resTypeErrors = left makeTypeError [] solverResult ++ typeErrors
                                 resInheritedBDG = (M.keys env1, M.elems env') : iBDG
                              in trace (showBG g) $ traceCShow showBGR (resTouchables, resAssumptions, resTypeSignatures, resConstraints, resBetaUnique, resSubstitution, resTypeErrors, resInheritedBDG)

                              {-
                              let
                                 (buR1, c1, touchs1) = instanceTS bu ass1 ts2
                                 c2 = instanceTSE env1 ts2
                                 env' = env1 M.\\ ts2
                                 c3 = equalASENV (ass1 M.\\ ts2) env'
                                 (buR2, c4) = foldr (\(a, e) (b, cs)-> let 
                                       t = 3
                                    in (b, [Constraint_Unify (var e) (var a') | (_, a') <- a ] ++ cs)) (buR1, []) $ M.intersectionWith (,) ass2 env'
                                 assR = ((ass1 M.\\ ts2) M.\\ env') `combineAssumptions` (ass2 M.\\ env')
                                 conR = c1 ++ c2 ++ c3 ++ c4 ++ con1
                                 touchablesW = touchs ++ touchs1
                                 (solverResult, _) = runFreshM $ solve [] [] conR $ map snd touchablesW
                                 te = either (\e -> [TypeError [] [MessageOneLiner $ MessageString $ show e] [] []]) (const []) solverResult
                                 (touchablesR, resiualConstraints, subs) = either (const (touchablesW, [], [])) (\sol -> (addTouchables (touchable sol) touchablesW, residual sol, substitution sol)) solverResult
                                 envR = traceShowId env1
                                 tsR = if not isTopLevel then M.empty else M.fromList $ mapMaybe (\(n, v) -> (\m -> (n, (v, PolyType_Mono [] m))) <$> lookup v subs) (M.toList $ envR M.\\ typeSignatures M.\\ assR)
                                 conTS = if not isTopLevel then [] else mapMaybe (\(n, v) -> Constraint_Unify (var v) <$> lookup v subs) (M.toList $ envR M.\\ typeSignatures)
                              in --trace "ConR" $ trace (unlines $ map show constraints)
                                 --trace ("env\n" ++ (unlines $ map show $ M.toList env1)) $ 
                                 --trace ("env'\n" ++ (unlines $ map show $ M.toList env')) $ 
                                 --trace ("ass\n" ++ (unlines $ map show $ M.toList assR)) $
                                 --trace ("ass1\n" ++ (unlines $ map show $ M.toList ass1)) $
                                 --trace ("ass2\n" ++ (unlines $ map show $ M.toList ass2)) $
                                 --trace ("subs\n" ++ (unlines $ map show subs)) $
                                 --trace ("touchables\n" ++ (unlines $ map show touchablesR)) $
                                 --trace (unlines $ map show conR)
                                 trace (showBG g) (touchablesR, assR, tsR `M.union` ts2, conR ++ con2, buR2, nub $ subs ++ subsOrig, typeErrors ++ te, iBDG) --(M.keys env1, M.elems env') : mt)
                           -}
addTouchables :: [TyVar] -> Touchables -> Touchables
addTouchables [] touchs = touchs
addTouchables (t:ts) touchs   | t `elem` map snd touchs = addTouchables ts touchs
                              | otherwise = (Nothing, t) : addTouchables ts touchs     

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

getMonos :: [Constraint] -> Monos
getMonos = concatMap fv

findMono :: Name -> InheritedBDG -> Monos
findMono n xs = 
            let 
               p = elem n . fst
               shead (x:_) = snd x
               shead [] = []
            in shead $ filter p xs

traceCShow :: (a -> String) -> a -> a
traceCShow s x = trace (s x) x
traceCShow s x = x

showBG :: (Environment, Assumptions, Constraints, Substitution) -> String
showBG (env, ass, cons, subs) = unlines [
        "BG(",
        "\tEnv: " ++ show env,
        "\tAss: " ++ show ass,
        "\tCon: " ++ show cons,
        "\tSub: " ++ show subs,
        ")"
    ]
    --(Bool, TypeSignatures, Monos, Touchables, Maybe (Assumptions, Constraints, Substitution), Integer)
-- showIBG :: (Bool, Assumptions, Constraints, TypeSignatures, Monos, Touchables, Integer) -> String
showIBG ::    (Bool, TypeSignatures, Monos, Touchables, Maybe (Assumptions, Constraints, Substitution), Integer) -> String
showIBG (tl, ts, monos, touchables, group, bu) = unlines $ "IBG(" : map ("\t" ++) [
        --"TypeSignatures: " ++ show ts,
        "Monos: " ++ show monos,
        "Touchables: " ++ show touchables,
        "Group" ++ maybe "" showBG ((\(x, y, z) -> (M.empty, x, y, z)) <$> group),
        "Beta unique: " ++ show bu
    ] ++ [")"]

showBGR :: (Touchables, Assumptions, TypeSignatures, Constraints, Integer, Substitution, TypeErrors, InheritedBDG) -> String
showBGR (touchables, ass, ts, cons, bu, subs, te, iBDG) = unlines $ "BGR(" : map ("\t" ++) [
        "Subs: \n" ++ unlines (map (\c -> "\t\t" ++ show c) subs),
        "Touchables: " ++ show touchables,
        "Assumptions: " ++ show ass,
        "TypeSignatures: " ++ show ts,
        "Constraints: \n" ++ unlines (map (\c -> "\t\t" ++ show c) cons),
        "BetaUnique: " ++ show bu,
        "TypErrors: " ++ show te,
        "Subs: " ++ show (nub subs),
        "Inherited BDG: " ++ show iBDG
    ] ++ [")", "", "-----------------------------------------", ""]


type InputBDG = (Bool, Constraints, Assumptions, Environment, TypeSignatures, Touchables, Integer)
type OutputBDG = (Substitution, TypeSignatures, Constraints, Touchables, TypeErrors, Integer)


bindingGroupAnalysis :: InputBDG -> [BindingGroup] -> OutputBDG
bindingGroupAnalysis t@(toplevel, bodyConstraints, bodyAssumptions, bodyEnvironment, typeSignatures, inTouchables, betaUnique) groups = traceShow sortedGroups $ traceShow typeSignatures $ traceShow bodyEnvironment variableDependencies
   where
      sortBindingGroups :: [BindingGroup] -> [BindingGroup]
      sortBindingGroups cs =
            let 
               explicits = M.keys typeSignatures
               indexMap = concat (zipWith f cs [0..])
               f (env,_,_, _) i = [ (n,i) | n <- M.keys env, n `notElem` explicits ]
               edges    = concat (zipWith f' cs [0..])
               f' (_,ass,_, _) i = [ (i,j)| n <- M.keys ass, (n',j) <- indexMap, n==n' ]
               list = topSort (length cs-1) edges
            in reverse $ map (concatBindingGroups . map (cs !!)) list
      sortedGroups = sortBindingGroups groups
      variableDependencies = foldr op initial sortedGroups
      initial :: OutputBDG
      initial = ([], typeSignatures, [], inTouchables, [], betaUnique)
      op :: BindingGroup -> OutputBDG -> OutputBDG
      op g@(gEnv, gAss, gCon, gSubs) i@(subs, typeSigs, resConstraints, resTouchables, resTypeErrors, bu) =
         let
            {- Gather new constraints -}
            bgTouchables = map snd resTouchables
            bgConstraints = subsConstraints gSubs ++ subsConstraints subs ++ gCon
            {- Solve results -} 
            ((solverResult, _), resultBetaUnique) = traceShowId $ contFreshMRes (solve [] [] bgConstraints bgTouchables) bu
            solverTouchables = map (\x -> (Nothing, x)) $ map integer2Name [bu..resultBetaUnique - 1]
            {- Construct results -}
            resultSubs = right substitution [] solverResult
            resultTypeSigs = typeSigs
            resultResConstraints = right residual [] solverResult
            resultResTouchables = solverTouchables ++ map (\x -> (Nothing, x)) (right touchable [] solverResult)
            resultResTypeErrors = left makeTypeError [] solverResult ++ resTypeErrors
         in traceShow bodyEnvironment (resultSubs, resultTypeSigs, resultResConstraints, resultResTouchables, resultResTypeErrors, resultBetaUnique)


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
