module Helium.CodeGeneration.Core.Strictness.SolveOld (solveConstraints) where

-- Solving using scc/topsort. Theoretically slower than SolveNew but does not stack overflow

import qualified Data.Graph as G
import Data.List
import qualified Data.Sequence as Q
import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.IdMap
import Lvm.Core.Type

type Node = (Id, Id, [Id])

-- Second round of constraint solving, replacing variables in joins and meets
solveConstraints :: AnnotationEnvironment -> Constraints -> SolvedConstraints
solveConstraints env cs = foldl (handleId sc) emptyMap scc
    where
        -- Solve constraints
        sc = foldr handleConstraint env (S.toList cs)
        -- Create edge map and scc
        edgeMap = map (\(x, y) -> (x, x, y)) $ listFromMap $ mapMap getVariablesAnn sc
        scc = G.stronglyConnCompR edgeMap

-- Handle a single constraint, adding it to the set of solved constraints
handleConstraint :: Constraint -> SolvedConstraints -> SolvedConstraints
handleConstraint (a `Constraint` AnnVar x) sc = insertMapWith x a (join a) sc
handleConstraint _ sc = sc

-- Handle a single variable, replacing its occurences with its value
handleId :: SolvedConstraints -> SolvedConstraints -> G.SCC Node -> SolvedConstraints
handleId sc nsc (G.AcyclicSCC (a, _, _)) = insertMap a (replaceVar nsc (findMap a sc)) nsc
handleId sc nsc (G.CyclicSCC as) = unionMap nsc nsc'
    where
        -- Replace all nonrecursive annotations with value
        ans = map (\(a, _, _) -> (a, replaceVar (insertMap a S nsc) (findMap a sc))) as
        nsc' = handleRec (Q.fromList asq) (mapFromList ans)
        asq = map fst $ sortOn (\(_, a) -> length $ nub $ getVariablesAnn a) ans -- map (\(a, an) -> (a, getVariablesAnn an)) ans

handleRec :: Q.Seq Id -> SolvedConstraints -> SolvedConstraints
handleRec as sc
    | null as = sc
    | otherwise = handleRec as'' nsc
    where
        (a' Q.:< as') = Q.viewl as
        nsc = mapMapWithId (\k a -> replaceVar (mapFromList [(k, S), (a', findMap a' sc)]) a) sc
        as'' = if listFromMap sc == listFromMap nsc then as' else as' Q.|> a'
