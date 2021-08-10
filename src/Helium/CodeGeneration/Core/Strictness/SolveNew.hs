module Helium.CodeGeneration.Core.Strictness.SolveNew (solveConstraints) where

-- Solving without graph, runs into stack overflow on Prelude (big recursion?)

import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Type

-- Second round of constraint solving, replacing variables in joins and meets
solveConstraints :: AnnotationEnvironment -> Constraints -> SolvedConstraints
solveConstraints env cs = foldr (\a sc' -> uncurry (updateMap a) $ solve (findMap a sc') a emptySet sc') sc z
    where
        -- Solve constraints
        sc = foldr handleConstraint env (S.toList cs)
        z = map fst $ listFromMap sc

-- Handle a single constraint, adding it to the set of solved constraints
handleConstraint :: Constraint -> SolvedConstraints -> SolvedConstraints
handleConstraint (a `Constraint` AnnVar x) sc = insertMapWith x a (join a) sc
handleConstraint _ sc = sc

solve :: SAnn -> Id -> IdSet -> SolvedConstraints -> (SAnn, SolvedConstraints)
solve (AnnVar x) i r sc
    | i == x = (S, sc)
    | elemSet x r = solve (findMap x sc) i r sc
    | elemMap x sc = (a, updateMap x a sc')
        where
            (a, sc') = solve (findMap x sc) x (insertSet x r) sc
solve (Join x y) i r sc = (join a1 a2, sc2)
    where
        (a1, sc1) = solve x i r sc
        (a2, sc2) = solve y i r sc1
solve (Meet x y) i r sc = (meet a1 a2, sc2)
    where
        (a1, sc1) = solve x i r sc
        (a2, sc2) = solve y i r sc1
solve x _ _ sc = (x, sc)
