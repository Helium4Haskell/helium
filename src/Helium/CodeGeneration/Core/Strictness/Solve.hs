module Helium.CodeGeneration.Core.Strictness.Solve (solveConstraints) where

import Helium.CodeGeneration.Core.Strictness.Analyse
import Lvm.Common.IdMap
import Lvm.Core.Type
import Data.Graph
import Data.Maybe

type Node = (Id, Id, [Id])

-- Solve a set of constraints
-- All variables have either S or L at the end
solveConstraints :: Constraints -> Constraints
solveConstraints cs = foldl (solveConstraint nodeFromVertex) cs vs
    where
        -- Turn constraints into graph
        (graph, nodeFromVertex, _) = graphFromEdges $ constraintsToGraph cs
        -- Solve order is reverse topological sor
        vs = reverse $ topSort graph

-- Turn constraints into graph
constraintsToGraph :: Constraints -> [Node]
constraintsToGraph cs = map toNode $ listFromMap $ mapMapWithId constraintToEdges cs
    where
        -- Node needs three values but id can be the same as name
        toNode (k, e) = (k, k, e)

-- Get dependencies of single constraints
constraintToEdges :: Id -> SAnn -> [Id]
constraintToEdges i (AnnVar a)   = [a | i /= a] -- Avoid constraints of type a == a
constraintToEdges i (Join s1 s2) = constraintToEdges i s1 ++ constraintToEdges i s2
constraintToEdges i (Meet s1 s2) = constraintToEdges i s1 ++ constraintToEdges i s2
constraintToEdges _ _            = []

-- Solve a single constraint
solveConstraint :: (Vertex -> Node) -> Constraints -> Vertex -> Constraints
solveConstraint nodeFromVertex c v = updateMap node new c
    where
        -- Get node corresponding to vertex
        (node, _, _) = nodeFromVertex v
        -- Get current value and replace with earlier solved annotations
        new = replaceVar c $ findMap node c

-- Replace solved annotation variables
replaceVar :: Constraints -> SAnn -> SAnn
replaceVar cs (AnnVar x) = fromMaybe L (lookupMap x cs)
replaceVar cs (Meet x y) = meet (replaceVar cs x) (replaceVar cs y)
replaceVar cs (Join x y) = join (replaceVar cs x) (replaceVar cs y)
replaceVar _  x          = x