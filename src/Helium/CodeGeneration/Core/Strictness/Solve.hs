module Helium.CodeGeneration.Core.Strictness.Solve (solveConstraints) where

import Helium.CodeGeneration.Core.Strictness.Analyse
import Lvm.Common.IdMap
import Lvm.Core.Type
import Data.Graph

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
constraintsToGraph cs = map toNode $ listFromMap $ mapMap constraintToEdges cs
    where
        -- Node needs three values but id can be the same as name
        toNode (k, e) = (k, k, e)

-- Get dependencies of single constraints
constraintToEdges :: SAnn -> [Id]
constraintToEdges (AnnVar a)   = [a]
constraintToEdges (Join s1 s2) = constraintToEdges s1 ++ constraintToEdges s2
constraintToEdges (Meet s1 s2) = constraintToEdges s1 ++ constraintToEdges s2
constraintToEdges _            = []

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
replaceVar cs (AnnVar x) = findMap x cs -- Variable should be solved because of order
replaceVar cs (Meet x y) = meet (replaceVar cs x) (replaceVar cs y)
replaceVar cs (Join x y) = join (replaceVar cs x) (replaceVar cs y)
replaceVar _  x          = x