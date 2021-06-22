module Helium.CodeGeneration.Core.Strictness.Solve (solveConstraints) where

import Data.Graph
import qualified Data.Map as M
import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.IdMap
import Lvm.Core.Type

type EdgeMap = M.Map SAnn [SAnn]
type Node a = (a, a, [a])

-- First round of constraint solving, using the constraint set
solveConstraints' :: Constraints -> SolvedConstraints
solveConstraints' cs = foldl (handleAnn nodeFromVertex) emptyMap ts
    where
        -- Create edges, graph and topological sort
        es = M.elems $ M.mapWithKey (\x y -> (x, x, y)) $ constraintsToEdges (S.toList cs) M.empty
        (graph, nodeFromVertex, _) = graphFromEdges es
        ts = topSort graph

-- Second round of constraint solving, replacing variables in joins and meets
solveConstraints :: Constraints -> SolvedConstraints
solveConstraints cs = foldr (handleId nodeFromVertex) sc ts
    where
        -- Solve constraints
        sc = solveConstraints' cs
        -- Create graph based on variables
        es = map (\(x, y) -> (x, x, y)) $ listFromMap $ mapMap getVariablesAnn sc
        (graph, nodeFromVertex, _) = graphFromEdges es
        ts = topSort graph

-- Handle a single annotation, adding it to the set of solved constraints
handleAnn :: (Vertex -> Node SAnn) -> SolvedConstraints -> Vertex -> SolvedConstraints
handleAnn nodeFromVertex sc v = foldr f sc es
    where
        -- Get node and neighbours
        (n, _, es) = nodeFromVertex v
        -- Update map of solved values with new information
        f (AnnVar x) y = case lookupMap x y of
            Nothing -> insertMap x n y
            Just z  -> updateMap x (join n z) y
        -- TODO: what if constraint was not put on variable?
        f x y = y

-- Handle a single variable, replacing its occurences with its value
handleId :: (Vertex -> Node Id) -> Vertex -> SolvedConstraints -> SolvedConstraints
handleId nodeFromVertex v sc = updateMap n (replaceVar sc (findMap n sc)) sc 
    where
        (n, _, _) = nodeFromVertex v

-- Turn list of constraints into a map of edges, drawing edges from the left to right parts of constraints
constraintsToEdges :: [Constraint] -> EdgeMap -> EdgeMap
constraintsToEdges []                    es = es
constraintsToEdges (x `Constraint` y:cs) es = case M.lookup x es' of
    Nothing -> M.insert x [y]   es'
    Just z  -> M.insert x (y:z) es'
    where
        es' = constraintsToEdges cs es
