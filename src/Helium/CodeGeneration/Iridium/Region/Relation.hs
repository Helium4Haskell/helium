module Helium.CodeGeneration.Iridium.Region.Relation
  ( RegionVar(..)
  , RelationConstraint(..)
  , Relation
  , outlives
  , instantiateRelationConstraints
  , instantiateRelationConstraint
  , emptyRelation
  , relationFromConstraints
  )
  where

import Data.Bits
import Data.Maybe
import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Helium.CodeGeneration.Iridium.Region.Sort

import Debug.Trace

newtype RegionVar = RegionVar Int deriving (Eq, Ord)
newtype Vertex = Vertex Int deriving (Eq, Show)
newtype Relation = Relation (IntMap (IntSet)) -- Map from vertex to the vertices it outlives

instance Show RegionVar where
  show (RegionVar idx) = 'ρ' : showSubscript idx

emptyRelation :: Relation
emptyRelation = Relation IntMap.empty

-- Polymorphic region variables may only be used in constraints if both arguments
-- are polymorphic on the same type, or if only the left argument is polymorphic
data RelationConstraint
  = Outlives !RegionVar !RegionVar
  deriving (Eq, Ord)

instantiateRelationConstraints :: (RegionVar -> Maybe [RegionVar]) -> [RelationConstraint] -> [RelationConstraint]
instantiateRelationConstraints f constraints = constraints >>= instantiateRelationConstraint f

instantiateRelationConstraint :: (RegionVar -> Maybe [RegionVar]) -> RelationConstraint -> [RelationConstraint]
instantiateRelationConstraint f c@(Outlives r1 r2) = case f r1  of
  Nothing -> [c]
  Just rs1 -> case f r2 of
    Nothing ->
      -- Only the left argument is polymorphic.
      map (\r1' -> Outlives r1' r2) rs1
    Just rs2 ->
      -- Both arguments are polymorphic. Extend element-wise
      zipWith Outlives rs1 rs2

instance Show RelationConstraint where
  show (Outlives r1 r2) = show r1 ++ " ≥ " ++ show r2
  showList constraints = (("⟦ " ++ intercalate ", " (map show constraints) ++ " ⟧") ++)

substitute :: IntMap Int -> RegionVar -> RegionVar
substitute mapping (RegionVar r1) = case IntMap.lookup r1 mapping of
  Just r2 -> RegionVar r2
  Nothing -> RegionVar r1

relationFromConstraints :: IntSet -> [RelationConstraint] -> (IntMap Int, Relation)
relationFromConstraints allVertices constraints = transitiveClosure allVertices (Relation graph)
  where
    graph = IntMap.fromAscList $ map fromGroup $ groupBy (\(Outlives r1 _) (Outlives r2 _) -> r1 == r2) $ sort constraints
    fromGroup :: [RelationConstraint] -> (Int, IntSet)
    fromGroup cs@(Outlives (RegionVar r1) _ : _) = (r1, IntSet.fromAscList $ map (\(Outlives _ (RegionVar r2)) -> r2) cs)

constraintsFromRelation :: Relation -> [RelationConstraint]
constraintsFromRelation (Relation graph) = IntMap.foldrWithKey constraintsForVertex [] graph
  where
    constraintsForVertex :: Int -> IntSet -> [RelationConstraint] -> [RelationConstraint]
    constraintsForVertex r1 set accum = map (\r2 -> Outlives (RegionVar r1) (RegionVar r2)) (IntSet.toList set) ++ accum

instance Show Relation where
  show rel = show (constraintsFromRelation rel)

outlives :: Relation -> RegionVar -> RegionVar -> Bool
outlives (Relation graph) (RegionVar r1) (RegionVar r2)
  | r1 == r2 = True
  | otherwise = case IntMap.lookup r1 graph of
    Nothing -> False
    Just rs -> r2 `IntSet.member` rs

newtype Component = Component { unComponent :: Int } deriving (Eq, Show)

data TCVertexState = TCVertexState 
  { vsComponent :: !(Maybe Component)
  , vsRoot :: !Vertex
  , vsTimeStart :: !Int
  }

data TCState = TCState 
  { tcVertices :: !(IntMap TCVertexState)
  , tcComponents :: !(IntMap IntSet)
  , tcVStack :: ![Vertex]
  , tcCStack :: ![Component]
  , tcCStackHeight :: !Int
  , tcFreshComponent :: !Int
  , tcFreshTraversalIndex :: !Int
  }

tcSetVertex :: Vertex -> TCVertexState -> TCState -> TCState
tcSetVertex (Vertex v) vertexState state = state{ tcVertices = IntMap.insert v vertexState $ tcVertices state }

tcUpdateVertex :: Vertex -> (TCVertexState -> TCVertexState) -> TCState -> TCState
tcUpdateVertex (Vertex v) f state = state{ tcVertices =
    IntMap.insertWith (const f) v (error "tcUpdateVertex: Vertex was not yet stored in the map, cannot update it.") $ tcVertices state
  }

tcGetVertex :: Vertex -> TCState -> Maybe TCVertexState
tcGetVertex (Vertex v) state = IntMap.lookup v $ tcVertices state

transitiveClosure :: IntSet -> Relation -> (IntMap Int, Relation)
transitiveClosure allVertices (Relation graph) =
  ( IntMap.map
      (unComponent . fromMaybe (error "transitiveClosure: vertex should have been placed in a vertex, got Nothing instead.") . vsComponent)
      $ tcVertices finalState
  , Relation $ tcComponents finalState
  )
  where
    initialState :: TCState
    initialState = TCState IntMap.empty IntMap.empty [] [] 0 0 0

    finalState = IntSet.foldr' visitIfNew initialState allVertices

    predecessors :: Vertex -> IntSet
    predecessors (Vertex v) = case IntMap.lookup v graph of
      Nothing -> IntSet.empty
      Just set -> set

    visitIfNew :: Int -> TCState -> TCState
    visitIfNew v state = case tcGetVertex (Vertex v) state of
      Nothing -> snd $ visit (Vertex v) state
      Just _ -> state

    visit :: Vertex -> TCState -> (TCVertexState, TCState)
    visit v state =
      let
        -- Root(v) := v; Comp(v) := Nil; push(v, vstack);
        -- SavedHeight(v) := height(cstack);
        state1 = tcSetVertex v (TCVertexState Nothing v (tcFreshTraversalIndex state)) state
        state2 = state1{ tcVStack = v : tcVStack state1, tcFreshTraversalIndex = tcFreshTraversalIndex state + 1 }
        savedHeight = tcCStackHeight state

        -- for each vertex w such that (w, v) ∈ E do
        state3 = IntSet.foldr' (\w -> visitEdge v (Vertex w)) state2 $ predecessors v

        final = fromMaybe (error "transitiveClosure: couldn't find nodes") $ tcGetVertex v state3
      in
        if vsRoot final /= v then (final, state3)
        else
          let
            c = tcFreshComponent state3
            -- sort the components in cstack between SavedHeight(v) and height(cstack) into a topological order and eliminate duplicates;
            count = tcCStackHeight state3 - savedHeight
            (components, rest) = splitAt count $ tcCStack state3
            components' = topologicalSort (tcComponents state3) components

            {-
            while height(cstack)  ̸= SavedHeight(v) do begin
              X := pop(cstack);
              if X \notin Succ(C) then Succ(C) := Succ(C)∪{X}∪Succ(X);
            end;
            -}
            unionComponent :: IntSet -> Component -> IntSet
            unionComponent p (Component x)
              | x `IntSet.member` p = p
              | otherwise = IntSet.insert x $ IntSet.union p predsX
              where
                predsX = fromMaybe IntSet.empty $ IntMap.lookup x $ tcComponents state3
            preds = foldl unionComponent IntSet.empty components'

            (vertices, vRest) = span (v /=) $ tcVStack state3
            state4 = state3{ tcFreshComponent = c + 1, tcCStack = rest, tcCStackHeight = savedHeight, tcVStack = tail vRest, tcComponents = IntMap.insert c preds $ tcComponents state3 }

            {-
            repeat
              w := pop(vstack); Comp(w) := C;
            until w = v
            -}
            setComponent :: Vertex -> TCState -> TCState
            setComponent w = tcUpdateVertex w (\vertex -> vertex{ vsComponent = Just $ Component c } )

          in (final{ vsComponent = Just $ Component c }, foldr setComponent state4 (v : vertices))
    
    {-
    if w /= v then begin
      if w is not already visited then stack_tc(w);
      if Comp(w)=Nil then Root(v):= min(Root(v),Root(w))
      else if (v, w) is not a forward edge then
      push(Comp(w), cstack);
    end
    -}
    visitEdge :: Vertex -> Vertex -> TCState -> TCState
    visitEdge v w state
      | v == w = state
      | otherwise = {- trace ("EDGE " ++ show v ++ " >= " ++ show w) -} state2
      where
        (vertex, state1) = case tcGetVertex w state of
          Nothing -> visit w state
          Just vertex ->
            -- Edge may be a forward edge
            -- We do not check for forward edges, which the original STACK_TC does. This may cause that a component is pushed multiple times to cstack.
            -- Duplicates are removed in topologicalSort, so this does not create problems with correctness.
            (vertex, state)
        state2 = case vertex of
          TCVertexState Nothing r1 _ -> tcUpdateVertex v (\(TCVertexState comp r2 traversalIndex) -> TCVertexState comp (minVertex state1 r1 r2) traversalIndex) state1
          TCVertexState (Just c) _ _  -> state1{ tcCStack = c : tcCStack state1, tcCStackHeight = tcCStackHeight state1 + 1 }

    minVertex :: TCState -> Vertex -> Vertex -> Vertex
    minVertex state v1 v2
      | t1 < t2 = v1
      | otherwise = v2
      where
        TCVertexState _ _ t1 = fromMaybe (error "minVertex: vertex not found") $ tcGetVertex v1 state
        TCVertexState _ _ t2 = fromMaybe (error "minVertex: vertex not found") $ tcGetVertex v2 state

topologicalSort :: IntMap IntSet -> [Component] -> [Component]
topologicalSort graph cs = snd $ foldr (\(Component c) -> topologicalSort' graph c) (IntSet.empty, []) cs

topologicalSort' :: IntMap IntSet -> Int -> (IntSet, [Component]) -> (IntSet, [Component])
topologicalSort' graph c (visited, accum)
  | c `IntSet.member` visited = (visited, accum)
  | otherwise = (visited'', Component c : accum')
  where
    preds = fromMaybe IntSet.empty $ IntMap.lookup c graph
    visited' = IntSet.insert c visited
    (visited'', accum') = IntSet.foldr (topologicalSort' graph) (visited', accum) preds
