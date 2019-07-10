module Helium.CodeGeneration.Iridium.Region.Relation
  ( RegionVar(..)
  , regionGlobal
  , RelationConstraint(..)
  , Relation
  , outlives
  , instantiateRelationConstraints
  , instantiateRelationConstraint
  , emptyRelation
  , relationFromTransitiveConstraints
  , relationFromConstraints
  , relationToConstraints
  , relationUnion
  , relationDecrementScope
  , relationDFS
  , relationDFS'
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

newtype RegionVar = RegionVar { unRegionVar :: Int } deriving (Eq, Ord)
newtype Vertex = Vertex Int deriving (Eq, Show)

-- Map from vertex x to the vertices y such that y outlives x
-- Example in pseudo code:
-- Relation { 1 => {2, 3}, 2 => {3} }
-- Corresponds to the constraints:
-- r_2 outlives r_1
-- r_3 outlives r_1
-- r_3 outlives r_2
newtype Relation = Relation (IntMap (IntSet))

instance IndexVariable RegionVar where
  variableToInt (RegionVar i) = i
  variableFromInt i = RegionVar i

instance Show RegionVar where
  show (RegionVar 0) = "ρ_global"
  show r = 'ρ' : showIndexVariable r

regionGlobal :: RegionVar
regionGlobal = RegionVar 0

emptyRelation :: Relation
emptyRelation = Relation IntMap.empty

-- Polymorphic region variables may only be used in constraints if both arguments
-- are polymorphic on the same type, or if only the left argument is polymorphic
data RelationConstraint
  = Outlives !RegionVar !RegionVar
  deriving (Eq)

instance Ord RelationConstraint where
  Outlives r1 r2 <= Outlives r1' r2' = r2 < r2' || (r2 == r2' && r1 <= r1')

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

substitute :: IntMap RegionVar -> RegionVar -> RegionVar
substitute mapping (RegionVar r1) = case IntMap.lookup r1 mapping of
  Just r2 -> r2
  Nothing -> RegionVar r1

graphFromConstraints :: [RelationConstraint] -> IntMap IntSet
graphFromConstraints constraints = IntMap.fromList $ map fromGroup $ groupBy (\(Outlives _ r1) (Outlives _ r2) -> r1 == r2) $ sort constraints
  where
    fromGroup :: [RelationConstraint] -> (Int, IntSet)
    fromGroup cs@(Outlives _ (RegionVar r1) : _) = (r1, IntSet.fromAscList $ map (\(Outlives (RegionVar r2) _) -> r2) cs)

relationFromTransitiveConstraints :: [RelationConstraint] -> Relation
relationFromTransitiveConstraints = Relation . graphFromConstraints

relationFromConstraints :: Int -> Int -> [RegionVar] -> [RelationConstraint] -> (IntMap RegionVar, Relation, Int)
relationFromConstraints lambdaBound regionCount externalRegions constraints = transitiveClosure lambdaBound regionCount externalRegions (Relation graph)
  where
    graph = graphFromConstraints constraints

relationFoldr :: (RegionVar -> RegionVar -> a -> a) -> a -> Relation -> a
relationFoldr f init (Relation graph) = IntMap.foldrWithKey (\r1 r2s a -> IntSet.foldr (\r2 -> f (RegionVar r1) (RegionVar r2)) a r2s) init graph

relationToConstraints :: Relation -> [RelationConstraint]
relationToConstraints = relationFoldr (\r1 r2 -> (Outlives r2 r1 :)) []

instance Show Relation where
  show rel = show (relationToConstraints rel)

outlives :: Relation -> RegionVar -> RegionVar -> Bool
outlives (Relation graph) (RegionVar r1) (RegionVar r2)
  | r1 == r2 = True
  | otherwise = case IntMap.lookup r2 graph of
    Nothing -> False
    Just rs -> r1 `IntSet.member` rs

newtype Component = Component { unComponent :: Int } deriving (Eq, Ord, Show)

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

transitiveClosure :: Int -> Int -> [RegionVar] -> Relation -> (IntMap RegionVar, Relation, Int)
transitiveClosure lambdaBound internalCount externalRegions (Relation graph) =
  ( IntMap.map
      (RegionVar . unComponent . fromMaybe (error "transitiveClosure: vertex should have been placed in a component, got Nothing instead.") . vsComponent)
      $ tcVertices finalState
  , Relation $ tcComponents finalState
  , tcFreshComponent $ finalState
  )
  where
    initialState :: TCState
    initialState = TCState IntMap.empty IntMap.empty [] [] 0 0 0

    finalState = foldr visitIfNew initialState $ map (variableFromIndices lambdaBound) [0..internalCount] ++ externalRegions

    successors :: Vertex -> IntSet
    successors (Vertex v) = case IntMap.lookup v graph of
      Nothing -> IntSet.empty
      Just set -> set

    visitIfNew :: RegionVar -> TCState -> TCState
    visitIfNew (RegionVar v) state = case tcGetVertex (Vertex v) state of
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

        -- for each vertex w such that (v, w) ∈ E (thus w outlives v) do
        state3 = IntSet.foldr' (\w -> visitEdge v (Vertex w)) state2 $ successors v

        final = fromMaybe (error "transitiveClosure: couldn't find nodes") $ tcGetVertex v state3
      in
        if vsRoot final /= v then (final, state3)
        else
          let
            (vertices', vRest') = span (v /=) $ tcVStack state3
            vertices = v : vertices'
            vRest = tail vRest'
            external = filter notTouchable vertices
            (c@(Component cIndex), freshComponent) = case external of
              [] ->
                let RegionVar r = variableFromIndices lambdaBound $ tcFreshComponent state3
                in (Component r, tcFreshComponent state3 + 1)
              [Vertex c] -> (Component c, tcFreshComponent state3)
              _ -> error "relationFromConstraints: Illegal constraints. A strongly connected component was found with multiple external region variables"

            -- sort the components in cstack between SavedHeight(v) and height(cstack) into a topological order and eliminate duplicates;
            count = tcCStackHeight state3 - savedHeight
            (components, rest) = splitAt count $ tcCStack state3
            components' = map head $ group $ sort components

            {-
            while height(cstack)  ̸= SavedHeight(v) do begin
              X := pop(cstack);
              if X \notin Succ(C) then Succ(C) := Succ(C)∪{X}∪Succ(X);
            end;
            -}
            unionComponent :: Component -> IntSet -> IntSet
            unionComponent (Component x) p
              | x `IntSet.member` p = p
              | otherwise = IntSet.insert x $ IntSet.union p predsX
              where
                predsX = fromMaybe IntSet.empty $ IntMap.lookup x $ tcComponents state3
            preds = foldr unionComponent IntSet.empty components'

            state4 = state3{ tcFreshComponent = freshComponent, tcCStack = rest, tcCStackHeight = savedHeight, tcVStack = vRest, tcComponents = IntMap.insert cIndex preds $ tcComponents state3 }

            {-
            repeat
              w := pop(vstack); Comp(w) := C;
            until w = v
            -}
            setComponent :: Vertex -> TCState -> TCState
            setComponent w = tcUpdateVertex w (\vertex -> vertex{ vsComponent = Just c } )

          in (final{ vsComponent = Just c }, foldr setComponent state4 (v : vertices))
    
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
      | otherwise = state2
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
    
    notTouchable :: Vertex -> Bool
    notTouchable (Vertex idx) = indexBoundLambda (RegionVar idx) /= lambdaBound

topologicalSort :: IntMap IntSet -> [Component] -> [Component]
topologicalSort _ [] = []
topologicalSort graph cs = snd $ foldr (\(Component c) -> topologicalSort' graph c) (IntSet.empty, []) cs

topologicalSort' :: IntMap IntSet -> Int -> (IntSet, [Component]) -> (IntSet, [Component])
topologicalSort' graph c (visited, accum)
  | c `IntSet.member` visited = (visited, accum)
  | otherwise = (visited'', Component c : accum')
  where
    preds = fromMaybe IntSet.empty $ IntMap.lookup c graph
    visited' = IntSet.insert c visited
    (visited'', accum') = IntSet.foldr (topologicalSort' graph) (visited', accum) preds

relationUnion :: Relation -> Relation -> Relation
relationUnion relLeft@(Relation gLeft) relRight@(Relation gRight) = iterate (unionWithoutClosure rel relHops)
  where
    rel = unionWithoutClosure relLeft relRight
    relHops = unionWithoutClosure (twoHops relLeft relRight) (twoHops relRight relLeft)

    iterate :: Relation -> Relation
    iterate current
      | didChange = iterate next
      | otherwise = current
      where
        (didChange, next) = relationFoldr edgeAddHops (False, current) relHops

    -- For an edge (v, w) performs successors(v) := (successors(v) union successors(w)) - {v}
    edgeAddHops :: RegionVar -> RegionVar -> (Bool, Relation) -> (Bool, Relation)
    edgeAddHops (RegionVar v) (RegionVar w) (change, Relation g) = case IntMap.lookup v g of
      Nothing -> error "relationUnion: couldn't find vertex v, whereas edge (v,w) exists"
      Just succVs -> case IntMap.lookup w g of
        Nothing -> (change, Relation g)
        Just succWs ->
          let
            new = v `IntSet.delete` IntSet.union succVs succWs
          in if new == succVs then (change, Relation g) else (True, Relation $ IntMap.insert v new g)

relationFilter :: (RegionVar -> Bool) -> Relation -> Relation
relationFilter f (Relation graph) = Relation $ IntMap.map (IntSet.filter (f . RegionVar)) $ IntMap.filterWithKey (\key _ -> f (RegionVar key)) graph

relationDecrementScope :: Relation -> Relation
relationDecrementScope relation
  = Relation
  $ IntMap.mapKeysMonotonic decrement 
  $ IntMap.map (IntSet.map decrement) graph
  where
    Relation graph = relationFilter (\r -> indexBoundLambda r /= 1) relation
    decrement :: Int -> Int
    decrement r = r'
      where
        RegionVar r' = variableIncrementLambdaBound 1 (-1) (RegionVar r)

relationDFS :: (RegionVar -> Bool) -> Relation -> RegionVar -> IntSet
relationDFS stop relation var = relationDFS' stop relation var IntSet.empty

relationDFS' :: (RegionVar -> Bool) -> Relation -> RegionVar -> IntSet -> IntSet
relationDFS' stop relation@(Relation graph) (RegionVar node) visited
  | IntSet.member node visited = visited
  | stop (RegionVar node) = visited'
  | otherwise = case IntMap.lookup node graph of
    Nothing -> visited'
    Just neighbours -> IntSet.foldr (relationDFS' stop relation . RegionVar) visited neighbours
  where
    visited' = IntSet.insert node visited

-- Internal utility functions. Note that these functions on their own do not assure that the
-- transitivity property is preserved.

hasEdge :: Relation -> Vertex -> Vertex -> Bool
hasEdge (Relation graph) (Vertex r1) (Vertex r2)
  | r1 == r2 = True
  | otherwise = case IntMap.lookup r1 graph of
    Nothing -> False
    Just rs -> r2 `IntSet.member` rs

addEdge :: Vertex -> Vertex -> Relation -> (Bool, Relation)
addEdge (Vertex v) (Vertex w) (Relation g)
  = (wasPresent, Relation g')
  where
    (old, g') = IntMap.insertLookupWithKey (\_ _ old -> IntSet.insert w old) v (IntSet.singleton w) g
    wasPresent = case old of
      Nothing -> False
      Just set -> w `IntSet.member` set

-- Creates a graph with edges for all two hops, eg. creates edge (v,w)
-- if edge (v,u) exists in graph g1 and (u, w) in graph g2
-- First element is the set of all vertices v for which an edge (v,w)
-- was added, the second is the resulting graph (relation)
twoHops :: Relation -> Relation -> Relation
twoHops (Relation g1) (Relation g2) = IntMap.foldrWithKey handleVertex emptyRelation g1
  where
    handleVertex :: Int -> IntSet -> Relation -> Relation
    handleVertex v us relationOut'
      = IntSet.foldr (handleEdge (Vertex v) . Vertex) relationOut' us

    handleEdge :: Vertex -> Vertex -> Relation -> Relation
    handleEdge (Vertex v) (Vertex u) relationOut' = case IntMap.lookup u g2 of
      Nothing -> relationOut'
      Just ws -> IntSet.foldr (addEdge' v u) relationOut' ws

    addEdge' :: Int -> Int -> Int -> Relation -> Relation
    addEdge' v u w relationOut'
      | v == w || hasEdge (Relation g1) (Vertex v) (Vertex w) || hasEdge (Relation g2) (Vertex v) (Vertex w) = relationOut'
      | otherwise = snd $ addEdge (Vertex v) (Vertex w) relationOut'

-- Gives the union of two relation, without computing the transitive closure
unionWithoutClosure :: Relation -> Relation -> Relation
unionWithoutClosure (Relation g1) (Relation g2) = Relation $ IntMap.unionWith (IntSet.union) g1 g2
