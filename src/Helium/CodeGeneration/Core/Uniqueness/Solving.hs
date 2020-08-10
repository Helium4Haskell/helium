{-# LANGUAGE TupleSections #-}

module Helium.CodeGeneration.Core.Uniqueness.Solving where

import Helium.CodeGeneration.Core.Uniqueness.Data
import qualified Data.IntMap as M
import qualified Data.Maybe as M
import qualified Data.Graph as G
import qualified Data.List as L
import Data.Monoid (appEndo)
import Lvm.Common.IdMap hiding (foldMap)
import Lvm.Common.IdSet
import Lvm.Common.Id
import Lvm.Core.Type

---------------------------------------------------------------
-- Constraint solving: starting point
---------------------------------------------------------------

-- Solve all the constraints, returning substitutions
solveConstraints :: (IdMap (WEnv, Type), [AConstraint]) -> Unique Substitutions
solveConstraints (mcs, acs) = do
  -- 1. Binding group analysis.
  graph <- bindingGroupAnalysis mcs
  -- 2. Solve global constraints
  let subs = solveGlobalAConstraints acs
  -- 3. Solve per function the constraints
  solveGraphConstraints subs graph

-- The nodes are solved in reverse, by first solving the tail and then the head
-- The substitutions are passed upwards.
solveGraphConstraints :: Substitutions -> [INodeInfo] -> Unique Substitutions
solveGraphConstraints subs [] = return subs
solveGraphConstraints subs (g:gs) = do
  subs1 <- solveGraphConstraints subs gs
  subs2 <- solveGraphConstraint subs1 g
  return subs2

-- The main solving order algorithm
solveGraphConstraint :: Substitutions -> INodeInfo -> Unique Substitutions
solveGraphConstraint gsubs ini =
  do
  -- 1. Reduce type in/equality to annotation in/equality
  let (tcs, acs) = solveTConstraints $ func_tconstraints ini
  -- 2. Run worklist algorithm, solve annotation constraints as much as possible
  let (acs', lsubs) = solveAConstraints gsubs (acs ++ func_aconstraints ini)
  -- combine substitutions
  let subs = lsubs <> gsubs
  -- 3. Solve Instantiation constraints, and return annotation equality constraints
  itacs <- solveITConstraints subs tcs
  -- 4. Run worklist algorithm again, solving annotation constraints as much as possible
  let (facs, fsubs) = solveAConstraints subs (itacs ++ acs')
  -- 5. Default the constraints, returning only substitutions
  return $ defaultCS facs fsubs

---------------------------------------------------------------
-- Binding time analysis: in which order must the functions be solved
---------------------------------------------------------------

{-
 A node in the graph has information attached:  the function name and type, the type and annotation constraints, and a map of type constraints
 for which topological sort determines which of these type constraints must be solved mono- or polymorphic
-}
data INodeInfo = INodeInfo {
  func_name :: Id,
  func_type :: Type,
  iconstraints :: IdMap (Type, [Type]),
  func_tconstraints :: [TConstraint],
  func_aconstraints :: [AConstraint]
}

{-
A node in the graph contains information about that node, INodeInfo, a unique identifier (the function name), and which functions this function calls (the edges)
-}
type INode = (INodeInfo, Int, [Int])

{-
After the constraint generation phasewe have not yet generated instantiantion constraints for function calls to global definitions.

-}
bindingGroupAnalysis :: IdMap (WEnv, Type) -> Unique [INodeInfo]
bindingGroupAnalysis mcs = do
  let -- return the type of this function
      getType m i = snd (getMap i m)
      -- for each function we create a node.
      graph = foldMapWithId (createINode (getType mcs)) [] mcs
      -- we solve the graph by calculating the strongly connected components
      sgraph = G.stronglyConnComp graph
  -- we use the solved graph to create instantation constraints
  -- The resulting graph is flattened and reversed (see `SolveGraphConstraints`)
  return $ reverse $ G.flattenSCCs $ map solveGraph sgraph

-- A node is uniquely identified by the function name, and has a list of function names this node as edges to.
-- The node itself is a INode.
createINode :: (Id -> Type) -> Id -> (WEnv, Type) -> [INode] -> [INode]
createINode getType i (WEnv {assumptions = tas, tconstraints = etcs, aconstraints = eacs}, tp) nodes =
  let -- map the type of the function with the assumption
      ts = mapMapWithId ((,) . getType) tas
      -- create new inode: name and type, assumption map, and type and annotation constraints
      node = INodeInfo i tp ts (appEndo etcs []) (appEndo eacs [])
  in -- We use function as key and all keys in the assumptions as edges
     (node, intFromId i, keysMap tas) : nodes

{-
Solve the graph constructed by `stronglyConnComp':
  - If we have an acyclic node (no recursion), we create a polymorphic instantiation constraint; the set of functions is empty
  - If we have a cyclic node, we create monomorphic instantiation constraints for those functions that occur in `func_names`:
    The functions that are recursive.
-}
solveGraph :: G.SCC INodeInfo -> G.SCC INodeInfo
solveGraph (G.AcyclicSCC x) = G.AcyclicSCC $ solveNode mempty x
solveGraph (G.CyclicSCC xs) = G.CyclicSCC $ map (solveNode func_names) xs
  -- collect function names in this binding group, if function name occurs in `iconstraints` then
  -- the resulting instantiation should be done monomorphically.
  where func_names = setFromList $ map func_name xs

-- Solve a Node in the graph: the map is emptied and the extra instantation constraints are added to the Node.
solveNode :: IdSet -> INodeInfo -> INodeInfo
solveNode func_names (ini@(INodeInfo {iconstraints = ics, func_tconstraints = tcs})) =
  ini { iconstraints = emptyMap,
        func_tconstraints = foldMapWithId (createTConstraint func_names) tcs ics
      }
-- Create the instantation csontraints
-- If the current assumption is not a member of the set of function names,
-- the instantiation constraint is polymorphic.
createTConstraint :: IdSet -> Id -> (Type, [Type]) -> [TConstraint] -> [TConstraint]
createTConstraint func_names k (t1, ts) tcs = map newtcs ts ++ tcs
  where newtcs = TIConstraint isPolymorph Global mempty t1
        isPolymorph :: Bool
        isPolymorph = not $ elemSet k func_names

---------------------------------------------------------------
-- Solve global constraints: global annotation constraints, determines if a private
-- global function is shared. If there is a AAndConstraint for a certain variable, the usage is shared.
---------------------------------------------------------------

{-
  -- We start by solving the &&-constraints: all substitutions are UShared, so we only
  need to apply substitutions to equality constraints
  -- We then solve the equality constraints using substitution.
-}
solveGlobalAConstraints :: [AConstraint] -> Substitutions
solveGlobalAConstraints acs = solveGlobalAEqConstraints (apply subs cs) mempty
  where (cs, subs) = solveGlobalAAndConstraints acs mempty

solveGlobalAEqConstraints :: [AConstraint] -> Substitutions -> Substitutions
solveGlobalAEqConstraints ((AEqConstraint u1 (UVar u2)):cs) subs = solveGlobalAEqConstraints cs' subs'
  where subs' = insertS u2 u1 subs
        cs' = apply subs' cs
solveGlobalAEqConstraints _ _ = error "invalid constraint"

solveGlobalAAndConstraints :: [AConstraint] -> Substitutions -> ([AConstraint], Substitutions)
solveGlobalAAndConstraints ((AAndConstraint u1 u2 u3):cs) subs = (cs', solveGlobalAAndConstraint [u1, u2, u3] subs')
  where solveGlobalAAndConstraint us s = foldr (\(UVar u) -> insertS u UShared) s us
        (cs', subs') = solveGlobalAAndConstraints cs subs
solveGlobalAAndConstraints (c:cs) subs = (c:cs', subs')
  where (cs', subs') = solveGlobalAAndConstraints cs subs
solveGlobalAAndConstraints _ _ = error "invalid constraint"

---------------------------------------------------------------
-- Solve Instantiation constraints
---------------------------------------------------------------

solveITConstraints :: Substitutions -> [TConstraint] -> Unique [AConstraint]
solveITConstraints s ts = concat <$> mapM (solveITConstraint s) ts

{-
  We first apply substitutions to the type on the left hand side.
  Then we have two types of instantiation constraints:
  - Mono: use equality: we zip over both types and create annotation constraints
  - Poly:
    - we apply substitutions to the mset
    - Then we generalize and instantiate the type
    - Finally proceed as in the monovariant case
-}
solveITConstraint :: Substitutions -> TConstraint -> Unique [AConstraint]
solveITConstraint s (TIConstraint b _ ms t1 t2) =
  let t1' = apply s t1 in
  case b of
    True -> flip solveTEqConstraint t2 . fst <$> instantiateConstrainedType (generalize (apply s ms) t1')
    False -> return $ solveTEqConstraint t1' t2
solveITConstraint _ _ = error "invalid constraint"

---------------------------------------------------------------
-- Solve Type constraints
---------------------------------------------------------------

{-
 Solving type constraints is rather easy: zip over both types and create annotation constraints
 If a constraint is a instantiation constraint we skip it.
-}
solveTConstraints :: [TConstraint] -> ([TConstraint], [AConstraint])
solveTConstraints [] = mempty
solveTConstraints (x:xs) =
 let (xs', as) = solveTConstraints xs
 in maybe (x : xs', as) ((xs' ,) . (++ as)) (solveTConstraint x)

solveTConstraint :: TConstraint -> Maybe [AConstraint]
solveTConstraint (TEqConstraint t1 t2) = Just $ solveTEqConstraint t1 t2
solveTConstraint (TInEqConstraint t1 t2) = Just $ uncurry AInEqConstraint <$> retrieveAnnotationsType t1 t2
solveTConstraint _ = Nothing

solveTEqConstraint :: Type -> Type -> [AConstraint]
solveTEqConstraint t1 t2 = uncurry AEqConstraint <$> retrieveAnnotationsType t1 t2

retrieveAnnotationsType :: Type -> Type -> [(UAnn, UAnn)]
retrieveAnnotationsType (TAp t11 t12) (TAp t21 t22) = retrieveAnnotationsType t11 t21 ++ retrieveAnnotationsType t12 t22
retrieveAnnotationsType (TForall _ t1) (TForall _ t2) = retrieveAnnotationsType t1 t2
retrieveAnnotationsType (TAnn _ u1) (TAnn _ u2) = [(u1, u2)]
retrieveAnnotationsType _ _ = []

---------------------------------------------------------------
-- Solve Annotation constraints
---------------------------------------------------------------

{-
We solve the annotation constraints using a worklist algorithm:
  - We create a map of edges of the constraints: every key is an annotation variable with constraints referring this key as values
  - Then we walk over the constraints, called the worklist. If a constraint changes the value of one of its annotation constraints
    then all constraints referring this annotation constraint is added to the `worklist`
  - If the worklist is empty, we simplify the constraints
-}
solveAConstraints :: Substitutions -> [AConstraint] -> ([AConstraint], Substitutions)
solveAConstraints vs cs = (simplifyConstraints cs subs, subs)
  where subs = getValues (workList (createGraph vs cs) cs)

workList :: Graph -> [AConstraint] -> Graph
workList g [] = g
workList g (c:cs) = let (g', w) = workElement g c in workList g' (w ++ cs)

workElement :: Graph -> AConstraint -> (Graph, [AConstraint])
workElement g (AEqConstraint u1 u2) = solveAEqConstraint g u1 u2
workElement g (AInEqConstraint u1 u2) = solveAInEqConstraint g u1 u2
workElement g (AFConstraint u1 us) = (solveAFConstraint g u1 us, [])
workElement g (AArgConstraint u1 u2 u3) = solveAArgConstraint g u1 u2 u3
workElement g (AAndConstraint u1 u2 u3) = solveAAndConstraint g u1 u2 u3
workElement g (AOrConstraint u1 u2 u3) = solveAOrConstraint g u1 u2 u3

{-
 Solve the the equality constraints:
  - there are two cases: none are known or one of the annotations is known
  - If one of the annotations is known: function usage (w) or reuse (1)
  - If none are known, we lookup the values in the edges map and check the values
-}
solveAEqConstraint :: Graph -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAEqConstraint g u1@(UVar _) u2@(UVar _) = solveEqUAnn g (getValue u1 g, u1) (getValue u2 g, u2)
solveAEqConstraint g u1@(UVar _) u2 = solveAEqConstraint' g u1 u2
solveAEqConstraint g u1 u2@(UVar _) = solveAEqConstraint' g u2 u1
solveAEqConstraint _ _ _ = error "Invalid constraint"

solveAEqConstraint' :: Graph -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAEqConstraint' g u1 u2 =
  case getValue u1 g of
    Just _ -> (g, []) -- We have a value, so we are done
    _ -> (setValue u1 u2 g, getEdge u1 g)

solveEqUAnn :: Graph -> (Maybe UAnn, UAnn) -> (Maybe UAnn, UAnn) -> (Graph, [AConstraint])
solveEqUAnn g (_, u1) (Nothing, u2) = (setValue u2 u1 g, getEdge u2 g)
solveEqUAnn g (Just UUnique, u1) (Just UShared, _) = (setValue u1 UShared g, getEdge u1 g)
solveEqUAnn g (Nothing, u1) (_, u2) = (setValue u1 u2 g, getEdge u1 g)
solveEqUAnn g (Just UShared, _) (Just UUnique, u2) = (setValue u2 UShared g, getEdge u2 g)
solveEqUAnn g (Just vu1, _) (Just vu2, u2) | vu1 /= vu2 = (setValue u2 vu1 g, getEdge u2 g)
solveEqUAnn g _ _ = (g, [])

solveAInEqConstraint :: Graph -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAInEqConstraint g u1 u2 =
  case (getValue u1 g, getValue u2 g) of
    (Nothing, Just UUnique) -> (setValue u1 UUnique g, getEdge u1 g)
    (Just UShared, Just UUnique) -> (setValue u2 UShared g, getEdge u2 g)
    (Just UShared, Nothing) -> (setValue u2 UShared g, getEdge u2 g)
    _ -> (g, [])

solveAFConstraint :: Graph -> UAnn -> [UAnn] -> Graph
solveAFConstraint g u1 [] = maybe (setValue u1 UNone g) (const g) (getValue u1 g)
solveAFConstraint g u1 (u:us) = maybe g solveAFConstraint' (getValue u g)
  where solveAFConstraint' u' = if u' == UShared then setValue u1 UShared g else solveAFConstraint g u1 us

solveAArgConstraint :: Graph -> UAnn -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAArgConstraint g u1 u2 u3 = maybe (g, []) solveAArgConstraint' (getValue u3 g)
  where solveAArgConstraint' u =
          case (getValue u2 g, u) of
            (Nothing, _) -> (setValue u1 UNone (setValue u2 u g), getEdge u2 g)
            (Just UShared, UUnique) -> (setValue u1 UShared (setValue u2 UShared g), [])
            _ -> (setValue u1 UNone g, [])

solveAAndConstraint :: Graph -> UAnn -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAAndConstraint g u1 u2 u3 = (g3, L.nub (a1 ++ a2 ++ a3))
  where (g1, a1) = solveAndAnn g (getValue u1 g) u1
        (g2, a2) = solveAndAnn g1 (getValue u2 g1) u2
        (g3, a3) = solveAndAnn g2 (getValue u3 g2) u3

solveAndAnn :: Graph -> Maybe UAnn -> UAnn -> (Graph, [AConstraint])
solveAndAnn g (Just UShared) _ = (g, [])
solveAndAnn g _ u = (setValue u UShared g, getEdge u g)

solveAOrConstraint :: Graph -> UAnn -> UAnn -> UAnn -> (Graph, [AConstraint])
solveAOrConstraint g u1 u2 u3 = solveOrLAnn g (getValue u1 g, u1) u2 u3

solveOrLAnn :: Graph -> (Maybe UAnn, UAnn) -> UAnn -> UAnn -> (Graph, [AConstraint])
solveOrLAnn g (Just UShared, _) u2 u3 = (g2, L.nub (a2 ++ a3))
  where (g1, a2) = solveAndAnn g (getValue u2 g) u2
        (g2, a3) = solveAndAnn g1 (getValue u3 g1) u3
solveOrLAnn g (Just UUnique, u1) u2 u3 = solveOrLUAnn g (getValue u2 g) (getValue u3 g) u1
solveOrLAnn g (_, u1) u2 u3 = solveOrRAnn g (getValue u2 g) (getValue u3 g) u1

solveOrLUAnn :: Graph -> Maybe UAnn -> Maybe UAnn -> UAnn -> (Graph, [AConstraint])
solveOrLUAnn g (Just UShared) _ u = (setValue u UShared g, getEdge u g)
solveOrLUAnn g _ (Just UShared) u = (setValue u UShared g, getEdge u g)
solveOrLUAnn g _ _ _ = (g, [])

solveOrRAnn :: Graph -> Maybe UAnn -> Maybe UAnn -> UAnn -> (Graph, [AConstraint])
solveOrRAnn g (Just UUnique) _ u = (setValue u UUnique g, getEdge u g)
solveOrRAnn g _ (Just UUnique) u = (setValue u UUnique g, getEdge u g)
solveOrRAnn g (Just UShared) _ u = (setValue u UShared g, getEdge u g)
solveOrRAnn g _ (Just UShared) u = (setValue u UShared g, getEdge u g)
solveOrRAnn g _ _ _ = (g, [])

---------------------------------------------------------------
-- Simplify Constraints
---------------------------------------------------------------

simplifyConstraints :: [AConstraint] -> Substitutions -> [AConstraint]
simplifyConstraints cs subs = foldr (simplifyConstraint subs) [] cs

simplifyConstraint :: Substitutions -> AConstraint -> [AConstraint] -> [AConstraint]
simplifyConstraint _ (AEqConstraint _ _) cs = cs
simplifyConstraint subs c@(AInEqConstraint u1 u2) cs = if isObseleteL u1 subs || isObseleteR u2 subs then cs else c:cs
simplifyConstraint subs c@(AArgConstraint u1 _ _) cs = if hasValue u1 subs then cs else c:cs
simplifyConstraint _ (AAndConstraint _ _ _) cs = cs
simplifyConstraint subs c@(AOrConstraint u1 _ _) cs = if isObseleteL u1 subs then cs else c:cs
simplifyConstraint subs c@(AFConstraint u1 _) cs = if hasValue u1 subs then cs else c:cs

isObseleteL :: UAnn -> Substitutions -> Bool
isObseleteL (UVar u) subs =
  case lookupSubs u subs of
    Just UShared -> True
    Just UUnique -> True
    _ -> False
isObseleteL _ _ = error "invalid annotation"

isObseleteR :: UAnn -> Substitutions -> Bool
isObseleteR (UVar u) subs =
  case lookupSubs u subs of
    Just UShared -> True
    _ -> False
isObseleteR _ _ = error "invalid annotation"

hasValue :: UAnn -> Substitutions -> Bool
hasValue (UVar u) subs = M.isJust (lookupSubs u subs)
hasValue _ _ = error "invalid annotation"

---------------------------------------------------------------
-- Default Constraints
---------------------------------------------------------------

defaultCS :: [AConstraint] -> Substitutions -> Substitutions
defaultCS [] subs = subs
defaultCS ((AInEqConstraint u1 (UVar u2)):xs) subs = defaultCS (apply subs' xs) subs'
  where subs' = insertS u2 u1 subs
defaultCS (_:xs) subs = defaultCS xs subs

---------------------------------------------------------------
-- A worklist graph: The representation of the worklist algorithm
---------------------------------------------------------------

-- an Edge is a list of constraints
type Edge = [AConstraint]

-- Edges maps an annotation variable to an Edge (constraints)
type Edges = M.IntMap Edge

-- Edges is for constraints referring a particular annotation variable
data Graph = Graph Edges Substitutions

---------------------------------------------------------------
-- Operations on the Worklist Graph
---------------------------------------------------------------

createGraph :: Substitutions -> [AConstraint] -> Graph
createGraph vs cs = foldr createEdge emptyGraph cs
  where emptyGraph = Graph M.empty vs

createEdge :: AConstraint -> Graph -> Graph
createEdge c@(AEqConstraint u1 u2) g = foldr (insertEdge c) g [u1,u2]
createEdge c@(AInEqConstraint u1 u2) g = foldr (insertEdge c) g [u1,u2]
createEdge c@(AArgConstraint u1 u2 u3) g = foldr (insertEdge c) g [u1,u2,u3]
createEdge c@(AAndConstraint u1 u2 u3) g = foldr (insertEdge c) g [u1,u2,u3]
createEdge c@(AOrConstraint u1 u2 u3) g = foldr (insertEdge c) g [u1,u2,u3]
createEdge c@(AFConstraint _ us) g = foldr (insertEdge c) g us

insertEdge :: AConstraint -> UAnn -> Graph -> Graph
insertEdge c (UVar u) (Graph e vs) = Graph (M.alter (Just . M.maybe [c] (c :)) u e) vs
insertEdge _ _ g = g

setValue :: UAnn -> UAnn -> Graph -> Graph
setValue (UVar k) u (Graph e m) = Graph e $ insertS k u m
setValue _ _ _ = error "invalid annotation"

getValue :: UAnn -> Graph -> (Maybe UAnn)
getValue (UVar k) g = lookupSubs k (getValues g)
getValue _ _ = error "invalid annotation"

getEdge :: UAnn -> Graph -> Edge
getEdge (UVar i) (Graph e _) = e M.! i
getEdge _ _ = []

getValues :: Graph -> Substitutions
getValues (Graph _ m) = m

