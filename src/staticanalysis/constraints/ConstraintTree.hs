-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- ConstraintTree.hs : A tree of type constraints. This tree can be flattened 
--    with a "Strategy"
--
-- Note: Better would be to use the AG-system. Unfortunately, this is not 
--    possible (yet) because of the type variable in the data type 
--   representing the information that is carried by a type constraint.
-- 
-------------------------------------------------------------------------------

module ConstraintTree where

import Strategy
import TypeConstraints
import Types
import Utils            (fst3, snd3, thd3, internalError)
import List             (intersperse)
import ConstraintInfo
import FiniteMap

type MappedConstraints  cinfo = FiniteMap Int (TypeConstraint cinfo)
type PhasedConstraints  cinfo = FiniteMap Int (ListCont (TypeConstraint cinfo))
type ConstraintTreeRoot cinfo = Strategy -> TypeConstraints cinfo
type ConstraintTrees    cinfo = [ConstraintTree cinfo]
type ConstraintTree     cinfo = Strategy ->                          -- strategy to order the constraints
                                MappedConstraints cinfo ->           -- the constraints that are mapped
                                ListCont (TypeConstraint cinfo) ->       -- constraints to add (downward)
                                ( ListCont (TypeConstraint cinfo)        -- the flattened tree
                                , ListCont (TypeConstraint cinfo)        -- constraints to add (upward)
                                , PhasedConstraints cinfo                -- all phased constraints 
                                )


ctRoot :: ConstraintTree cinfo -> ConstraintTreeRoot cinfo
ctRoot tree strategy = 
   let tuple = tree strategy emptyFM id
   in inStrictOrder (fst3 strategy) tuple []

ctNode :: ConstraintTrees cinfo -> ConstraintTree cinfo
ctNode trees strategy albinds addDown =
   let (tuples, phaseLists) = unzip [ ((a, b), c)
                                    | tree <- trees
                                    , let (a, b, c) = tree strategy albinds id 
                                    ]
       TreeWalk treeWalk = fst3 strategy
       phased = foldr (plusFM_C (.)) emptyFM phaseLists -- moeten ook geordend worden?
   in (treeWalk addDown tuples, id, phased)

ctStrictOrder :: ConstraintTrees cinfo -> ConstraintTree cinfo
ctStrictOrder trees strategy albinds addDown = 
   let tuples                = [ tree strategy albinds id | tree <- trees ]
       t@(TreeWalk treeWalk) = fst3 strategy
       result                = foldr (.) id (map (inStrictOrder t) tuples)
   in (treeWalk addDown [(result, id)], id, emptyFM)

ctAdd :: Bool -> TypeConstraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
ctAdd upward constraints tree strategy albinds addDown

   | upward    = let (flattened, added, phased) = tree strategy albinds addDown
                 in (flattened, (constraints++) . added, phased)

   | otherwise = tree strategy albinds ((constraints++) . addDown)


ctMapped :: Bool -> TypeConstraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
ctMapped upward constraints tree strategy albinds addDown

   | snd3 strategy = tree strategy (toMappedConstraints constraints `plusFM` albinds) addDown

   | upward        = let (flattened, added, phased) = tree strategy albinds addDown
                     in (flattened, (constraints++) . added, phased)

   | otherwise     = tree strategy albinds ((constraints++) . addDown)

ctPhased :: ConstraintInfo cinfo => Int -> TypeConstraints cinfo -> ConstraintTree cinfo
ctPhased phase constraints strategy allbinds addDown = 
   let phasedConstraints = map (fmap (setConstraintPhaseNumber phase)) constraints
   in (id, addDown, unitFM phase (phasedConstraints++) )

ctVariable :: Int -> ConstraintTree cinfo
ctVariable int strategy albinds addDown = 
   (id, maybe id (:) (lookupFM albinds int) . addDown, emptyFM)

ctEmpty :: ConstraintTree cinfo
ctEmpty strategy albinds addDown = 
   (id, addDown, emptyFM)

---------------------------------------------

infixr 8 .>. , !<! , .>>. , !<<! , .<. , .<<.

ctSingle :: TypeConstraints a -> ConstraintTree a
ctSingle cs = ctNode [cs .<. ctEmpty]

(.>.), (.<.), (!<!) :: TypeConstraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
(.>.) = ctAdd False
(.<.) = ctAdd True

(!<!) constraints tree strategy albinds addDown
   | thd3 strategy   = let (flattened, added, phased) = tree strategy albinds addDown
                       in ((constraints++) . flattened, added, phased)
   | otherwise       = (constraints .>. tree) strategy albinds addDown


(.>>.), (.<<.), (!<<!) :: TypeConstraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
(.>>.) = ctMapped False
(.<<.) = ctMapped True

(!<<!) constraints tree strategy albinds addDown
   | thd3 strategy   = let (flattened, added, phased) = tree strategy albinds addDown
                       in ((constraints++) . flattened, added, phased)
   | otherwise       = (constraints .<<. tree) strategy albinds addDown

toMappedConstraints :: TypeConstraints info -> MappedConstraints info
toMappedConstraints = listToFM . concatMap f 
   where f constraint = case constraint of
                           Equality _ _ (TVar i)           -> [(i,constraint)]
                           ExplicitInstance _ (TVar i) _   -> [(i,constraint)]
                           ImplicitInstance _ (TVar i) _ _ -> [(i,constraint)]
                           MakeConsistent                  -> []

inStrictOrder :: TreeWalk ->                          -- treewalk
                 ( ListCont (TypeConstraint cinfo)        -- the flattened tree
                 , ListCont (TypeConstraint cinfo)        -- constraints to add (upward)
                 , PhasedConstraints cinfo            -- all phased constraints 
                 ) ->
                 ListCont (TypeConstraint cinfo)
inStrictOrder (TreeWalk treewalk) (flattened, added, phased) = 
   let list        = treewalk id [(flattened, added)]
       listOfLists = eltsFM phased
       seperator   = (MakeConsistent:)
   in foldr (.) id (intersperse seperator (list : listOfLists))
