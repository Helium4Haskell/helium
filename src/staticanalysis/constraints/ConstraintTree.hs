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
import Constraints
import Types
import Utils            (fst3, snd3, thd3, internalError)
import qualified IntMap 

type MappedConstraints  cinfo = IntMap.IntMap (Constraint cinfo)
type ConstraintTreeRoot cinfo = Strategy -> Constraints cinfo
type ConstraintTrees    cinfo = [ConstraintTree cinfo]
type ConstraintTree     cinfo = Strategy ->                          -- strategy to order the constraints
                                MappedConstraints cinfo ->           -- the constraints that are mapped
                                ListCont (Constraint cinfo) ->       -- constraints to add (downward)
                                ( ListCont (Constraint cinfo)        -- the flattened tree
                                , ListCont (Constraint cinfo)        -- constraints to add (upward)
                                )


ctRoot :: ConstraintTree cinfo -> ConstraintTreeRoot cinfo
ctRoot tree strategy = 
   let tuple             = tree strategy IntMap.empty id
       TreeWalk treeWalk = fst3 strategy
   in treeWalk id [tuple] []

ctNode :: ConstraintTrees cinfo -> ConstraintTree cinfo
ctNode trees strategy albinds addDown =
   let tupled            = [ tree strategy albinds id | tree <- trees ]
       TreeWalk treeWalk = fst3 strategy
   in (treeWalk addDown tupled,id)

ctStrictOrder :: ConstraintTrees cinfo -> ConstraintTree cinfo
ctStrictOrder trees strategy albinds addDown =
   let tupled            = [ tree strategy albinds id | tree <- trees ]
       TreeWalk treeWalk = fst3 strategy
   in (treeWalk addDown [(foldr (.) id [ treeWalk id [tuple] | tuple <- tupled ],id)],id)

ctAdd :: Bool -> Constraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
ctAdd upward constraints tree strategy albinds addDown

   | upward    = let (flattened,added) = tree strategy albinds addDown
                 in (flattened,(constraints++) . added)

   | otherwise = let (flattened,added) = tree strategy albinds ((constraints++) . addDown)
                 in (flattened,added)

ctMapped :: Bool -> Constraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
ctMapped upward constraints tree strategy albinds addDown

   | snd3 strategy = tree strategy (IntMap.union (toMappedConstraints constraints) albinds) addDown

   | upward        = let (flattened,added) = tree strategy albinds addDown
                     in (flattened,(constraints++) . added)

   | otherwise     = let (flattened,added) = tree strategy albinds ((constraints++) . addDown)
                     in (flattened,added)

ctVariable :: Int -> ConstraintTree cinfo
ctVariable int strategy albinds addDown = 
   (id,(maybe id (:) (IntMap.lookupM albinds int)) . addDown)

ctEmpty :: ConstraintTree cinfo
ctEmpty strategy albinds addDown =
   (id,addDown)

---------------------------------------------

infixr 8 .>. , !<! , .>>. , !<<! , .<. , .<<.

ctSingle :: Constraints a -> ConstraintTree a
ctSingle cs = ctNode [cs .<. ctEmpty]

(.>.), (.<.), (!<!) :: Constraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
(.>.) = ctAdd False
(.<.) = ctAdd True

(!<!) constraints tree strategy albinds addDown
   | thd3 strategy   = let (flattened,added) = tree strategy albinds addDown
                       in ((constraints++) . flattened,added)
   | otherwise       = (constraints .>. tree) strategy albinds addDown


(.>>.), (.<<.), (!<<!) :: Constraints cinfo -> ConstraintTree cinfo -> ConstraintTree cinfo
(.>>.) = ctMapped False
(.<<.) = ctMapped True

(!<<!) constraints tree strategy albinds addDown
   | thd3 strategy   = let (flattened,added) = tree strategy albinds addDown
                       in ((constraints++) . flattened,added)
   | otherwise       = (constraints .<<. tree) strategy albinds addDown

toMappedConstraints :: Constraints info -> MappedConstraints info
toMappedConstraints = IntMap.fromList . map f 
   where f constraint = case constraint of
                           Equiv _ _ (TVar i)          -> (i,constraint)
                           ExplInstance _ (TVar i) _   -> (i,constraint)
                           ImplInstance _ (TVar i) _ _ -> (i,constraint)
                           _                           -> internalError "ConstraintTree.hs"
                                                                        "toMappedConstraints"
                                                                        "invalid constraint"
