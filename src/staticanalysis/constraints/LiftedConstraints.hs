-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- LiftedConstraints.hs : Type constraints lifted to sorted association lists.
--
-------------------------------------------------------------------------------

module LiftedConstraints where

import Constraints
import TypeRepresentation
import SortedAssocList

infix 3 .===. , .:::. , .<==.
infix 3 !===! , !:::! , !<==!

------------------------------------------------------------------------------
-- Lifted constructors

lift combinator = 
    \as bs cf -> 
       let (_,binds,bsRest) = as ./\. bs 
       in 
          ( [ (a `combinator` b) (cf n) 
            | (alist,blist) <- binds
            , (_,a)         <- alist
            , (n,b)         <- blist 
            ]
          , bsRest
          )

(.===.) :: Ord key =>        AssocList key Tp       -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp)
(.:::.) :: Ord key =>        AssocList key TpScheme -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp)  
(.<==.) :: Ord key => Tps -> AssocList key Tp       -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp)

(.===.)    = lift (.==.)
(.:::.)    = lift (flip (.::.))
(.<==.) ms = lift (flip ((.<=.) ms))

------------------------------------------------------------------------------
-- Check and Lift constructors

checkAndLift combinator =
   \as bs cf -> 
       let (asUnique,asDuplicated) = onlyUniqueKeys as
           (asUnused,binds,bsRest) = asUnique ./\. bs
       in 
          ( [ (a `combinator` b) (cf n) 
            | (alist,blist) <- binds
            , (_,a)         <- alist
            , (n,b)         <- blist 
            ]
          , bsRest
          , asDuplicated
          , keys asUnused
          )

(!===!) :: Ord key =>        AssocList key Tp       -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp,[[key]],[key])
(!:::!) :: Ord key =>        AssocList key TpScheme -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp,[[key]],[key])
(!<==!) :: Ord key => Tps -> AssocList key Tp       -> AssocList key Tp -> (key -> (Tp,Tp) -> info) -> (Constraints info,AssocList key Tp,[[key]],[key])

(!===!)    = checkAndLift (.==.)
(!:::!)    = checkAndLift (flip (.::.))
(!<==!) ms = checkAndLift (flip ((.<=.) ms))

---------------------------------------------------------------------------------
-- utility functions

onlyUniqueKeys :: Ord key => AssocList key a -> (AssocList key a,[[key]])
onlyUniqueKeys aset = let (list,doubles) = rec (toList aset)
                      in (unsafeFromList list,doubles)

   where rec []       = ([],[])
         rec ((name,e):rest) = let (rest1,rest2) = span ((name==).fst) rest
                                   (rest',ds)    = rec rest2
                               in if null rest1
                                     then ((name,e):rest',ds)
                                     else (rest',(name:map fst rest1):ds)

(./\.) :: Ord key => AssocList key a -> AssocList key b -> (AssocList key a,[([(key,a)],[(key,b)])],AssocList key b) 
a1 ./\. a2  = let (alist,binds,blist) = rec (toList a1) (toList a2)
              in (unsafeFromList alist,binds,unsafeFromList blist)

   where rec [] bs = ([],[],bs)
         rec as [] = (as,[],[])
         rec (a:as) (b:bs) = case compare (fst a) (fst b) of
                               LT -> let (firstpart,rest) = span (\n -> fst n < fst b) as
                                         (xs,ys,zs)       = rec rest (b:bs)
                                     in (a:firstpart++xs,ys,zs)
                               EQ -> let (firstA,restA) = span (\n -> fst n == fst a) as
                                         (firstB,restB) = span (\n -> fst n == fst b) bs
                                         (xs,ys,zs)     = rec restA restB
                                     in (xs,(a:firstA,b:firstB):ys,zs)
                               GT -> let (firstpart,rest) = span (\n -> fst n < fst a) bs
                                         (xs,ys,zs)       = rec (a:as) rest
                                     in (xs,ys,b:firstpart++zs)
