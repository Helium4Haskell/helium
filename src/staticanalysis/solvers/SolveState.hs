module SolveState 
  ( SolveState
  , getUnique, setUnique
  , setTypeSynonyms, getTypeSynonyms
  , addSiblings, getSiblings
  , getPredicates, addPredicate, setPredicates      -- type classes
  , newState, extend, liftFunction, getWith
  , module BasicState
  ) where

import           BasicState hiding   (extend, getWith, liftFunction, newState)
import qualified BasicState as State (extend, getWith, liftFunction, newState)
import Types

type SolveState monad info a = BasicState monad info (SS info a)

data SS info a = S { counter    :: Int
                   , synonyms   :: OrderedTypeSynonyms
                   , siblings   :: [[(String, TpScheme)]]
                   , predicates :: [(Predicate, info)]               
                   , hiddenExt  :: a 
                   }

newState :: SolveState monad info ()
newState = State.extend $
              S { counter    = 0
                , synonyms   = noOrderedTypeSynonyms
                , siblings   = []              
                , predicates = []                
                , hiddenExt  = () 
                }

instance Show a => Show (SS info a) where
   show s = unlines [ "counter = " ++ show (counter s)
                    , show (hiddenExt s)
                    ]

getUnique :: MonadState (SolveState monad info a) monad => 
                monad Int
setUnique :: MonadState (SolveState monad info a) monad => 
                Int -> monad ()

getUnique = gets (State.getWith counter)
setUnique i = modify $ State.liftFunction (\x -> x { counter = i })

setTypeSynonyms :: MonadState (SolveState monad info a) monad => 
                      OrderedTypeSynonyms -> monad ()
getTypeSynonyms :: MonadState (SolveState monad info a) monad => 
                      monad OrderedTypeSynonyms
 
setTypeSynonyms xs = modify $ State.liftFunction (\x -> x { synonyms = xs })
getTypeSynonyms    = gets (State.getWith synonyms)

addSiblings :: MonadState (SolveState monad info a) monad => 
                  [[(String, TpScheme)]] -> monad ()
getSiblings :: MonadState (SolveState monad info a) monad => 
                  monad [[(String, TpScheme)]]

addSiblings xs = modify $ State.liftFunction (\x -> x { siblings = xs ++ siblings x })
getSiblings    = gets (State.getWith siblings)

getPredicates :: MonadState (SolveState monad info a) monad => 
                    monad [(Predicate, info)]
addPredicate  :: MonadState (SolveState monad info a) monad =>
                    (Predicate, info)  -> monad ()
setPredicates :: MonadState (SolveState monad info a) monad => 
                    [(Predicate, info)] -> monad ()

getPredicates    = gets (State.getWith predicates)
addPredicate  p  = modify $ State.liftFunction (\x -> x { predicates = p : predicates x })
setPredicates ps = modify $ State.liftFunction (\x -> x { predicates = ps })

liftFunction :: (a -> b) -> SolveState monad info a -> SolveState monad info b
extend       :: a -> SolveState monad info a
getWith      :: (a -> b) -> SolveState monad info a -> b   

liftFunction f = State.liftFunction (\x -> x { hiddenExt = f (hiddenExt x) })
extend       a = liftFunction (const a) newState
getWith      f = f  . State.getWith hiddenExt
