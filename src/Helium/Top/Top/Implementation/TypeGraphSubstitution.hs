{-# LANGUAGE MonoLocalBinds, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Implementation.TypeGraphSubstitution where

import Helium.Top.Top.Implementation.TypeGraph.ClassMonadic
import Helium.Top.Top.Implementation.TypeGraph.Standard
import Helium.Top.Top.Implementation.TypeGraph.Heuristic
import Helium.Top.Top.Interface.Substitution
import Helium.Top.Top.Interface.Basic
import Helium.Top.Top.Interface.TypeInference
import Helium.Top.Top.Interface.Qualification
import Helium.Top.Top.Implementation.TypeGraph.DefaultHeuristics
import Helium.Top.Top.Implementation.TypeGraph.ApplyHeuristics
import Helium.Top.Top.Monad.Select
import Helium.Top.Top.Monad.StateFix
import Helium.Top.Top.Solver
import Helium.Top.Top.Implementation.General
import Helium.Top.Top.Util.Embedding

------------------------------------------------------------------------
-- (I)  Algebraic data type

data TypeGraphState info = TypeGraphState 
   { typegraph  :: StandardTypeGraph info
   , heuristics :: PathHeuristics info
   }

------------------------------------------------------------------------
-- (II)  Instance of SolveState (Empty, Show)

instance Show info => SolveState (TypeGraphState info) where
   stateName _ = "Typegraph substitution state"
  
instance Show info => Show (TypeGraphState info) where
   show = show . typegraph

instance Show info => Empty (TypeGraphState info) where
   empty = TypeGraphState empty defaultHeuristics

------------------------------------------------------------------------
-- (III)  Embeddings

instance Embedded ClassSubst (TypeGraphState info) (TypeGraphState info)              where embedding = idE
instance Embedded ClassSubst (Simple (TypeGraphState info) x m) (TypeGraphState info) where embedding = fromFstSimpleE embedding

------------------------------------------------------------------------
-- (IV)  Instance declaration

instance ( Monad m
         , Embedded ClassSubst (s (StateFixT s m)) t
         , HasTG (Select t (StateFixT s m)) info
         ) => 
           HasTG (StateFixT s m) info where 

   withTypeGraph f = deSubst (withTypeGraph f)
         
instance ( MonadState s m
         , Embedded ClassSubst s (TypeGraphState info)
         ) => 
           HasTG (Select (TypeGraphState info) m) info where
           
   withTypeGraph f =
    do (a, new) <- gets (f . typegraph)
       modify (\tgs -> tgs { typegraph = new })
       return a  

instance ( HasBasic m info
         , HasTI m info
         , HasQual m info
         , HasTG m info
         , MonadWriter LogEntries m
         , Show info
         , MonadState s m
         , Embedded ClassSubst s (TypeGraphState info)
         ) => 
           HasSubst (Select (TypeGraphState info) m) info where

   makeSubstConsistent = 
      do hs <- gets heuristics
         select (removeInconsistencies hs)
      
   unifyTerms a b c  = select (theUnifyTerms a b c)
   findSubstForVar a = select (substituteVariable a)
   fixpointSubst     = select  makeFixpointSubst

removeInconsistencies :: HasTypeGraph m info => PathHeuristics info -> m ()
removeInconsistencies hs =
   do errs <- applyHeuristics hs
      mapM_ deleteEdge (concatMap fst errs)
      mapM_ (addLabeledError unificationErrorLabel . snd) errs
      if null errs
            then -- everything is okay: no errors were found.
               unmarkPossibleErrors
        else -- Bug patch 3 february 2004
                 -- safety first: check whether *everything* is really removed. 
              removeInconsistencies hs