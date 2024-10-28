{-# LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts#-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
--
-- An interface for a monad that constains the most basic operations to 
-- solve constraints. Can be reused for all kinds of constraint-based
-- analyses.
--
-----------------------------------------------------------------------------


module Helium.Top.Top.Implementation.Basic where

import Control.Arrow
import Helium.Top.Top.Constraint
import Helium.Top.Top.Util.Option
import Helium.Top.Top.Implementation.General
import Helium.Top.Top.Interface.Basic
    ( ErrorLabel,
      HasBasic(getLabeledErrors, checkConditions, getChecks, addCheck,
               updateErrorInfo, addLabeledError, popConstraint, pushConstraints,
               stopAfterFirstError, discardConstraints),
      ClassBasic,
      stopOption,
      checkOption )
import Helium.Top.Top.Monad.Select
-- import Control.Monad.State
import Helium.Top.Top.Util.Embedding
import Helium.Top.Top.Util.Empty()
import Control.Monad (when)

------------------------------------------------------------------------
-- (I)  Algebraic data type

-- |A BasicState is parameterized over the monad in which the constraints can
-- be solved, and over the information that is stored with each constraint.
data BasicState info m = BasicState 
   { constraints :: Constraints m          -- ^ A stack of constraints that is to be solved
   , errors      :: [(info, ErrorLabel)]   -- ^ The detected errors
   , conditions  :: [(m Bool, String)]     -- ^ Conditions to check (for the solved constraints)
   , optionStop  :: Option Bool            -- ^ Discard all remaining constraints after the first error
   , optionCheck :: Option Bool
   }

------------------------------------------------------------------------
-- (II)  Instance of SolveState (Empty, Show)

instance SolveState (BasicState info m) where 
   stateName    _ = "Basic State"
   stateOptions s = [show (optionStop s), show (optionCheck s)] 
   
-- |An empty BasicState.
instance Empty (BasicState info m) where
   empty = BasicState 
      { constraints = []
      , errors      = []
      , conditions  = []
      , optionStop  = stopOption
      , optionCheck = checkOption
      }
 
instance Show (BasicState info m) where 
   show s
      | null (constraints s) = overview
      | otherwise = 
           unlines $ 
              ["Constraints", "-----------"] ++ 
              map (("   "++) . show) (constraints s) ++
              [overview]
    where
      overview = "("++show (length (constraints s))++" constraints, "++
                 show (length (errors s))++" errors, "++
                 show (length (conditions s))++" checks)"

------------------------------------------------------------------------
-- (III)  Embeddings

instance Embedded ClassBasic (BasicState info m) (BasicState info m)           where embedding = idE
instance Embedded ClassBasic (Fix (BasicState info) x m) (BasicState info m)   where embedding = fromFstFixE embedding 

------------------------------------------------------------------------
-- (IV)  Instance declaration

instance ( MonadState s m
         , Embedded ClassBasic s (BasicState info m)
         ) => 
           HasBasic (SelectFix (BasicState info) m) info where

   -- constraints
   pushConstraints xs = 
      modify (\s -> s { constraints = map (mapConstraint deselectFix) xs ++ constraints s })
   
   popConstraint = 
      do cs <- gets constraints 
         case cs of 
            []     -> return Nothing
            (x:xs) -> do modify (\s -> s { constraints = xs })
                         return (Just (mapConstraint selectFix x))
                         
   discardConstraints = 
      modify (\s -> s { constraints = [] })

   -- errors
   addLabeledError label info =
      do modify (\s -> s { errors = (info, label) : errors s })
         stop <- getOption stopAfterFirstError
         Control.Monad.when stop discardConstraints

   getLabeledErrors = 
      gets errors

   updateErrorInfo f =
      do errs    <- getLabeledErrors
         newErrs <- let g (info, label) = 
                           do newInfo <- f info
                              return (newInfo, label)
                    in mapM g errs
         modify (\s -> s { errors = newErrs })

   -- conditions
   addCheck text check = 
      modify (\s -> s { conditions = (deselectFix check, text) : conditions s})

   getChecks =
      gets (map (first selectFix) . conditions)

   stopAfterFirstError = useOption optionStop  (\x s -> s { optionStop  = x })
   checkConditions     = useOption optionCheck (\x s -> s { optionCheck = x })