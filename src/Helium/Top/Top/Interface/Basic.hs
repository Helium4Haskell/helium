{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances,
            FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Interface.Basic where

import Helium.Top.Top.Constraint
import Helium.Top.Top.Util.Option
import Helium.Top.Top.Monad.Select
import Helium.Top.Top.Monad.StateFix
import Helium.Top.Utils (internalError)
import Control.Monad (liftM, when, unless, filterM)

------------------------------------------------------------------------
-- (I)  Class name and (dedicated) deselect function
    
data ClassBasic = ClassBasic

deBasic :: (Embedded ClassBasic (s (StateFixT s m)) (t (StateFixT s m)), Monad m) => SelectFix t (StateFixT s m) a -> StateFixT s m a
deBasic = deselectFixFor ClassBasic

------------------------------------------------------------------------
-- (II)  Type class declaration

class Monad m => HasBasic m info | m -> info where

   -- constraints
   pushConstraint      :: Constraint m -> m ()
   pushConstraints     :: Constraints m -> m ()
   popConstraint       :: m (Maybe (Constraint m))
   discardConstraints  :: m ()
   -- errors
   addLabeledError     :: ErrorLabel -> info -> m () 
   getLabeledErrors    :: m [(info, ErrorLabel)]
   updateErrorInfo     :: (info -> m info) -> m ()
   -- conditions
   addCheck            :: String -> m Bool -> m ()
   getChecks           :: m [(m Bool, String)]
   -- options
   stopAfterFirstError :: OptionAccess m Bool
   checkConditions     :: OptionAccess m Bool

   -- defaults
   pushConstraint c    = pushConstraints [c]
   pushConstraints     = mapM_ pushConstraint
   stopAfterFirstError = ignoreOption stopOption
   checkConditions     = ignoreOption checkOption

------------------------------------------------------------------------
-- (III)  Instance for solver monad

instance ( Monad m
         , Embedded ClassBasic (s (StateFixT s m)) (t (StateFixT s m))
         , HasBasic (SelectFix t (StateFixT s m)) info
         ) => 
           HasBasic (StateFixT s m) info where
           
   -- constraints
   pushConstraint        = deBasic . pushConstraint . mapConstraint selectFix
   pushConstraints       = deBasic . pushConstraints . map (mapConstraint selectFix)
   popConstraint         = deBasic $ Control.Monad.liftM (fmap (mapConstraint deBasic)) popConstraint
   discardConstraints    = deBasic discardConstraints
   -- errors
   addLabeledError label = deBasic . addLabeledError label
   getLabeledErrors      = deBasic getLabeledErrors
   updateErrorInfo       = deBasic . selectFix . updateErrorInfo
   -- conditions
   addCheck s            = deBasic . addCheck s . selectFix
   getChecks             = deBasic (selectFix getChecks)
   -- options
   stopAfterFirstError   = optionAccessTrans deBasic stopAfterFirstError
   checkConditions       = optionAccessTrans deBasic checkConditions

------------------------------------------------------------------------
-- (IV)  Additional functions

pushOperation :: HasBasic m info => m () -> m ()
pushOperation = pushNamedOperation "operation"

pushNamedOperation :: HasBasic m info => String -> m () -> m ()
pushNamedOperation s = pushConstraint . operation s

addError :: HasBasic m info => info -> m ()
addError = addLabeledError NoErrorLabel

getErrors :: HasBasic m info => m [info]  
getErrors = Control.Monad.liftM (map fst) getLabeledErrors

doChecks :: HasBasic m info => m ()
doChecks = 
   do ms <- getChecks
      bs <- Control.Monad.filterM (Control.Monad.liftM not . fst) ms
      Control.Monad.unless (null bs) $ 
         let err = "\n\n  The following constraints were violated:\n" 
                   ++ unlines (map (("  - "++) . snd) bs)
         in internalError "Top.States.BasicState" "doChecks" err

startSolving  :: HasBasic m info => m ()
startSolving =
   do mc <- popConstraint
      case mc of                    
         Nothing -> 
            do check <- getOption checkConditions
               errs  <- getErrors
               Control.Monad.when (check && null errs) doChecks
         Just c  -> 
            do solveConstraint c
               addCheck (show c) (checkCondition c)
               startSolving 

-- |A datatype to label the errors that are detected.
data ErrorLabel = ErrorLabel String 
                | NoErrorLabel 
   deriving (Eq, Ord, Show)
   
stopOption, checkOption :: Option Bool
stopOption  = option False "Stop solving constraints after the first error"
checkOption = option False "Check constraint satisfaction afterwards"