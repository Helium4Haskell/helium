{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, KindSignatures,
            FunctionalDependencies, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Monad.Select 
   ( module Helium.Top.Top.Monad.Select
   , module Control.Monad.State
   ) where

import Helium.Top.Top.Util.Embedding
import Control.Monad.State
import Control.Monad (liftM, ap)
--import Control.Applicative

--------------------------------------------------------
-- Select Monad

newtype Select t m a = Select (m a)

-- To satisfy the 7.10.x proposal:
instance Monad m => Functor (Select s m) where
    fmap  = Control.Monad.liftM
    
instance Monad m => Applicative (Select s m) where
   pure   = Select . return 
   (<*>)  = Control.Monad.ap

-- Back to real code:
instance Monad m => Monad (Select t m) where
   return         = pure
   Select f >>= g = Select (do x <- f
                               let Select h = g x
                               h)

instance (MonadState s m, Embedded label s t) => MonadState t (Select t m) where
   get   = Select (gets   (getE embedding  ))
   put i = Select (modify (setE embedding i))

instance MonadTrans (Select t) where
   lift = select
   
select :: m a -> Select t m a
select = Select

--------------------------------------------------------
-- SelectFix Monad

data SelectFix (t :: (* -> *) -> *) (m :: * -> *) a = SelectFix (m a)

-- To satisfy the 7.10.x proposal:
instance Monad m => Functor (SelectFix t m) where
    fmap  = Control.Monad.liftM
    
instance Monad m => Applicative (SelectFix t m) where
   pure   = SelectFix . return 
   (<*>)  = Control.Monad.ap

-- Back to real code:
instance Monad m => Monad (SelectFix t m) where
   return            = pure
   SelectFix f >>= g = SelectFix (do x <- f
                                     let SelectFix h = g x
                                     h)
                            
instance (MonadState s m, Embedded label s (t m)) => MonadState (t m) (SelectFix t m) where
   get   = SelectFix (gets   (getE embedding  ))
   put i = SelectFix (modify (setE embedding i))

instance MonadTrans (SelectFix t) where
   lift = selectFix

selectFix :: m a -> SelectFix t m a
selectFix = SelectFix

--------------------------------------------------------
-- Class Embedded

class Embedded label s t | label s -> t, t -> label where
   embedding :: Embedding s t

instance Embedded c s2 t => Embedded c (s1, s2) t where
   embedding = composeE sndE embedding
   
--------------------------------------------------------
-- deselect functions for Select Monad

deselect :: Select t m a -> m a  
deselect (Select m) = m

deselectFor :: (Embedded label s t, MonadState s m) => label -> Select t m a -> m a
deselectFor  _ = deselect

--------------------------------------------------------
-- deselect functions for SelectFix Monad

deselectFix :: SelectFix t m a -> m a  
deselectFix (SelectFix m) = m

deselectFixFor :: (Embedded label s (t m), MonadState s m) => label -> SelectFix t m a -> m a
deselectFixFor _ = deselectFix 
