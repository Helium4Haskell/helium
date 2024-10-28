{-# LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Monad.StateFix 
   ( module Helium.Top.Top.Monad.StateFix
   , module Control.Monad.State
   ) where

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad (liftM, ap)
--import Control.Applicative

type StateFix s = StateFixT s Identity

data StateFixT s m a = Fix { unFix :: StateT (s (StateFixT s m)) m a }

-- To satisfy the 7.10.x proposal:
instance Monad m => Functor (StateFixT s m) where
    fmap  = Control.Monad.liftM
    
instance Monad m => Applicative (StateFixT s m) where
   pure = Fix . return
   (<*>) = Control.Monad.ap
   
-- Back to real code:   
instance Monad m => Monad (StateFixT s m) where 
   return  = pure
   m >>= f = Fix (unFix m >>= unFix . f)

instance Monad m => MonadState (s (StateFixT s m)) (StateFixT s m) where
   get = Fix get
   put = Fix . put

instance MonadTrans (StateFixT s) where
   lift = Fix . lift
   
instance MonadWriter w m => MonadWriter w (StateFixT s m) where
   tell   = lift . tell
   listen = Fix . listen . unFix
   pass   = Fix . pass   . unFix
   
--

runStateFixT :: StateFixT s m a -> s (StateFixT s m) -> m (a, s (StateFixT s m))
runStateFixT = runStateT . unFix

evalStateFixT :: Monad m => StateFixT s m a -> s (StateFixT s m) -> m a
evalStateFixT = evalStateT . unFix

execStateFixT :: Monad m => StateFixT s m a -> s (StateFixT s m) -> m (s (StateFixT s m))
execStateFixT = execStateT . unFix

--

runStateFix :: StateFix s a -> s (StateFix s) -> (a, s (StateFix s))
runStateFix m = runIdentity . runStateFixT m

evalStateFix :: StateFix s a -> s (StateFix s) -> a
evalStateFix m = runIdentity . evalStateFixT m

execStateFix :: StateFix s a -> s (StateFix s) -> s (StateFix s)
execStateFix m = runIdentity . execStateFixT m
