module FixpointSolveState where

import ST 
import MonadState
import SolveState

data Fix info extra monad result = Fix { unFix :: StateT (SolveState (Fix info extra monad) info extra) monad result }

instance Monad monad => Monad (Fix info extra monad) where
   return x    = Fix (return x)
   Fix f >>= g = Fix (f >>= (unFix . g))

instance Monad monad => MonadState (SolveState (Fix info extra monad) info extra) (Fix info extra monad) where
   get = Fix get
   put = Fix . put

instance MonadTrans (Fix info extra) where
   lift = Fix . lift
 
liftSet    :: MonadTrans m => (forall a . ST a (val a))          -> m (STMonad val) ()
liftUse    :: MonadTrans m => (forall a . val a -> ST a result)  -> m (STMonad val) result
liftUpdate :: MonadTrans m => (forall a . val a -> ST a (val a)) -> m (STMonad val) ()

liftSet    f = lift (setSTMonad    f)
liftUse    f = lift (useSTMonad    f)
liftUpdate f = lift (updateSTMonad f)

runFix ::  Fix info extra monad result -> SolveState (Fix info extra monad) info extra -> monad (result, SolveState (Fix info extra monad) info extra)
runFix = runStateT . unFix
   
data STMonad val result = S { unS :: forall a . STRef a (val a) -> ST a result }

instance Monad (STMonad val) where 
   return x  = S (\ref -> return x)
   S f >>= g = S (\ref -> do result <- f ref
                             let S h = g result
                             h ref)
                             
runSTMonad :: STMonad val result -> result
runSTMonad (S f) = runST (
    do ref <- newSTRef (error "unset ref")
       f ref)
       
setSTMonad    :: (forall a . ST a (val a))          -> STMonad val ()
useSTMonad    :: (forall a . val a -> ST a result)  -> STMonad val result
updateSTMonad :: (forall a . val a -> ST a (val a)) -> STMonad val ()

setSTMonad    f = S (\ref -> f >>= writeSTRef ref)
useSTMonad    f = S (\ref -> readSTRef ref >>= f)
updateSTMonad f = S (\ref -> readSTRef ref >>= f >>= writeSTRef ref)
