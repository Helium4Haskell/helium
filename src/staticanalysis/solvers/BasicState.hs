module BasicState
  ( BasicState, newState
  , startSolving
  , pushConstraint, pushConstraints, popConstraint, allConstraints
  , addDebug, stateDebug, getDebug
  , addError, getErrors, setErrors
  , addCheck, doChecks
  , liftFunction, extend, getWith
  , module Control.Monad.State
  ) where

import Control.Monad.State
import Constraints
import GHC.IOBase (unsafePerformIO)
  
---------------------------------------------------------------------

data BasicState m err a = 
     S { constraints :: Constraints m
       , debug       :: IO ()
       , errors      :: [err]
       , checks      :: [(m Bool, String)]
       , hiddenExt   :: a
       }
       
newState :: BasicState m err ()
newState = S { constraints = [] 
             , debug       = return ()
             , errors      = []
             , checks      = []
             , hiddenExt   = ()
             }

instance Show a => Show (BasicState m err a) where 
   show s = unlines $ [ replicate 60 '-'
                      , "Constraints"
                      , "-----------"
                      ] ++
                      map (("  - "++) . show) (constraints s) ++
                      [ "("++show (length (constraints s))++" constraints, "
                        ++ show (length (errors s))++" errors)\n"
                      , "Extended State"
                      , "--------------"
                      , show (hiddenExt s)
                      , replicate 60 '-'
                      ]

---------------------------------------------------------------------

startSolving :: MonadState (BasicState monad info a) monad => monad ()
startSolving = 
   do mc <- popConstraint
      case mc of                    
         Nothing -> return () -- doChecks
         Just c  -> do solveConstraint c 
                       -- addCheck (show c) (checkConstraint c)
                       startSolving 
      
      
---------------------------------------------------------------------
       
pushConstraint  :: MonadState (BasicState monad info a) monad => 
                      Constraint monad -> monad ()
pushConstraints :: MonadState (BasicState monad info a) monad => 
                      Constraints monad -> monad ()
popConstraint   :: MonadState (BasicState monad info a) monad =>
                      monad (Maybe (Constraint monad))
allConstraints  :: MonadState (BasicState monad info a) monad =>
                      monad (Constraints monad)

pushConstraint x   = modify (\s -> s { constraints = x : constraints s })
pushConstraints xs = modify (\s -> s { constraints = xs ++ constraints s })
popConstraint      = do cs <- allConstraints 
                        case cs of 
                          []     -> return Nothing
                          (x:xs) -> do modify (\s -> s { constraints = xs })
                                       return (Just x)
allConstraints     = gets constraints

---------------------------------------------------------------------

addDebug   :: MonadState (BasicState monad info a) monad => 
                 IO () -> monad ()
stateDebug :: (MonadState (BasicState monad info a) monad, Show a) => 
                 monad ()             
getDebug   :: MonadState (BasicState monad info a) monad => 
                 monad (IO ())

addDebug io = modify (\s -> s { debug = debug s >> io })  
stateDebug  = get >>= (addDebug . putStrLn . show)
getDebug    = gets debug

---------------------------------------------------------------------

addError  :: MonadState (BasicState monad info a) monad => 
                info -> monad ()
setErrors :: MonadState (BasicState monad info a) monad =>  
                [info] -> monad ()                
getErrors :: MonadState (BasicState monad info a) monad => 
                monad [info]

addError err  = modify (\s -> s { errors = err : errors s })
getErrors     = gets errors
setErrors err = modify (\s -> s { errors = err })

---------------------------------------------------------------------

addCheck :: MonadState (BasicState monad info a) monad => 
               String -> monad Bool -> monad ()
doChecks :: MonadState (BasicState monad info a) monad => 
               monad ()

addCheck text check = modify (\s -> s { checks = (check, text) : checks s})
doChecks = do ms <- gets checks
              bs <- let f (m, _) = do bool <- m
                                      return (not bool)
                    in filterM f ms
              unless (null bs) $ 
                 error ( "\n\n  The following constraints were violated:\n" ++ 
                         unlines (map (("  - "++) . snd) bs))

---------------------------------------------------------------------
                                          
liftFunction :: (a -> b) -> BasicState monad info a -> BasicState monad info b
extend       :: a -> BasicState monad info a
getWith      :: (a -> b) -> BasicState monad info a -> b

liftFunction f x = x { hiddenExt = f (hiddenExt x) }
extend         a = liftFunction (const a) newState
getWith        f = f . hiddenExt
