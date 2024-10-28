--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Instr.Resolve (instrResolve) where

import Control.Exception (assert)
import Data.Maybe
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Instr.Data

{---------------------------------------------------------------
  resolve monad
---------------------------------------------------------------}
newtype Resolve a   = R ((Base,Env,Depth) -> (a,Depth))

type Env            = IdMap Depth
type Base           = Depth

find :: Id -> IdMap a -> a
find x env
  = fromMaybe (error msg) (lookupMap x env)
 where
   msg = "InstrResolve.find: unknown identifier " ++ show x

instance Functor Resolve where
  fmap f (R r)      = R (\ctx -> case r ctx of (x,d) -> (f x,d))

instance Applicative Resolve where
  pure x = R (\(_,_,d) -> (x,d))
  f1 <*> f2 = f1 >>= \v1 -> f2 >>= (pure . v1)
  
instance Monad Resolve where
  return            = pure 
  (R r) >>= f       = R (\ctx@(base,env,_) ->
                            case r ctx of
                              (x,depth') -> case f x of
                                              R fr -> fr (base,env,depth'))

{---------------------------------------------------------------
  non-proper morphisms
---------------------------------------------------------------}
pop :: Depth -> Resolve ()
pop n
  = push (-n)

push :: Depth -> Resolve ()
push n
  = R (\(_,_,d) -> ((),d+n))

-- base :: Resolve Base
-- base = R (\(bas,_,d) -> (bas,d))

depth :: Resolve Depth
depth
  = R (\(_,_,d) -> (d,d))

bind :: Id -> Resolve a -> Resolve a
bind x (R r)
  = R (\(bas,env,d) -> r (bas,extendMap x d env,d))

based :: Resolve a -> Resolve a
based (R r)
  = R (\(_,env,d) -> r (d,env,d))

resolveVar :: Var -> Resolve Var
resolveVar (Var x _ _)
  = R (\(_,env,d) -> let xd = find x env in (Var x (d - xd) xd,d))

alternative :: Depth -> Resolve a -> Resolve a
alternative d (R r)
  = R (\(bas,env,_) -> let (x,d1) = r (bas,env,d)
                       in assert (d1==d+1) (x,d1))
                         -- "InstrResolve.alternative: invalid elements on the stack " ++ show depth' ++ ", " ++ show depth)
                           
runResolve :: Resolve a -> a
runResolve (R r)
  = let (x,d) = r (0,emptyMap,0)
    in  assert (d==0) x -- "InstrResolve.runResolve: still elements on the stack (" ++ show depth ++ ")"

{---------------------------------------------------------------
  codeResolver
---------------------------------------------------------------}
instrResolve :: [Instr] -> [Instr]
instrResolve instrs
  = runResolve (resolves instrs)

resolves :: [Instr] -> Resolve [Instr]
resolves instrs
  = case instrs of
      (PARAM x : rest)          -> do{ push 1; bind x (resolves rest) }
      (VAR x : rest)            -> bind x (resolves rest)
      (instr : rest)            -> do{ is <- resolve instr
                                     ; iss <- resolves rest
                                     ; return (is ++ iss)
                                     }
      []                        -> return []

resolve :: Instr -> Resolve [Instr]
resolve (PUSHVAR v)
  = do{ var <- resolveVar v
      ; push 1
      ; return [PUSHVAR var]
      }

resolve (STUB v)
  = do{ var <- resolveVar v
      ; return [STUB var]
      }

resolve (PACKAP v n)
  = do{ var <- resolveVar v
      ; pop n
      ; return [PACKAP var n]
      }

resolve (PACKNAP v n)
  = do{ var <- resolveVar v
      ; pop n
      ; return [PACKNAP var n]
      }

resolve (PACKCON con v)
  = do{ var <- resolveVar v
      ; pop (arityFromCon con)
      ; return [PACKCON con var]
      }

resolve (PACK arity v)
  = do{ var <- resolveVar v
      ; pop arity
      ; return [PACK arity var]
      }

resolve (EVAL _ is)
  = do{ push 3
      ; d   <- depth
      ; is' <- based (resolves is)
      ; pop 3
      ; push 1
      ; return [EVAL d is']
      }

resolve (CATCH is)
  = do{ pop 1
      ; push 3
      ; is' <- resolves is
      ; return (PUSHCATCH : is')
      }
{-

  = do{ b   <- base
      ; pop 1
      ; push 3
      ; is' <- based (resolves is)
      ; d   <- depth
      ; pop (d-b)
      ; return (PUSHCATCH : is')
      }
-}
{-
resolve (RESULT is)
  = do{ b   <- base
      ; d   <- depth
      ; is' <- resolves is
      ; d'  <- depth
      ; pop (d' - b)
      ; if (d' <= d)
         then return (is' ++ [SLIDE 1 (d'-b-1) (d'-1), ENTER])
         else return (is' ++ [SLIDE (d'-d) (d-b) d,ENTER])
      }
-}
resolve (ATOM is)
  = resolveSlide 1 is

resolve (INIT is)
  = resolveSlide 0 is

resolve (MATCH alts)
  = resolveAlts MATCH alts

resolve (MATCHCON alts)
  = resolveAlts MATCHCON alts

resolve (SWITCHCON alts)
  = resolveAlts SWITCHCON alts

resolve (MATCHINT alts)
  = resolveAlts MATCHINT alts

resolve instr
  = do{ effect instr; return [instr] }

resolveSlide :: Depth -> [Instr] -> Resolve [Instr]
resolveSlide n is
  = do{ d0  <- depth
      ; is' <- resolves is
      ; d1  <- depth
      ; let m = d1-d0-n
      ; pop m
      ; return (is' ++ [SLIDE n m d1])
      }

resolveAlts :: ([Alt] -> a) -> [Alt] -> Resolve [a]
resolveAlts match alts
  = do{ pop 1
      ; d     <- depth
      ; alts' <- mapM (alternative d . resolveAlt) alts
      ; return [match alts']
      }

{-
resolveAlt (Alt pat [])
  = do{ b <- base
      ; d <- depth
      ; pop (d-b)
      ; return (Alt pat [])
      }
-}
resolveAlt :: Alt -> Resolve Alt
resolveAlt (Alt pat [])
  = do{ push 1
      ; return (Alt pat [])
      }


resolveAlt (Alt pat is)
  = do{ is' <- resolves is
      ; return (Alt pat is')
      }

effect :: Instr -> Resolve ()
effect instr
  = case instr of
      ENTER            -> pop 1
      RAISE            -> pop 1

      CALL global      -> do{ pop (arityFromGlobal global); push 1 }

      ALLOCAP {}       -> push 1
      NEWAP n          -> do{ pop n; push 1 }
      NEWNAP n         -> do{ pop n; push 1 }

      ALLOCCON {}      -> push 1
      NEWCON con       -> do{ pop (arityFromCon con); push 1 }

      NEW arity        -> do{ pop 1; pop arity; push 1 }
      UNPACK arity     -> do{ pop 1; push arity }

      ALLOC            -> do{ pop 2; push 1 }
      GETFIELD         -> do{ pop 2; push 1 }
      SETFIELD         -> pop 3
      GETTAG           -> do{ pop 1; push 1 }
      GETSIZE          -> do{ pop 1; push 1 }
      UPDFIELD         -> do{ pop 3; push 1 }

      RETURNCON con    -> pop (arityFromCon con)        -- it is the last instruction!

      PUSHCODE _       -> push 1
      PUSHINT _        -> push 1
      PUSHFLOAT _      -> push 1
      PUSHBYTES _ _    -> push 1

      PUSHCONT _       -> push 3
      PUSHCATCH        -> do{ pop 1; push 3 }

      ADDINT           -> pop 1
      SUBINT           -> pop 1
      MULINT           -> pop 1
      DIVINT           -> pop 1
      MODINT           -> pop 1
      QUOTINT          -> pop 1
      REMINT           -> pop 1

      ANDINT           -> pop 1
      XORINT           -> pop 1
      ORINT            -> pop 1
      SHRINT           -> pop 1
      SHLINT           -> pop 1
      SHRNAT           -> pop 1

      EQINT            -> pop 1
      NEINT            -> pop 1
      LTINT            -> pop 1
      GTINT            -> pop 1
      LEINT            -> pop 1
      GEINT            -> pop 1

      ADDFLOAT         -> pop 1
      SUBFLOAT         -> pop 1
      MULFLOAT         -> pop 1
      DIVFLOAT         -> pop 1

      EQFLOAT          -> pop 1
      NEFLOAT          -> pop 1
      LTFLOAT          -> pop 1
      GTFLOAT          -> pop 1
      LEFLOAT          -> pop 1
      GEFLOAT          -> pop 1

      _                -> return ()
