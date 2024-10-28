--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$
module Helium.Lvm.Asm.Inline (asmInline) where

import Data.Maybe
import Helium.Lvm.Asm.Data
import Helium.Lvm.Asm.Occur ( asmOccur )
import Helium.Lvm.Common.Id       
import Helium.Lvm.Common.IdMap

{---------------------------------------------------------------
  Inline environment maps identifiers to their definition
---------------------------------------------------------------}
type Env  = IdMap Expr

removeIds :: [Id] -> IdMap a -> IdMap a
removeIds = flip (foldr deleteMap)

{---------------------------------------------------------------
  asmInline
---------------------------------------------------------------}
asmInline :: AsmModule -> AsmModule
asmInline = fmap inlineTop . asmOccur

inlineTop :: Top -> Top
inlineTop (Top params expr)
  = Top params (inlineExpr emptyMap expr)

inlineExpr :: Env -> Expr -> Expr
inlineExpr env expr
  = case expr of
      -- dead variable
      Let _ (Note (Occur Never) _) e2
                    -> inlineExpr env e2
      -- once
      Let x (Note (Occur Once) e1) e2
                    -> let e1' = inlineExpr env e1  -- de-annotate
                       in  inlineExpr (extendMap x e1' env) e2

      -- trivial, inline everywhere
      Let x e1 e2   | trivial e1
                    -> let e1' = inlineExpr env (deAnnotate e1)
                       in inlineExpr (extendMap x e1' env) e2
                       
      Eval x e1 e2  | whnfTrivial e1
                    -> let e1' = inlineExpr env (deAnnotate e1)
                       in inlineExpr (extendMap x e1' env) e2

      -- inline-able let! binding?
      Eval x (Note (Occur Once) e1) e2  
                    -> let e1' = inlineExpr env e1 -- de-annotate
                       in if firstuse x e2
                           -- firstuse is true, we can inline immediately
                           then let env' = extendMap x (Eval x e1' (Ap x [])) env  -- NOTE: should we use a fresh id?
                                in inlineExpr env' e2
                           else let e2'  = inlineExpr env e2
                                in if firstuse x e2'
                                    -- firstuse became true after inlining! re-inline this definition again (is this too expensive?)
                                    then let env' = extendMap x (Eval x e1' (Ap x [])) emptyMap  -- NOTE: should we use a fresh id?
                                         in inlineExpr env' e2'
                                    -- otherwise, don't inline this definition
                                    else Eval x (Note (Occur Once) e1') e2'
      
      -- basic cases
      Let x e1 e2   -> let env' = deleteMap x env
                       in Let x (inlineExpr env e1) (inlineExpr env' e2)
      
      Eval x e1 e2  -> let env' = deleteMap x env 
                       in Eval x (inlineExpr env e1) (inlineExpr env' e2)

      LetRec bs e   -> let (bs',env') = inlineBinds env bs 
                       in LetRec bs' (inlineExpr env' e)

      Match x alts  -> case lookupMap x env of
                         Just e  -> -- trivial inlining of a let! binding leads to this configuration.
                                    -- a case-of-known transformation would actually remove this match.
                                    Eval x (Note (Occur Once) e) (Match x (inlineAlts env alts))
                         Nothing -> Match x (inlineAlts env alts)

      Ap x []       -> fromMaybe (Ap x []) (lookupMap x env)
      Ap x args     -> let args0 = inlineExprs env args
                       in case lookupMap x env of
                            Just e   -> case e of
                                          Ap id1 args1 -> Ap id1 (args1 ++ args0)     -- flatten applications
                                          Eval id1 e1 (Ap id2 [])  | id1==id2         -- special case for the strict inliner
                                                       -> Eval id1 e1 (Ap id1 args0)   
                                          _            -> Let x e (Ap x args)       -- don't inline!
                            Nothing  -> Ap x args0
      Con con args  -> Con (inlineCon env con)  (inlineExprs env args)
      Prim x args   -> Prim x (inlineExprs env args)
      Lit _         -> expr
      Note note e   -> Note note (inlineExpr env e)

inlineCon :: Env -> Con Expr -> Con Expr
inlineCon env con
  = case con of
      ConTag tag arity  -> ConTag (inlineExpr env tag) arity
      _                 -> con

inlineExprs :: Env -> [Expr] -> [Expr]
inlineExprs env exprs
  = [inlineExpr env expr | expr <- exprs]

inlineBinds :: Env -> [(Id,Expr)] -> ([(Id,Expr)],Env)
inlineBinds env binds 
  = let env' = removeIds (map fst binds) env
    in ([(x,inlineExpr env' e) | (x,e) <- binds], env')

inlineAlts :: Env -> [Alt] -> [Alt]
inlineAlts env alts
  = [inlineAlt env alt | alt <- alts]

inlineAlt :: IdMap Expr -> Alt -> Alt
inlineAlt env (Alt pat expr)
  = Alt pat (inlineExpr (removeIds (patIds pat) env) expr)
  where
    patIds (PatVar x)    = [x]
    patIds (PatCon _ xs) = xs
    patIds (PatLit _)    = []


{---------------------------------------------------------------
  deAnnotate
---------------------------------------------------------------}
deAnnotate :: Expr -> Expr
deAnnotate expr
  = case expr of
      Note _ e  -> deAnnotate e
      _         -> expr

{---------------------------------------------------------------
  trivial   
---------------------------------------------------------------}
trivial :: Expr -> Bool
trivial expr
  = case expr of
      Note _ e            -> trivial e
      Ap _ []             -> True
      Con (ConId _) []    -> True
      Lit _               -> True
      _                   -> False

whnfTrivial :: Expr -> Bool
whnfTrivial expr
  = case expr of
      Note _ e            -> whnfTrivial e
      Con (ConId _) []    -> True
      Lit _               -> True
      _                   -> False

{---------------------------------------------------------------
  firstuse
---------------------------------------------------------------}

firstuse :: Id -> Expr -> Bool
firstuse x = first x False

firsts :: Id -> Bool -> [Expr] -> Bool
firsts = foldl . first

first :: Id -> Bool -> Expr -> Bool
first x c expr
  = case expr of
      LetRec bs e   -> firsts x c (map snd bs ++ [e])
      Let _ e1 e2   -> firsts x c [e1,e2]
      Eval _ e1 _   -> first x False e1
      Match _ _     -> False
      Prim _ args   -> firsts x False args
      Ap y args    | null args && y == x -> True
                   | not (null args)     -> firsts x c (Ap y [] : args)
      Con _ args    -> firsts x c args
      Note _ e      -> first x c e
      _             -> c