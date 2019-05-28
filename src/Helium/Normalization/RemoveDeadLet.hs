module Helium.Normalization.RemoveDeadLet where

import Helium.Normalization.Utils

import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..))

import Text.PrettyPrint.Leijen

{- Remove Dead Let -}
exprRemoveDeadLet :: Expr -> DBGS Expr
exprRemoveDeadLet expr =
    let (after, dbgs) = case expr of
            Let (Strict bind) expr1 ->
                let (bind', dbgs') = bindRemoveDeadLet bind
                    (expr1', dbgs'') = exprRemoveDeadLet expr1
                in  (Let (Strict bind') expr1', dbgs' ++ dbgs'')
            Let binds expr1 ->
                let (binds', dbgs') = bindsRemoveDeadLet binds
                    (expr1', dbgs'') = exprRemoveDeadLet expr1
                    bindNames = snd $ bindsOcc binds'
                    occ = exprOcc expr1'
                    simplify = Let binds' expr1'
                in  if anyMember occ bindNames -- Only removes complete let bindings (which are already split for mutual recursion)
                     then (simplify, dbgs' ++ dbgs'') -- Not a dead let
                     else (expr1', dbgs' ++ dbgs'') -- Dead let removal
            Match name alts ->
                let (alts', dbgs') = altsRemoveDeadLet alts
                in (Match name alts', dbgs')
            Ap expr1 expr2 ->
                let (expr1', dbgs') = exprRemoveDeadLet expr1
                    (expr2', dbgs'') = exprRemoveDeadLet expr2
                in (Ap expr1' expr2', dbgs' ++ dbgs'')
            Lam name expr1 ->
                let (expr1', dbgs') = exprRemoveDeadLet expr1
                in (Lam name expr1', dbgs')
            Con _ -> (expr, [])
            Var _ -> (expr, [])
            Lit _ -> (expr, [])
    in (after, (if expr == after then dbgs else ("\nDeadLet:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) after ):dbgs))

bindsRemoveDeadLet :: Binds -> DBGS Binds
bindsRemoveDeadLet binds = case binds of
    NonRec bind ->
        let (bind', dbgs) = bindRemoveDeadLet bind
        in (NonRec bind', dbgs)
    Strict bind ->
        let (bind', dbgs) = bindRemoveDeadLet bind
        in (Strict bind', dbgs)
    Rec binds' ->
        let (binds'', dbgs) = unpackdbgs $ map bindRemoveDeadLet binds'
        in (Rec binds'', dbgs)

bindRemoveDeadLet :: Bind -> DBGS Bind
bindRemoveDeadLet (Bind name expr) =
    let (expr', dbgs) = exprRemoveDeadLet expr
    in (Bind name expr', dbgs)

altsRemoveDeadLet :: Alts -> DBGS Alts
altsRemoveDeadLet alts = unpackdbgs $ map (altRemoveDeadLet) alts

altRemoveDeadLet :: Alt -> DBGS Alt
altRemoveDeadLet(Alt pat expr) =
    let (expr', dbgs) = exprRemoveDeadLet expr
    in (Alt pat expr', dbgs)
