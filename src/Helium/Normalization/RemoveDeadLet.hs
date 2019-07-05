module Helium.Normalization.RemoveDeadLet where

import Helium.Normalization.Utils

import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..))

{- Remove Dead Let -}
exprRemoveDeadLet :: Expr -> Expr
exprRemoveDeadLet expr =
    case expr of
        Let (Strict bind) expr1 ->
            let bind' = bindRemoveDeadLet bind
                expr1' = exprRemoveDeadLet expr1
            in  Let (Strict bind') expr1'
        Let binds expr1 ->
            let binds' = bindsRemoveDeadLet binds
                expr1' = exprRemoveDeadLet expr1
                bindNames = snd $ bindsOcc binds'
                occ = exprOcc expr1'
                simplify = Let binds' expr1'
            in  if anyMember occ bindNames -- Only removes complete let bindings (which are already split for mutual recursion)
                    then simplify -- Not a dead let
                    else expr1' -- Dead let removal
        Match name alts ->
            let alts' = altsRemoveDeadLet alts
            in Match name alts'
        Ap expr1 expr2 ->
            let expr1' = exprRemoveDeadLet expr1
                expr2' = exprRemoveDeadLet expr2
            in Ap expr1' expr2'
        Lam name expr1 ->
            let expr1' = exprRemoveDeadLet expr1
            in Lam name expr1'
        Con _ -> expr
        Var _ -> expr
        Lit _ -> expr

bindsRemoveDeadLet :: Binds -> Binds
bindsRemoveDeadLet binds = case binds of
    NonRec bind ->
        let bind' = bindRemoveDeadLet bind
        in NonRec bind'
    Strict bind ->
        let bind' = bindRemoveDeadLet bind
        in Strict bind'
    Rec binds' ->
        let binds'' = map bindRemoveDeadLet binds'
        in Rec binds''

bindRemoveDeadLet :: Bind -> Bind
bindRemoveDeadLet (Bind name expr) =
    let expr' = exprRemoveDeadLet expr
    in Bind name expr'

altsRemoveDeadLet :: Alts -> Alts
altsRemoveDeadLet alts = map (altRemoveDeadLet) alts

altRemoveDeadLet :: Alt -> Alt
altRemoveDeadLet(Alt pat expr) =
    let expr' = exprRemoveDeadLet expr
    in Alt pat expr'
