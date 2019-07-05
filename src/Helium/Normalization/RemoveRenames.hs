module Helium.Normalization.RemoveRenames where

import qualified Data.Map as Map
import Data.Either(Either)
import qualified Data.Either as Either

import Lvm.Common.Id(Id)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..))

{- Remove Renames -}
type Rename = Map.Map Id Id
exprRemoveRename :: Rename -> Expr -> Expr
exprRemoveRename renames expr =
    case expr of
        Let (Strict bind) expr1 ->
            let renameORbind' = bindRename renames bind
                expr1' = exprRemoveRename renames expr1
            in  case renameORbind' of
                Left renames' ->
                    let expr1'' = exprRemoveRename renames' expr1'
                    in expr1''
                Right bind' -> Let (Strict bind') expr1'
        Let binds expr1 ->
            let renamesANDMbinds' = bindsRemoveRename renames binds
                (renames', binds') = case renamesANDMbinds' of
                    Left renames'' -> (renames'', Nothing)
                    Right (binds'',renames'') -> (renames'', (Just binds''))
                expr1' = exprRemoveRename renames' expr1
            in  case binds' of
                Just binds'' -> Let binds'' expr1'
                Nothing -> expr1'
        Match name alts ->
            let name' = Map.findWithDefault name name renames
                alts' = altsRemoveRename renames alts
            in  Match name' alts'
        Ap expr1 expr2 ->
            let expr1' = exprRemoveRename renames expr1
                expr2' = exprRemoveRename renames expr2
            in Ap expr1' expr2'
        Lam name expr1 ->
            let expr1' = exprRemoveRename renames expr1
            in Lam name expr1'
        Con _ -> expr
        Var name -> Var $ Map.findWithDefault name name renames
        Lit _ -> expr

bindsRemoveRename :: Rename -> Binds -> (Either Rename (Binds, Rename))
bindsRemoveRename renames binds = case binds of
    NonRec bind -> case bindRemoveRename renames bind of
        Left rename -> Left rename
        Right bind' -> Right (NonRec bind', renames)
    Strict bind -> case bindRename renames bind of
        Left rename -> Left rename
        Right bind' -> Right (Strict bind', renames)
    Rec binds' ->
        let binds'' = map (bindRename renames) binds'
            (renames', binds''') = Either.partitionEithers binds''
            rename = Map.unions (renames:renames')
        in if length binds''' == 0
            then Left rename
            else Right (Rec binds''', rename)

bindRemoveRename :: Rename -> Bind -> (Either Rename Bind)
bindRemoveRename renames (Bind name (Var name')) = Left $ Map.union renames $ Map.singleton name (Map.findWithDefault name' name' renames)
bindRemoveRename renames bind = bindRename renames bind

bindRename :: Rename -> Bind -> (Either Rename Bind)
bindRename renames (Bind name expr) =
    let expr' = exprRemoveRename renames expr
    in  Right $ Bind name expr'

altsRemoveRename :: Rename -> Alts -> Alts
altsRemoveRename renames alts = map (altRemoveRename renames) alts

altRemoveRename :: Rename -> Alt -> Alt
altRemoveRename renames (Alt pat expr) =
    let expr' = exprRemoveRename renames expr
    in  Alt pat expr'
