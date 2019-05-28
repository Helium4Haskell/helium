module Helium.Normalization.RemoveRenames where

import Helium.Normalization.Utils

import qualified Data.Map as Map
import Data.Either(Either)
import qualified Data.Either as Either

import Lvm.Common.Id(Id)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..))

import Text.PrettyPrint.Leijen

{- Remove Renames -}
type Rename = Map.Map Id Id
exprRemoveRename :: Rename -> Expr -> DBGS Expr
exprRemoveRename renames expr =
    let (after, dbgs) = case expr of
            Let (Strict bind) expr1 ->
                let (renameORbind', dbgs') = bindRename renames bind
                    (expr1', dbgs'') = exprRemoveRename renames expr1
                in  case renameORbind' of
                    Left renames' ->
                        let (expr1'', dbgs''') = exprRemoveRename renames' expr1'
                        in (expr1'', dbgs' ++ dbgs'' ++ dbgs''')
                    Right bind' -> (Let (Strict bind') expr1', dbgs' ++ dbgs'')
            Let binds expr1 ->
                let (renamesANDMbinds', dbgs') = bindsRemoveRename renames binds
                    (renames', binds') = case renamesANDMbinds' of
                        Left renames'' -> (renames'', Nothing)
                        Right (binds'',renames'') -> (renames'', (Just binds''))
                    (expr1', dbgs'') = exprRemoveRename renames' expr1
                in  case binds' of
                    Just binds'' -> (Let binds'' expr1', dbgs' ++ dbgs'')
                    Nothing -> (expr1', dbgs' ++ dbgs'')
            Match name alts ->
                let name' = Map.findWithDefault name name renames
                    (alts', dbgs') = altsRemoveRename renames alts
                in  (Match name' alts', dbgs')
            Ap expr1 expr2 ->
                let (expr1', dbgs') = exprRemoveRename renames expr1
                    (expr2', dbgs'') = exprRemoveRename renames expr2
                in (Ap expr1' expr2', dbgs' ++ dbgs'')
            Lam name expr1 ->
                let (expr1', dbgs') = exprRemoveRename renames expr1
                in (Lam name expr1', dbgs')
            Con _ -> (expr, [])
            Var name -> (Var $ Map.findWithDefault name name renames, [])
            Lit _ -> (expr, [])
    in (after, (if expr == after then dbgs else ("\nRename:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) after ):dbgs))

bindsRemoveRename :: Rename -> Binds -> DBGS (Either Rename (Binds, Rename))
bindsRemoveRename renames binds = case binds of
    NonRec bind -> case bindRemoveRename renames bind of
        (Left rename, dbgs) -> (Left rename, dbgs)
        (Right bind', dbgs) -> (Right (NonRec bind', renames), dbgs)
    Strict bind -> case bindRename renames bind of
        (Left rename, dbgs) -> (Left rename, dbgs)
        (Right bind', dbgs) -> (Right (Strict bind', renames), dbgs)
    Rec binds' ->
        let (binds'', dbgs) = unpackdbgs $ map (bindRename renames) binds'
            (renames', binds''') = Either.partitionEithers binds''
            rename = Map.unions (renames:renames')
        in if length binds''' == 0
            then (Left rename, dbgs)
            else (Right (Rec binds''', rename), dbgs)

bindRemoveRename :: Rename -> Bind -> DBGS (Either Rename Bind)
bindRemoveRename renames (Bind name (Var name')) = (Left $ Map.union renames $ Map.singleton name (Map.findWithDefault name' name' renames), [])
bindRemoveRename renames bind = bindRename renames bind

bindRename :: Rename -> Bind -> DBGS (Either Rename Bind)
bindRename renames (Bind name expr) =
    let (expr', dbgs) = (exprRemoveRename renames expr)
    in  (Right $ Bind name expr', dbgs )

altsRemoveRename :: Rename -> Alts -> DBGS Alts
altsRemoveRename renames alts = unpackdbgs $ map (altRemoveRename renames) alts

altRemoveRename :: Rename -> Alt -> DBGS Alt
altRemoveRename renames (Alt pat expr) =
    let (expr', dbgs) = exprRemoveRename renames expr
    in  (Alt pat expr', dbgs)
