module Helium.Normalization.Simplify where

import Helium.Normalization.Utils
import Helium.Normalization.RemoveRenames(exprRemoveRename)
import Helium.Normalization.NormalizeMatches(exprNormalizeMatches)
import Helium.Normalization.RemoveDeadLet(exprRemoveDeadLet)

import qualified Data.Map as Map

import Lvm.Core.Expr(CoreModule)
import Lvm.Core.Module(Decl(..),moduleDecls)

import Text.PrettyPrint.Leijen

{- CoreSimplify -}
coreSimplify :: CoreModule -> DBGS CoreModule
coreSimplify m = (t, dbgs)
    where
    t = m{moduleDecls = mds}
    (mds,dbgs) = foldr (\decl (mds',dbgs'''') -> case decl of
                    DeclValue _ _ _ expr _ ->
                        let (expr', dbgs') = exprRemoveRename Map.empty expr
                            (expr'', dbgs'') = exprNormalizeMatches expr'
                            (expr''', dbgs''') = exprRemoveDeadLet expr''
                        in (mds' ++ [decl{valueValue = expr'''}]
                            , dbgs''''
                                ++ (if expr == expr' then [] else ["\nRemove Renames(only diff):\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) expr' ++ "\n"])
                                ++ (if expr' == expr'' then [] else ["\nNormalize Matches(only diff):\nbefore:\n" ++ (show . pretty) expr' ++ "\nafter:\n" ++ (show . pretty) expr'' ++ "\n"])
                                ++ (if expr'' == expr''' then [] else ["\nRemove Dead Let(only diff):\nbefore:\n" ++ (show . pretty) expr'' ++ "\nafter:\n" ++ (show . pretty) expr''' ++ "\n"])
                                ++ dbgs'' ++ dbgs' ++ dbgs''')
                    _ -> (mds' ++ [decl], dbgs'''')) ([],[]) $ moduleDecls m
