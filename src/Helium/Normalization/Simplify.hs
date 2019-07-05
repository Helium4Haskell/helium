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
                        let expr' = exprRemoveRename Map.empty expr
                            expr'' = exprNormalizeMatches expr'
                            expr''' = exprRemoveDeadLet expr''
                        in (mds' ++ [decl{valueValue = expr'''}]
                            , dbgs''''
                                ++ (if expr == expr' then [] else ["\nRemove Renames:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) expr' ++ "\n"])
                                ++ (if expr' == expr'' then [] else ["\nNormalize Matches:\nbefore:\n" ++ (show . pretty) expr' ++ "\nafter:\n" ++ (show . pretty) expr'' ++ "\n"])
                                ++ (if expr'' == expr''' then [] else ["\nRemove Dead Let:\nbefore:\n" ++ (show . pretty) expr'' ++ "\nafter:\n" ++ (show . pretty) expr''' ++ "\n"]))
                    _ -> (mds' ++ [decl], dbgs'''')) ([],[]) $ moduleDecls m
