module Helium.Optimization.StrictnessInfo(getLetBangs, showLetBangs) where

import Helium.Utils.Utils

import Helium.Optimization.LVM_Syntax

import Lvm.Common.Id(stringFromId)

import Text.PrettyPrint.Leijen(pretty)
--import Data.Set (Set)
--import qualified Data.Set as Set
import Data.Maybe(mapMaybe)
import Data.List(intercalate)

showLetBangs :: [(String, Expr, [Expr])] -> String
showLetBangs fnBangs = intercalate "\n" (map showLetBang (filter (\(_,_,bangs) -> not $ null bangs) fnBangs))

showLetBang :: (String, Expr, [Expr]) -> String
showLetBang (functionName, _{-expr-}, letBangs) = functionName ++ ":\n" {-++ showPrettyExpr expr ++ "\n"-} ++ (intercalate "\n" (map showBang letBangs))
    where
    showBang :: Expr -> String
    showBang (Expr_Let (Binds_Strict (Bind_Bind name expr _)) _ _) = "    let! " ++ stringFromId name ++ " = " ++ showPrettyExpr expr
    showBang _ = internalError "StrictnessInfo.hs" "showLetBang" "not bang!?"

showPrettyExpr :: Expr -> String
showPrettyExpr = show . pretty . expr2CoreExpr

getLetBangs :: OptimizeModule -> [(String, Expr, [Expr])]
getLetBangs (OptimizeModule_Module _ _ _ decls) = getLetBangsDecls decls

getLetBangsDecls :: Decls -> [(String, Expr, [Expr])]
getLetBangsDecls = mapMaybe getLetBangsDecl
getLetBangsDecl :: Decl -> Maybe (String, Expr, [Expr])
getLetBangsDecl (Decl_Start name _ _ expr) = Just (stringFromId name, expr, getLetBangsExpr expr)
getLetBangsDecl (Decl_Function name _ _ expr _ _) = Just (stringFromId name, expr, getLetBangsExpr expr)
getLetBangsDecl _ = Nothing

getLetBangsExpr :: Expr -> [Expr]
getLetBangsExpr expr = case expr of
    Expr_Let (Binds_Strict bind ) expr1 _ -> expr : getLetBangsBind bind ++ getLetBangsExpr expr1
    Expr_Let binds expr1 _ -> getLetBangsBinds binds ++ getLetBangsExpr expr1
    Expr_Match _ alts _ -> getLetBangsAlts alts
    Expr_Ap expr1 expr2 _ -> getLetBangsExpr expr1 ++ getLetBangsExpr expr2
    Expr_Lam _ expr1 _ -> getLetBangsExpr expr1
    Expr_ConId _ _ -> []
    Expr_ConTag tag _ _ -> getLetBangsExpr tag
    Expr_Var _ _ -> []
    Expr_Lit _ _ -> []

getLetBangsBinds :: Binds -> [Expr]
getLetBangsBinds (Binds_Rec binds) = concatMap getLetBangsBind binds
getLetBangsBinds (Binds_NonRec bind) = getLetBangsBind bind
getLetBangsBinds (Binds_Strict _) = internalError "StrictnessInfo.hs" "getLetBangsBinds" "Let! should have been handled"

getLetBangsBind :: Bind -> [Expr]
getLetBangsBind (Bind_Bind _ expr _) = getLetBangsExpr expr

getLetBangsAlts :: Alts -> [Expr]
getLetBangsAlts = concatMap getLetBangsAlt

getLetBangsAlt :: Alt -> [Expr]
getLetBangsAlt (Alt_Alt _ expr) = getLetBangsExpr expr
