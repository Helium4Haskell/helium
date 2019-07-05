module Helium.Normalization.NormalizeMatches where

import Helium.Utils.Utils(internalError)
import Helium.Normalization.Utils

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Lvm.Common.Id(Id,idFromString)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..),Pat(..),Con(..))

import Text.PrettyPrint.Leijen

{- Normalize Matches-}
leading :: String -> String -> Bool
leading ls ss = (all (\(l,s) -> l == s) (zip ls ss)) && (length ls <= length ss)
leadingNextClause :: String -> Bool
leadingNextClause = leading "\"nextClause$"
leadingGuard :: String -> Bool
leadingGuard = leading "\"guard$"

exprNormalizeMatches :: Expr -> Expr
exprNormalizeMatches expr =
    case expr of
        Let (Strict (Bind nameB exprB)) (Match nameM (Alt (PatCon (ConId trueId) []) exprA:_))
            | nameB == nameM --leadingGuard (show nameB) &&
            && show trueId == "\"True\""
            && exprB == Var (idFromString "otherwise") -> exprA
        Let (NonRec (Bind nameNB exprNB)) exprN@(Let bindS@(Strict (Bind nameSB exprSB)) (Match nameM alts))
            | leadingNextClause (show nameNB)
            && nameSB == nameM ->
            let exprNB' = exprNormalizeMatches exprNB
                exprN' = exprNormalizeMatches exprN
                expr' = Let (NonRec (Bind nameNB exprNB')) exprN'

                exprSB' = exprNormalizeMatches exprSB
                alts' = map (\(Alt pat exprA) ->
                    let exprA' = exprNormalizeMatches exprA
                    in Alt pat exprA') alts

                (expr'', dbgs'''') = case exprNormalize exprSB' exprNB' of
                    Just (alts'',bindss) ->
                        let combAlts = combineAlts nameNB alts' alts''
                        in foldr (Let) (Let bindS (Match nameM combAlts)) bindss
                    Nothing -> expr'

            in expr''
        Let (Strict (Bind nameB exprB)) exprL ->
            let exprB' = exprNormalizeMatches exprB
                exprL' = exprNormalizeMatches exprL
            in Let (Strict (Bind nameB exprB')) exprL'
        Let (NonRec (Bind nameB exprB)) exprL ->
            let exprB' = exprNormalizeMatches exprB
                exprL' = exprNormalizeMatches exprL
            in Let (NonRec (Bind nameB exprB')) exprL'
        Let (Rec binds) exprL ->
            let binds' = map (\(Bind nameB exprB) ->
                    let exprB' = exprNormalizeMatches exprB
                    in (Bind nameB exprB') binds
                exprL' = exprNormalizeMatches exprL
            in Let (Rec binds') exprL'
        Match name alts ->
            let alts' = map (\(Alt pat exprA) ->
                    let exprA' = exprNormalizeMatches exprA
                    in (Alt pat exprA') alts
            in Match name alts'
        Ap expr1 expr2 ->
            let expr1' = exprNormalizeMatches expr1
                expr2' = exprNormalizeMatches expr2
            in Ap expr1' expr2'
        Lam name expr1 ->
            let expr1' = exprNormalizeMatches expr1
            in Lam name expr1'
        Con _ -> expr
        Var _ -> expr
        Lit _ -> expr

exprNormalize :: Expr -> Expr -> Maybe (Alts,[Binds])
exprNormalize exprName expr = case expr of
    Let (Strict (Bind nameSB exprSB)) (Match nameM alts)
        | nameSB == nameM
        && exprName == exprSB -> Just (alts,[])
    Let binds exprL -> case exprNormalize exprName exprL of
        (Just (alts,bindss),dbgs) -> Just (alts,binds:bindss)
        (Nothing,dbgs) -> Nothing
    Lam name exprL ->
        let m = exprNormalize exprName exprL
        in m
    _ -> Nothing
    where namesFromBinds :: Binds -> String
          namesFromBinds (Strict (Bind nameB _)) = show nameB
          namesFromBinds (NonRec (Bind nameB _)) = show nameB
          namesFromBinds (Rec binds) = unwords $ map (\(Bind nameB _) -> show nameB) binds

altsRemovePatDefault :: Alts -> Alts
altsRemovePatDefault [] = []
altsRemovePatDefault (Alt PatDefault _:alts) = alts
altsRemovePatDefault (alt:alts) = alt:altsRemovePatDefault alts

combineAlts :: Id -> Alts -> Alts -> Alts
combineAlts _ [] altsN = altsN
combineAlts _ altsP [] = altsP
combineAlts nextClause (Alt PatDefault _:altsP) altsN = combineAlts nextClause altsP altsN
combineAlts nextClause (altP@(Alt (PatLit litP) exprP):altsP) altsN = replaceDefaults nextClause $ case findPatLit altsN of
    (altsN', Just exprN) -> Alt (PatLit litP) (combineExpr nextClause exprP exprN):combineAlts nextClause altsP altsN'
    (altsN', Nothing) -> altP:combineAlts nextClause altsP altsN'
    where
        findPatLit :: Alts -> (Alts, Maybe Expr)
        findPatLit ((Alt (PatLit litN) exprN):altsN') | litP == litN = (altsN', Just exprN)
        findPatLit (altN':altsN') =
            let (altsN'', mAlt) = findPatLit altsN'
            in  (altN':altsN'', mAlt)
        findPatLit [] = ([],Nothing)
combineAlts nextClause (altP@(Alt (PatCon contagP idsP) exprP):altsP) altsN = replaceDefaults nextClause $ case findPatCon altsN of
    (altsN', Just (idsN, exprN)) ->
        let idsR = idsRFromList (zip idsP idsN)
            idsN' = map (\n -> Map.findWithDefault n n idsR) idsN
        in Alt (PatCon contagP idsN') (combineExpr nextClause (updateIds idsR exprP) exprN):combineAlts nextClause altsP altsN'
    (altsN', Nothing) -> altP:combineAlts nextClause altsP altsN'
    where
        findPatCon :: Alts -> (Alts, Maybe ([Id], Expr))
        findPatCon ((Alt (PatCon contagN idsN) exprN):altsN') | contagP == contagN = (altsN', Just (idsN, exprN))
        findPatCon (altN':altsN') =
            let (altsN'', mAlt) = findPatCon altsN'
            in  (altN':altsN'', mAlt)
        findPatCon [] = ([],Nothing)

combineExpr :: Id -> Expr -> Expr -> Expr
combineExpr nextClause exprP exprN = case (exprP, exprN) of
    (Let (Strict (Bind namePB _)) _
        ,Let (Strict (Bind nameNB exprNB)) exprNL) ->
            let (Let (Strict (Bind _ exprPB)) exprPL) = updateIds (idsRSingleton namePB nameNB) exprP
            in Let (Strict (Bind nameNB (combine exprPB exprNB))) (combine exprPL exprNL)
    (Let (NonRec (Bind namePB _)) _
        ,Let (NonRec (Bind nameNB exprNB)) exprNL) ->
            let (Let (NonRec (Bind _ exprPB)) exprPL) = updateIds (idsRSingleton namePB nameNB) exprP
            in Let (NonRec (Bind nameNB (combine exprPB exprNB))) (combine exprPL exprNL)
    (Let (Rec bindsP) exprPL
        ,Let (Rec bindsN) exprNL) -> -- TODO: update names?
            let binds' = map (\(Bind _ exprPB,Bind nameNB exprNB) -> Bind nameNB (combine exprPB exprNB)) (zip bindsP bindsN)
            in Let (Rec binds') (combine exprPL exprNL)
    (Match namePM altsP
        ,Match nameNM altsN) | namePM == nameNM ->
            let alts' = combineAlts nextClause altsP altsN
            in Match nameNM alts'
    (Ap exprP1 exprP2
        ,Ap exprN1 exprN2) -> Ap (combine exprP1 exprN1) (combine exprP2 exprN2)
    (Lam namePL exprPL
        ,Lam nameNL exprNL) | namePL == nameNL -> Lam nameNL (combine exprPL exprNL)
    (Con conP
        ,Con conN) | conP == conN -> exprN
    (Var namePV
        ,Var nameNV) | namePV == nameNV -> exprN
    (Lit litP
        ,Lit litN) | litP == litN -> exprN
    -- If there is a nextclause in exprP place exprN there and return
    _ | Maybe.isJust (getOcc nextClause (exprOcc exprP)) -> replaceNextClause nextClause exprN exprP
    _ -> internalError "PhaseNormalize" "combineExpr" ("\nnextClause:\n" ++ show nextClause ++ "\nexprP:\n" ++ (show . pretty) exprP  ++ "\nexprN:\n" ++ (show . pretty) exprN)
    where combine = combineExpr nextClause

idsRSingleton :: Id -> Id -> Map Id Id
idsRSingleton x y
    | "\"_\"" == show y = Map.singleton y x
    | otherwise = Map.singleton x y

idsRFromList :: [(Id,Id)] -> Map Id Id
idsRFromList [] = Map.empty
idsRFromList ((x,y):xys) = Map.union (idsRSingleton x y) (idsRFromList xys)

updateIds :: Map Id Id -> Expr -> Expr
updateIds idsR expr = case expr of
    Let (Strict (Bind nameB exprB)) exprL ->
        Let (Strict (Bind (replace nameB) (update exprB))) (update exprL)
    Let (NonRec (Bind nameB exprB)) exprL ->
        Let (NonRec (Bind (replace nameB) (update exprB))) (update exprL)
    Let (Rec binds) exprL ->
        let binds' = map (\(Bind nameB exprB) -> Bind (replace nameB) (update exprB)) binds
        in Let (Rec binds') (update exprL)
    Match nameM alts ->
        let alts' = map (\(Alt pat exprA) -> Alt pat (update exprA)) alts
        in Match (replace nameM) alts'
    Ap expr1 expr2 -> Ap (update expr1) (update expr2)
    Lam nameL exprL -> Lam (replace nameL) (update exprL)
    Con _ -> expr
    Var nameV -> Var (replace nameV)
    Lit _ -> expr
    where update expr' = updateIds idsR expr'
          replace name = Map.findWithDefault name name idsR

replaceDefaults :: Id -> Alts -> Alts
replaceDefaults nextClause alts =
    if Maybe.isJust findDefault
     then map (\(Alt pat exprP) -> Alt pat $ replaceNextClause nextClause defaultExpr exprP) alts
     else alts
    where defaultExpr = Maybe.fromJust findDefault
          findDefault = findDefault' alts
          findDefault' [] = Nothing
          findDefault' (Alt PatDefault exprA:_) = Just exprA
          findDefault' (_:alts') = findDefault' alts'

replaceNextClause :: Id -> Expr -> Expr -> Expr
replaceNextClause nextClause exprN exprP = case exprP of
    Let (Strict (Bind nameB exprB)) exprL ->
        Let (Strict (Bind nameB (replace exprB))) (replace exprL)
    Let (NonRec (Bind nameB exprB)) exprL ->
        Let (NonRec (Bind nameB (replace exprB))) (replace exprL)
    Let (Rec binds) exprL ->
        let binds' = map (\(Bind nameB exprB) -> Bind nameB (replace exprB)) binds
        in Let (Rec binds') (replace exprL)
    Match nameM alts ->
        let alts' = map (\(Alt pat exprA) -> Alt pat (replace exprA)) alts
        in Match nameM alts'
    Ap expr1 _ | leftMostAp expr1 == Var nextClause -> exprN
    Ap expr1 expr2 -> Ap (replace expr1) (replace expr2)
    Lam nameL exprL -> Lam nameL (replace exprL)
    Con _ -> exprP
    Var nameV | nameV == nextClause -> exprN
    Var _ -> exprP
    Lit _ -> exprP
    where replace = replaceNextClause nextClause exprN
          leftMostAp (Ap expr1 _) = leftMostAp expr1
          leftMostAp expr1 = expr1
