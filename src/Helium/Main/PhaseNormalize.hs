{-| Module      :  PhaseNormalize
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseNormalize(phaseNormalize) where

import Lvm.Core.Expr(CoreModule)
import Helium.Utils.Utils(internalError)
import Helium.Main.CompileUtils

import Helium.Optimization.Show()
import Lvm.Common.Id(idFromString)
import Lvm.Core.Module(Decl(..),moduleDecls)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..),Pat(..),Con(..))
import qualified Data.Maybe as Maybe
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Either(Either)
import qualified Data.Either as Either
import Data.Set(Set)
import qualified Data.Set as Set
--import qualified Data.Maybe as Maybe
import System.IO.Unsafe(unsafePerformIO)


import Lvm.Common.Id              (Id, NameSupply, newNameSupply, splitNameSupplies)
import Lvm.Core.NoShadow          (coreRename)    -- rename local variables
import Lvm.Core.Saturate          (coreSaturate)  -- saturate constructors, instructions and externs
import Lvm.Core.Normalize         (coreNormalize) -- normalize core, ie. atomic arguments and lambda's at let bindings
import Lvm.Core.LetSort           (coreLetSort)   -- find smallest recursive let binding groups
import Lvm.Core.Lift              (coreLift)      -- lambda-lift, ie. make free variables arguments

import Debug.Trace(trace)
import Text.PrettyPrint.Leijen(Pretty, pretty)
tracePretty :: Pretty a => String -> a -> a
tracePretty s t = trace (s ++ ": \n" ++ (show $ pretty t)) t

traceShow :: Show a => String -> a -> a
traceShow s t = trace (s ++ ": \n" ++ show t) t

phaseNormalize :: String -> CoreModule -> [Option] -> IO CoreModule
phaseNormalize fullName coreModule options = do
    enterNewPhase "Code normalization" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName
    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.beforenormalize") $ show . pretty $ coreModule



    nameSupply <- newNameSupply

    let (coreModule', dbgs) = (normalize nameSupply coreModule)
    writeFile (fullNameNoExt ++ ".core.duringnormalize") (unwords dbgs)

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.afternormalize") $ show . pretty $ coreModule'

    return coreModule'

type DBGS a = (a, [String])

normalize :: NameSupply -> CoreModule -> DBGS CoreModule
normalize supply =
    coreSimplify
  . coreLift
  . coreLetSort
  . coreNormalize supply2
  . coreSaturate supply1
  . coreRename supply0
  where
    (supply0:supply1:supply2:_) = splitNameSupplies supply

{- CoreSimplify -}
coreSimplify :: CoreModule -> DBGS CoreModule
coreSimplify m = (t, dbgs)
    where
    t = m{moduleDecls = mds}
    (mds,dbgs) = foldr (\decl (mds,dbgs) -> case decl of
                    DeclValue _ _ _ expr _ ->
                        let (expr', dbgs') = exprRemoveRename Map.empty expr
                            (expr'', dbgs'') = exprSolidifyMatches expr'
                            (expr''', dbgs''') = exprRemoveDeadLet expr''
                        in (mds ++ [decl{valueValue = expr'''}], dbgs ++ (if expr' == expr'' then [] else ["\nSolidify(only diff):\nbefore:\n" ++ (show . pretty) expr' ++ "\nafter:\n" ++ (show . pretty) expr'' ++ "\n"]){-dbgs'' ++ dbgs' ++ dbgs'''-})
                    _ -> (mds ++ [decl], dbgs)) ([],[]) $ moduleDecls m

{- Remove Dead Let -}
exprRemoveDeadLet :: Expr -> DBGS Expr
exprRemoveDeadLet expr =
    let (after, dbgs) = case expr of
            Let (Strict bind) expr1 ->
                let (bind', dbgs) = bindRemoveDeadLet bind
                    (expr1', dbgs') = exprRemoveDeadLet expr1
                in  (Let (Strict bind') expr1', dbgs ++ dbgs')
            Let binds expr1 ->
                let (binds', dbgs) = bindsRemoveDeadLet binds
                    (expr1', dbgs') = exprRemoveDeadLet expr1
                    bindNames = snd $ bindsOcc binds'
                    occ = exprOcc expr1'
                    simplify = Let binds' expr1'
                in  if anyMember occ bindNames -- Only removes complete let bindings (which are already split for mutual recursion)
                     then (simplify, dbgs ++ dbgs') -- Not a dead let
                     else (expr1', dbgs ++ dbgs') -- Dead let removal
            Match name alts ->
                let (alts', dbgs) = altsRemoveDeadLet alts
                in (Match name alts', dbgs)
            Ap expr1 expr2 ->
                let (expr1', dbgs) = exprRemoveDeadLet expr1
                    (expr2', dbgs') = exprRemoveDeadLet expr2
                in (Ap expr1' expr2', dbgs ++ dbgs')
            Lam name expr1 ->
                let (expr1', dbgs) = exprRemoveDeadLet expr1
                in (Lam name expr1', dbgs)
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

{- Remove Renames -}
type Rename = Map.Map Id Id
exprRemoveRename :: Rename -> Expr -> DBGS Expr
exprRemoveRename renames expr =
    let (after, dbgs) = case expr of
            Let (Strict bind) expr1 ->
                let (renameORbind', dbgs) = bindRename renames bind
                    (expr1', dbgs') = exprRemoveRename renames expr1
                in  case renameORbind' of
                    Left renames' ->
                        let (expr1'', dbgs') = exprRemoveRename renames' expr1
                        in (expr1'', dbgs ++ dbgs')
                    Right bind' -> (Let (Strict bind') expr1', dbgs ++ dbgs')
            Let binds expr1 ->
                let (renamesANDMbinds', dbgs) = bindsRemoveRename renames binds
                    (renames', binds') = case renamesANDMbinds' of
                        Left renames -> (renames, Nothing)
                        Right (binds,renames) -> (renames, (Just binds))
                    (expr1', dbgs') = exprRemoveRename renames' expr1
                in  case binds' of
                    Just binds'' -> (Let binds'' expr1', dbgs ++ dbgs')
                    Nothing -> (expr1', dbgs ++ dbgs')
            Match name alts ->
                let name' = Map.findWithDefault name name renames
                    (alts', dbgs) = altsRemoveRename renames alts
                in  (Match name' alts', dbgs)
            Ap expr1 expr2 ->
                let (expr1', dbgs') = exprRemoveRename renames expr1
                    (expr2', dbgs'') = exprRemoveRename renames expr2
                in (Ap expr1' expr2', dbgs' ++ dbgs'')
            Lam name expr1 ->
                let (expr1', dbgs) = exprRemoveRename renames expr1
                in (Lam name expr1', dbgs)
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
bindRemoveRename renames (Bind name rename@(Var name')) = (Left $ Map.union renames $  Map.singleton name (Map.findWithDefault name' name' renames), [])
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

unpackdbgs :: [DBGS a] -> DBGS [a]
unpackdbgs [] = ([],[])
unpackdbgs ((a,dbgs):dbgsas) =
    let (as, dbgs') = unpackdbgs dbgsas
    in  (a:as, dbgs ++ dbgs')

{- Solidify Matches-}
mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a,f b)

leading :: String -> String -> Bool
leading leading string = (all (\(l,s) -> l == s) (zip leading string)) && (length leading <= length string)
leadingNextClause :: String -> Bool
leadingNextClause = leading "\"nextClause$"
leadingGuard :: String -> Bool
leadingGuard = leading "\"guard$"

exprSolidifyMatches :: Expr -> DBGS Expr
exprSolidifyMatches expr =
    let (after, dbgs) = case expr of
            Let (Strict (Bind nameB exprB)) (Match nameM (Alt (PatCon (ConId trueId) []) exprA:alts))
                | nameB == nameM --leadingGuard (show nameB) &&
                && exprB == Var (idFromString "otherwise") -> (exprA, ["\nSolidify useless otherwise removed"])
            Let (NonRec (Bind nameNB exprNB)) exprN@(Let bindS@(Strict (Bind nameSB exprSB)) (Match nameM alts))
                | leadingNextClause (show nameNB)
                && nameSB == nameM ->
                let (exprNB', dbgs) = exprSolidifyMatches exprNB
                    (exprN', dbgs') = exprSolidifyMatches exprN
                    expr' = Let (NonRec (Bind nameNB exprNB')) exprN'

                    (exprSB', dbgs'') = exprSolidifyMatches exprSB
                    (alts', dbgs''') = mapSnd concat $ unzip $ map (\(Alt pat exprA) ->
                        let (exprA', dbgs) = exprSolidifyMatches exprA
                        in (Alt pat exprA', dbgs)) alts

                    (expr'', dbgs'''') = case exprSolidify exprSB' exprNB' of
                        (Just (alts'',bindss), dbgs) ->
                            let combAlts = combineAlts nameNB alts' alts''
                            in (foldr (Let) (Let bindS (Match nameM combAlts)) bindss, ("\ncombining alts:\n" ++ (show . pretty) alts' ++ "\nand alts':\n" ++ (show . pretty) alts'' ++ "\ncombAlts:\n" ++ (show . pretty) combAlts):dbgs)
                        (Nothing, dbgs) -> (expr', dbgs)

                in (expr'', dbgs ++ dbgs' ++ dbgs'' ++ dbgs''' ++ dbgs'''' ++ [("\nSolidify: nextclause encountered" ++ (if expr' /= expr'' then "\nbefore:\n" ++ ((show . pretty) expr') ++ "\nafter:\n" ++ ((show . pretty) expr'') else "\nnot solidified:\n" ++ (show.pretty) expr''))])
            Let (Strict (Bind nameB exprB)) exprL ->
                let (exprB', dbgs) = exprSolidifyMatches exprB
                    (exprL', dbgs') = exprSolidifyMatches exprL
                in (Let (Strict (Bind nameB exprB')) exprL', dbgs ++ dbgs')
            Let (NonRec (Bind nameB exprB)) exprL ->
                let (exprB', dbgs) = exprSolidifyMatches exprB
                    (exprL', dbgs') = exprSolidifyMatches exprL
                in (Let (NonRec (Bind nameB exprB')) exprL', dbgs ++ dbgs')
            Let (Rec binds) exprL ->
                let (binds', dbgs') =  mapSnd concat $ unzip $ map (\(Bind nameB exprB) ->
                        let (exprB', dbgs) = exprSolidifyMatches exprB
                        in (Bind nameB exprB', dbgs)) binds
                    (exprL', dbgs'') = exprSolidifyMatches exprL
                in (Let (Rec binds') exprL', dbgs' ++ dbgs'')
            Match name alts ->
                let (alts', dbgs') = mapSnd concat $ unzip $ map (\(Alt pat exprA) ->
                        let (exprA', dbgs) = exprSolidifyMatches exprA
                        in (Alt pat exprA', dbgs)) alts
                in (Match name alts', dbgs')
            Ap expr1 expr2 ->
                let (expr1', dbgs) = exprSolidifyMatches expr1
                    (expr2', dbgs') = exprSolidifyMatches expr2
                in (Ap expr1' expr2', dbgs ++ dbgs')
            Lam name expr1 ->
                let (expr1', dbgs) = exprSolidifyMatches expr1
                in (Lam name expr1', dbgs)
            Con _ -> (expr, [])
            Var _ -> (expr, [])
            Lit _ -> (expr, [])
    in (after, (if True{-expr == after-} then dbgs else ("\nSolidify:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) after ):dbgs))

exprSolidify :: Expr -> Expr -> DBGS (Maybe (Alts,[Binds]))
exprSolidify exprName expr = case expr of
    Let (Strict (Bind nameSB exprSB)) (Match nameM alts)
        | nameSB == nameM
        && exprName == exprSB -> (Just (alts,[]), ["\nFound match: " ++ show nameM])
    Let binds expr -> case exprSolidify exprName expr of
        (Just (alts,bindss),dbgs) -> (Just (alts,binds:bindss),("\nFound let: " ++ namesFromBinds binds ++ ": solidifying"):dbgs)
        (Nothing,dbgs) -> (Nothing,("\nFound let: " ++ namesFromBinds binds ++ ": not solidifying"):dbgs)
    Lam name exprL ->
        let (m, dbgs) = exprSolidify exprName exprL
        in (m, ("\nLam: " ++ show name):dbgs)
    _ -> (Nothing, ["\nNot a let"])
    where namesFromBinds :: Binds -> String
          namesFromBinds (Strict (Bind nameB _)) = show nameB
          namesFromBinds (NonRec (Bind nameB _)) = show nameB
          namesFromBinds (Rec binds) = unwords $ map (\(Bind nameB _) -> show nameB) binds

altsRemovePatDefault :: Alts -> Alts
altsRemovePatDefault [] = []
altsRemovePatDefault (Alt PatDefault _:alts) = alts
altsRemovePatDefault (alt:alts) = alt:altsRemovePatDefault alts

combineAlts :: Id -> Alts -> Alts -> Alts
combineAlts nextClause [] altsN = altsN
combineAlts nextClause altsP [] = altsP
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
    (Let (Strict (Bind namePB exprPB)) exprPL
        ,Let (Strict (Bind nameNB exprNB)) exprNL) ->
            let (Let (Strict (Bind namePB' exprPB')) exprPL') = updateIds (idsRSingleton namePB nameNB) exprP
            in Let (Strict (Bind nameNB (combine exprPB' exprNB))) (combine exprPL' exprNL)
    (Let (NonRec (Bind namePB exprPB)) exprPL
        ,Let (NonRec (Bind nameNB exprNB)) exprNL) ->
            let (Let (NonRec (Bind namePB' exprPB')) exprPL') = updateIds (idsRSingleton namePB nameNB) exprP
            in Let (NonRec (Bind nameNB (combine exprPB exprNB))) (combine exprPL exprNL)
    (Let (Rec bindsP) exprPL
        ,Let (Rec bindsN) exprNL) -> -- TODO: update names?
            let binds' = map (\(Bind namePB exprPB,Bind nameNB exprNB) -> Bind nameNB (combine exprPB exprNB)) (zip bindsP bindsN)
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
    where update expr = updateIds idsR expr
          replace name = Map.findWithDefault name name idsR

replaceDefaults :: Id -> Alts -> Alts
replaceDefaults nextClause alts =
    if Maybe.isJust findDefault
     then map (\(Alt pat exprP) -> Alt pat $ replaceNextClause nextClause defaultExpr exprP) alts
     else alts
    where defaultExpr = Maybe.fromJust findDefault
          findDefault = findDefault' alts
          findDefault' [] = Nothing
          findDefault' (Alt PatDefault defaultExpr:_) = Just defaultExpr
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
    Ap expr1 expr2 | leftMostAp expr1 == Var nextClause -> exprN
    Ap expr1 expr2 -> Ap (replace expr1) (replace expr2)
    Lam nameL exprL -> Lam nameL (replace exprL)
    Con _ -> exprP
    Var nameV | nameV == nextClause -> exprN
    Var _ -> exprP
    Lit _ -> exprP
    where replace = replaceNextClause nextClause exprN
          leftMostAp (Ap expr1 _) = leftMostAp expr1
          leftMostAp expr1 = expr1

{- Occurences -}
exprOcc :: Expr -> Occ
exprOcc expr = case expr of
    Let (Strict bind) expr1 ->
        let (occ1, bindNames) = bindOcc bind
            occ2 = exprOcc expr1
        in  removeNames (combineOcc occ1 occ2) bindNames
    Let binds expr1 ->
        let (occ1, bindNames) = bindsOcc binds
            occ2 = exprOcc expr1
        in  if anyMember occ2 bindNames
             then removeNames (combineOcc occ1 occ2) bindNames
             else occ2
    Match name alts ->
        let occ1 = useOcc name
            occ2 = altsOcc alts
        in  combineOcc occ1 occ2
    Ap expr1 expr2 ->
        let occ1 = (exprOcc expr1)
            occ2 = (exprOcc expr2)
        in  combineOcc occ1 occ2
    Lam name expr1 ->
        let occ = exprOcc expr1
        in  deleteOcc name occ
    Con con -> conOcc con
    Var name -> useOcc name
    Lit _ -> noOcc

bindsOcc :: Binds -> (Occ,Names)
bindsOcc (NonRec bind) = bindOcc bind
bindsOcc (Strict bind) = bindOcc bind
bindsOcc (Rec binds) = foldr (\(occ,name) (occs,names) -> (combineOcc occ occs, Set.union name names)) (noOcc,Set.empty) (map bindOcc binds)

bindOcc :: Bind -> (Occ,Names)
bindOcc (Bind name expr) = (exprOcc expr, Set.singleton name)

altsOcc :: Alts -> Occ
altsOcc alts = foldr combineOcc noOcc (map altOcc alts)

altOcc :: Alt -> Occ
altOcc (Alt pat expr) =
    let occ = exprOcc expr
        patNames = patIntro pat
    in  removeNames occ patNames

patIntro :: Pat -> Names
patIntro (PatCon _ ids) = Set.fromList ids
patIntro _ = Set.empty

conOcc :: Con Expr -> Occ
conOcc con = case con of
    ConId _ -> noOcc
    ConTag tag _ -> exprOcc tag

{- Occ -}
type Occ = Map Id Int
type Names = Set Id

combineOcc :: Occ -> Occ -> Occ
combineOcc = Map.unionWith (+)

removeNames :: Occ -> Names -> Occ
removeNames m s = Map.filterWithKey (\k _ -> k `Set.notMember` s) m

anyMember :: Occ -> Names -> Bool
anyMember occ names = foldr (\name bool -> bool || (Map.member name occ)) False names

noOcc :: Occ
noOcc = Map.empty

useOcc :: Id -> Occ
useOcc name = Map.singleton name 1

getOcc :: Id -> Occ -> Maybe Int
getOcc = Map.lookup

deleteOcc :: Id -> Occ -> Occ
deleteOcc = Map.delete
