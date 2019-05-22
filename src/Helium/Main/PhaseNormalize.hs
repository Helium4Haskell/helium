{-| Module      :  PhaseNormalize
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseNormalize(phaseNormalize) where

import Lvm.Core.Expr(CoreModule)
import Helium.Main.CompileUtils

import Helium.Optimization.Show()
import Lvm.Core.Module(Decl(..),moduleDecls)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..),Pat(..),Con(..))
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
  . coreRename supply3
  . coreLift
  . coreLetSort
  . coreNormalize supply2
  . coreSaturate supply1
  . coreRename supply0
  where
    (supply0:supply1:supply2:supply3:_) = splitNameSupplies supply

{- CoreSimplify -}
coreSimplify :: CoreModule -> DBGS CoreModule
coreSimplify m = (t, dbgs)
    where
    t = m{moduleDecls = mds}
    (mds,dbgs) = foldr (\decl (mds,dbgs) -> case decl of
                    DeclValue _ _ _ expr _ ->
                        let (expr', dbgs') = exprRemoveDeadLet expr
                            (expr'', dbgs'') = exprRemoveRename Map.empty expr'
                        in (mds ++ [decl{valueValue = expr''}], dbgs ++ dbgs' ++ dbgs'')
                    _ -> (mds ++ [decl], dbgs)) ([],[]) $ moduleDecls m

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
    in (after, (if expr == after then "" else ("\nDeadLet:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) after )):dbgs)

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
    in (after, (if expr == after then "" else ("\nRename:\nbefore:\n" ++ (show . pretty) expr ++ "\nafter:\n" ++ (show . pretty) after )):dbgs)

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

--getOcc :: Id -> Occ -> Maybe Int
--getOcc = Map.lookup

deleteOcc :: Id -> Occ -> Occ
deleteOcc = Map.delete
