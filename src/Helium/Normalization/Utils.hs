module Helium.Normalization.Utils where

import Lvm.Common.Id(Id)
import Lvm.Core.Expr(Expr(..),Binds(..),Bind(..),Alts,Alt(..),Pat(..),Con(..))

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
{-
import qualified Data.Maybe as Maybe
import Data.Either(Either)
import qualified Data.Either as Either
-}
mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a,f b)

type DBGS a = (a, [String])

unpackdbgs :: [DBGS a] -> DBGS [a]
unpackdbgs = (mapSnd concat) . unzip

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
