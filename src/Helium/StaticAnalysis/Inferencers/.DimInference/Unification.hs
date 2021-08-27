{-| Module      :  Unification
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    Perform the unification of dimension types
-}

module Helium.StaticAnalysis.Inferencers.DimInference.Unification where

import Helium.StaticAnalysis.Inferencers.DimInference.DimUtils
import Helium.StaticAnalysis.Inferencers.DimInference.NormUnit
import Helium.StaticAnalysis.Inferencers.DimInference.Normalization (normalize)
import Helium.StaticAnalysis.Inferencers.DimInference.Unifier

------------------------------------------------------------------------------------------
------------------------------- Unification ----------------------------------------------
------------------------------------------------------------------------------------------

constraint_solver ::  UnitConstraints -> Either Fail Unifier
constraint_solver lunitconst =
    let normlunitconst = map (\x,y -> (normalize x, normalize y)) lunitconst
    foldr
        (\(ut1, ut2), subst ->
            let nut1, nut2 = (apply subst ut1, apply subst ut2) in
            unify nut1 nut2 M.empty)
    M.empty
    normlunitconst

unify :: NormUnitType -> NormUnitType -> M.Map Name NormUnitType -> (M.Map Name NormUnitType, Either Fail Unifier)
unify ut1 ut2 tvarToNUT = case (ut1, ut2) of
    (UTApp a1 b1, UTApp a2 b2) ->
        case unify a1 a2 of
            map, Right unifier1 -> 
                let nb1, nb2 = apply unifier1 b1, apply unifier1 b2 in
                case unify nb1 nb2 map of
                    _, Right unifier2 -> compose unifier2 unifier1
                    _ -> Left Fail
            _ -> Left Fail
    (UTCon a, UTCon b) ->
        if a == b then Right M.empty
        else internalError "Type inference should not have worked"
    (UTVar v1, _) -> case M.lookup v1 tvarToNUT of
        Just nut1 -> unify nut1 ut2 tvarToNUT
        Nothing -> (M.insert v1 ut2 tvarToNUT, M.empty)
    (_, UTVar v2) -> unify ut2 ut1 tvarToNUT
    -- Base case --
    (Base u1, Base u2) -> unifyOne (divide u1 u2)
    (QuestionMark, a) -> Right M.empty
    (a, QuestionMark) -> Right M.empty
    (Undimensioned, Undimensioned) -> Right M.empty
    (Undimensioned, u) -> Left Fail
    (u, Undimensioned) -> Left Fail
    _ -> internalError "Type inference should not have worked"

unifyOne :: NormUnit -> Either Fail Unifier
unifyOne ([], []) = Right M.empty
unifyOne ([], _)  = Left Fail
unifyOne ([(n,x)], lcons) =
    if all (\(_,int) -> int mod x == 0) lcons then
        Right M.singleton (n,map (\(name,int) -> (name, - int/x)) lcons)
    else Left Fail
unifyOne ((n,x):q, lcons) =
    if x == 0 then
        unifyOne q lcons
    else
        let u = (n, map (\(name,int) -> (name, - floor int/x)) (q++lcons)) in
        let (uvar, ucons) = apply_substitution x (q,lcons) in
        let res = unifyOne uvar ucons in
        case res of
            Right s -> compose_one s u -- s o u
            Left Fail -> Left Fail

------------------------------------------------------------------------------------------
------------------------------- Tools ----------------------------------------------------
------------------------------------------------------------------------------------------


reduce_power :: Int -> (Name, Int) -> (Name, Int)
reduce_power x (name, int) =
    (name, int mod x) -- int - (floor int/x) * x

suppr_zero :: [Int] -> [Int]
suppr_zero [] = []
suppr_zero h:q =
    if h == 0 then suppr_zero q
    else h:q

insertion :: (Name, Int) -> UnitVar -> UnitVar -- insert in a sorted list
insertion (n,x) [] = [(n,x)]
insertion (n,x) (n',x'):q =
    if n <= n' then
        (n,x):(n',x'):q
    else (n',x'): (insertion (n,x) q)

{-
apply_substitution x_1  ([(v_1, x_1), ..., (v_m, x_m)],[(C_1, y_1), ... (C_n, y_n)])
apply to unit = v_1 ^ x_1 . ... v_m ^ x_m . C_1 ^ y_1 . ... C_n ^ y_n the substitution
 {v_1 -> v_1 . v_2 ^ -(floor x_2/ x_1) . ... . v_m ^ -(floor x_m/ x_1)
  . C_1 ^ -(floor y_1 / x_1) . ... . C_n ^( floor y_n / x_1)}
-}
apply_substitution :: (Name,Int) -> NormUnit -> NormUnit
apply_substitution (n,x) (uvar, ucons) =
    let nuvar, nucons = 
        ( suppr_zero ( sortOn (abs . snd) (map (reduce_power x) uvar) ),
          suppr_zero ( sortOn (abs . snd) (map (reduce_power x) ucons) ) )
    in -- sorted regarding to the abs of the exponents, suppressing zero
    (insertion (n,x) nuvar, nucons)



