
{-| Module      :  Unification
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    The data type of normalized Unit
-}

module Helium.StaticAnalysis.Inferencers.DimInference.NormUnit where


type UnitVar  = [(Name,Int)]
type UnitCons = [(Name,Int)]
type NormUnit = (UnitVar, UnitCons)

---------------------------- Useful functions on units ------------------------

op_on_exp :: (Int -> Int) -> NormUnit -> NormUnit
op_on_exp f (uvar, ucons)
    (map (\n,int -> (n, f int) ) uvar,
     map (\n,int -> (n, f int) ) ucons)

mult :: [(Name, Int)] -> [(Name, Int)] 
-- if sorted by Name and they are because toList return an ordered List
mult (n1, int1):q1 (n2,int2):q2 =
    if n1 == n2 then
        (n1, int1 * int2):(mult q1 q2)
    else if n1 < n2 then
        (n1, int1):(mult q1 (n2,int2):q2)
    else
        (n2, int2):(mult (n1,int1):q1 q2)

multiply :: NormUnit -> NormUnit -> NormUnit
multiply (uvar1, ucons1) (uvar2, ucons2) =
    (mult uvar1 uvar2, mult ucons1 ucons2)

inverse :: NormUnit -> NormUnit
inverse (uvar, ucons) = op_on_exp (-)

power :: NormUnit -> Int -> Unit
power (uvar, ucons) exp = op_on_exp (*exp)

divide :: NormUnit -> NormUnit -> NormUnit
divide u1 u2 = 
    multiply u1 (inverse u2)