{-| Module      :  Unification
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    Tools for unifier
-}

module Helium.StaticAnalysis.Inferencers.DimInference.Unifier where

type Unifier = M.Map Name NormUnit

------------------------ Useful functions on substitution ---------------------

-- Apply f to Base components
apply_to_base :: UTp a -> (a -> a) -> UTp a 
apply_to_base utp f = case utp of
    UTApp ut1 ut2 -> UTApp (apply_to_base ut1) (apply_to_base ut2)
    Base a -> Base (f a)
    u -> u

-- Apply the substitution to an unit type
apply :: Unifier -> NormUnitType -> NormUnitType
apply subst utp = apply_to_base utp (\a -> substitute a subst)

-- Apply the substitution to an unit
substitute :: NormUnit -> Unifier -> NormUnit
substitute (uvar, ucons) subst =
    M.foldr
        (\n, u ->
            let pow, uvar' =  pop n uvar in
            -- to sort by name first: n log n then n better than n^2
            multiply (uvar', ucons) (u `power` pow)
        )
    subst

-- Compose a substitution with a single-name-substitution
compose_one :: Unifier -> (Name, NormUnit) -> Unifier
compose_one subst (name, (luvar, lucons)) =
    L.foldl
    (\(varname, int) nu@(built_luvar, built_lucons) ->
        case M.lookup varname subst of
            Just nunit ->
                multiply (power nunit 5) nu
            Nothing -> 
                ((varname, int):built_luvar, built_lucons)

    )
    ([], lucons)
    luvar
    M.insert name

-- Compose a substitution with another : compose u1 u2 = u1 o u2
compose :: Unifier -> Unifier -> Unifier
compose unifier1 unifier2 =
    M.map (compose_one unifier1) unifier2

-- pop from uvar the element 
pop :: Name -> UnitVar -> (Int, UnitVar)
pop n [] = 
    internalError "Unknow unit variable"
pop n ((name,int):uvar) =
    if name == n then
        int, uvar
    else
        let power, uvar' = pop n uvar in
            power, (name,int):uvar'
