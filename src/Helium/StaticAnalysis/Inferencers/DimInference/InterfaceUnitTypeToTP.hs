
module Helium.StaticAnalysis.InterfaceUnitTypeToTP where

unitConsToTp :: UnitCons -> Tp
unitConsToTp (name,exp):l =
    TApp "*" (TApp ("^" ++ show exp) (TCon name)) (normUnitToTp l)

unitVarToTp :: UnitCons -> Tp
unitConsToTp (name,exp):l =
    TApp "*" (TApp ("^" ++ show exp) (TVar name)) (normUnitToTp l)

normUnitToTp :: NormUnit -> Tp
normUnitToTp (uvar, ucons) =
    TApp (TApp (TCon "*") (unitVarToTp uvar)) (unitConsToTp ucons)

normUnitTypeToTp :: NormUnitType -> Tp
normUnitTypeToTp nut =
    case nut of
        App nut1 nut2 -> TApp (normUnitTypeToTp nut1) (normUnitTypeToTp nut2)
        Cons name -> TCon (show name)
        Base nu -> normUnitToTp nu
        Undimensioned -> TCon "Undimensioned"

unitClassEnvironmentToClassEnvironment :: UnitClassEnvironment -> UnitClassEnvironment
unitClassEnvironmentToClassEnvironment =
    map unitClassToClass


unitClassToClass :: UnitClass -> Class
unitClassToClass (ls, uinstances) =
    (ls, map unitPredicateToPredicate uinstances)

unitPredicateToPredicate :: UnitPredicate -> Predicate
unitPredicateToPredicate (Predicate str utp) =
    Predicate str (unitTypeToTp utp)