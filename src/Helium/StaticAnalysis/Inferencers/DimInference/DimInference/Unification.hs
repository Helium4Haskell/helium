
type UnitCons = [(Name,Int)]
type UnitVar  = [(Name,Int)]
type Unit = (UnitVar, UnitCons)

data Unfier = Fail | Substitution M.Map Name Unit


compose:: (Name, Unit) -> Unifier
compose mapu maps =
    case M.lookup 


apply_substitution :: (Name,Unit) -> Unit -> Unit
apply_substitution map (uvar, ucons) =


unifyOne :: (UnitVar, UnitCons) -> Unifier
unifyOne [] [] = Substitution M.empty
unifyOne [] _  = Fail
unifyOne [(n,x)] lcons =
    if all (\(_,int) -> int mod x == 0) lcons then
        M.singleton (n,map ((name,int) -> (name, int/x)) lcons)
    else Fail
unifyOne (x:q) lcons =
    let u = (n,map ((name,int) -> (name, floor int/x)) lcons) in
    let (uvar, ucons) = apply_substitution u  in
    let s = unifyOne (map uvar ucons)
    compose u s