module Helium.Helium.StaticAnalysis.Inference.DimInference.Normalization(normalizeUnitType) where


normalizeUnitType :: UnitType Unit -> NormUnitType
normalizeUnitType unit =
    case unit of
        Arrow lu u  -> Arrow (map normalizeUnitType lu) (normalizeUnitType u)
        Cons n lu -> Cons n (map normalizeUnitType lu)
        InfixConstructor u1 u2 -> InfixConstructor (normalizeUnitType u1) (normalizeUnitType u2)
        Tuple lu -> Tuple (map normalizeUnitType lu)
        List u -> List (normalizeUnitType u)
        Record lnu -> Record (map (\name, ut -> (name, normalizeUnitType ut)) u)
        Base u -> Base (normalize u)
        Undimensioned -> Undimensioned

normalize :: Unit -> NormUnit
normalize = separeVarandCons . toList . normMap

normMap :: Unit -> M.map Name Int
normMap u =
    case u of
        Unit_Base _ su -> M.singleton (unitName su) 1
        Unit_Parenthesized _ u -> normMap u
        Unit_Times _ prefix term ->
            M.unionWith (+) (normMap prefix) (normMap term)
        Unit_Div _ dividend divisor ->
            M.unionWith (-) (normMap divisor) (normMap dividend)
        Unit_Power _ term exponent ->
            M.map (*exponent) (normMap term)
        Unit_NegPower _ term exponent ->
            M.map (*(-exponent)) (normMap term)
        

separeVarandCons :: [(Name,Int)] -> NormUnit
separeVarandCons unit =
    separeWithAccumulator unit [] []
    where
        separeWithAccumulator :: [(Name,Int)] -> [(Name, Int)] -> [(Name,Int)] -> NormUnit
        separeWithAccumulator [] unitVar unitCons = (unitVar,unitCons)
        separeWithAccumulator (name,int):unit unitVar unitCons =
            if isVariable name then
                separeWithAccumulator unit (name,int):unitVar unitCons
            else
                separeWithAccumulator unit unitVar (name,int):unitCons

unitName :: SimpleUnit -> Name
        unitName SimpleUnit _ n = n

isVariable :: String -> Bool
isVariable (hd:tl) = isLower hd