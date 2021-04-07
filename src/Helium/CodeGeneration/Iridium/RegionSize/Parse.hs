module Helium.CodeGeneration.Iridium.RegionSize.Parse
where

import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints

import Data.List (elemIndex)
import Data.Map (fromList)

-- | Parse an annotation
pAnnotation :: [String] -> Parser Annotation
pAnnotation names = do
    c <- lookahead
    case c of
        -- Parens 
        '(' -> do
            pToken '('
            ann <- pAnnotation names
            pToken ')'
            return ann
        _ -> do
            ann1 <- pAnnotation' []
            pWhitespace'
            c2 <- lookahead
            case c2 of
                '⊕' -> pChar >> AAdd  ann1 <$> pAnnotation' names
                '⊔' -> pChar >> AJoin ann1 <$> pAnnotation' names
                '<' -> do
                    pToken '<'
                    ann2 <- pAnnotation' names
                    pToken '>'
                    return $ AApl ann1 ann2 
                '{' -> do
                    pToken '{'
                    ty <- pType' names
                    pToken '}'
                    return $ AInstn ann1 ty 
                _    -> return ann1
            

-- | Parse an annotation
pAnnotation' :: [String] -> Parser Annotation
pAnnotation' names = do
    pWhitespace'
    c <- lookahead
    case c of
        -- Constraint set
        '{' -> AConstr <$> pConstr names
        -- Region 
        'ρ' -> AReg <$> pRegionVar
        -- Quantification
        '∀' -> do
            pToken '∀'
            pWhitespace'
            name <- pRsName
            pToken '.'
            pWhitespace'
            AQuant <$> pAnnotation (name:names)
        -- Lambda
        'λ' -> do 
            pToken 'λ'
            name <- pRsName
            pToken ':'
            sort <- pSort names
            pToken '.'
            pWhitespace'
            ALam sort <$> pAnnotation (name:names)
        -- Fixpoint
        'f' -> do 
            pSymbol "fix"
            pWhitespace'
            name <- pRsName
            pWhitespace'
            pToken ':'
            pWhitespace'
            sort <- pSort names
            pWhitespace'
            pToken '.'
            pWhitespace'
            anns <- pArgumentsWith '[' ']' $ pAnnotation (name:names)
            return $ AFix sort anns
        -- Bot
        '⊥' -> pToken '⊥' >> return (ABot undefined) -- TODO: Sort of bot
        -- Tuples/top
        'T' -> do
            pToken 'T'
            c2 <- lookahead
            case c2 of
                'U' -> do
                    pSymbol "UP"
                    anns <- pArguments $ pAnnotation names
                    return $ ATuple anns
                _ -> do 
                    pToken '['
                    constr <- pConstr names
                    pToken ']'
                    -- TODO: Sort of top
                    return $ ATop undefined constr
        -- Projection
        'π' -> do
            pToken 'π'
            pToken '_'
            idx <- pUnsignedInt
            pToken '['
            ann <- pAnnotation names
            pToken ']'
            return $ AProj idx ann
        _ -> do
            name <- pRsName
            return $ AVar (getIdx names name)

-- | Parse a sort
pSort :: [String] -> Parser Sort
pSort names = do
    sort1 <- pSort' names
    pWhitespace'
    c <- lookahead
    case c of 
        '↦' -> do
            pToken '↦' 
            pWhitespace'
            SortLam sort1 <$> pSort' names
        _ -> return sort1 

pSort' :: [String] -> Parser Sort
pSort' names = do
    c <- lookahead
    case c of
        'C' -> return SortConstr
        -- Region sorts
        'P' -> do
            pToken 'P'
            c2 <- lookahead
            case c2 of
                '<' -> do 
                    (idx, types) <- pPolySort names
                    return $ SortPolyRegion idx types
                _   -> return SortMonoRegion 
        -- Poly sort
        'Ψ' -> do
            pToken 'Ψ'
            (idx, types) <- pPolySort names
            return $ SortPolySort idx types
        -- Quantification
        '∀' -> do
            pToken '∀'
            name <- pRsName
            pToken '.'
            pWhitespace'
            SortQuant <$> pSort (name:names)
        -- Parens 
        '(' -> do
            pToken '('
            sort <- pSort names
            pToken ')'
            return sort
        -- Tuples
        'T' -> do
            pSymbol "TUP"
            sorts <- pArguments $ pSort names
            return $ SortTuple sorts
        c   -> pError $ c:[] 

-- | Parse a polymorphic sort <name [t1,t2,..]>
pPolySort :: [String] -> Parser (Int, [Type])
pPolySort names = do
    pToken '<'
    pWhitespace'
    name <- pRsName
    let idx = getIdx names name
    pWhitespace'
    types <- pArgumentsWith '[' ']' $ pType' names
    pToken '>'
    return (idx, types)

-- | Parse a constraint set
pConstr :: [String] -> Parser Constr
pConstr names = do
    pWhitespace'
    constrs <- pArgumentsWith '{' '}' $ pConstraints names
    pWhitespace'
    return $ fromList constrs

pConstraints ::  [String] -> Parser (ConstrIdx,Bound)
pConstraints names = do
    idx <- pConstrIdx names
    pWhitespace'
    pToken '↦'
    pWhitespace'
    pWhitespace'
    bound <- pBound
    return (idx,bound)

pConstrIdx :: [String] -> Parser ConstrIdx
pConstrIdx names = do
    c <- lookahead
    case c of
        'ρ' -> Region <$> pRegionVar
        _   -> do 
            name <- pRsName
            let idx = getIdx names name
            projs <- pProjs
            return $ foldr CnProj (AnnVar idx) projs

pProjs :: Parser [Int]
pProjs = do
    c <- lookahead
    case c of 
        '.' -> do
            pToken '.'
            n <- pUnsignedInt
            (:) n <$> pProjs
        _   -> return []

pBound :: Parser Bound
pBound = do
    c <- lookahead
    case c of
        '∞' -> pToken '∞' >> return Infty
        _   -> Nat <$> pUnsignedInt

-- | Parse a region variable
pRegionVar :: Parser RegionVar
pRegionVar = do        
    pToken 'ρ'
    c <- lookahead
    case c of
        '_' -> do
            c2 <- lookahead
            case c2 of
                'g' -> RegionGlobal <$ pSymbol "global"
                'b' -> RegionBottom <$ pSymbol "bottom"
                _ -> pError "Expected global or bottom" 
        _ -> do
            idx <- pSubscriptInt
            return $ RegionLocal idx


-- | Get the index from an array
getIdx :: [String] -> String -> Int
getIdx names name = 
    case name `elemIndex` names of
        Just i  -> i
        Nothing -> -1 

-- | Parse a name
pRsName :: Parser String
pRsName = do
    c <- lookahead
    if c == '"' then
      pString
    else
      pSomeSatisfy "expected name" valid
  where
    valid c
      = ('a' <= c && c <= 'z')
      || ('A' <= c && c <= 'Z')
      || ('0' <= c && c <= '9')
      || c == '_'
