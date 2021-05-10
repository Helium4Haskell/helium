module Helium.CodeGeneration.Iridium.RegionSize.Parse
where

import Lvm.Core.Type hiding (showType, typeReindex, typeWeaken)

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints

import Data.List (elemIndex)
import Data.Map (fromList)

-- | TODO: Split names into two: Quants and vars 
-- | Parse an annotation
pAnnotation :: [String] -> Parser Annotation
pAnnotation names = do
    c <- lookahead
    case c of
        _ -> do
            ann1 <- pAnnotation' names
            pWhitespace'
            args <- pMany (pAnnMany names) pIsNext
            return $ foldr ($) ann1 args


pIsNext :: Parser Bool
pIsNext = do
    c <- lookahead
    return $ c == '⊕' 
          || c == '⊔' 
          || c == '<'
          || c == '{'

pAnnMany :: [String] -> Parser (Annotation -> Annotation)
pAnnMany names = do
    pWhitespace'
    c <- lookahead
    case c of
        '⊕' -> pChar >> pWhitespace' >> flip AAdd <$> pAnnotation' names
        '⊔' -> pChar >> pWhitespace' >> flip AJoin <$> pAnnotation' names
        '<' -> do
            pToken '<'
            pWhitespace'
            ann2 <- pAnnotation names
            pWhitespace'
            pToken '>'
            pWhitespace'
            return $ flip AApl ann2 
        '{' -> do
            pToken '{'
            ty <- pType' names
            pToken '}'
            pWhitespace'
            return $ flip AInstn ty 
        _ -> return id
    

-- | Parse an annotation
pAnnotation' :: [String] -> Parser Annotation
pAnnotation' names = do
    pWhitespace'
    c <- lookahead
    case c of
        -- Parens 
        '(' -> do
            pToken '('
            ann <- pAnnotation names
            pWhitespace'
            pToken ')'
            return ann
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
        -- Bot
        '⊥' -> do 
            pToken '⊥' 
            pToken '[' 
            sort <- pSort names
            pToken ']'
            return (ABot sort)
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
                    pToken ':'
                    sort <- pSort names
                    pToken ']'
                    return $ ATop sort constr
        -- Projection
        'π' -> do
            pToken 'π'
            pToken '_'
            idx <- pUnsignedInt
            pToken '['
            ann <- pAnnotation names
            pToken ']'
            return $ AProj idx ann
        -- Fixpoint & var
        _ -> do 
            name1 <- pRsName
            case name1 of
                "fix" -> do
                    pWhitespace'
                    name2 <- pRsName
                    pWhitespace'
                    pToken ':'
                    pWhitespace'
                    sort <- pSort names
                    pWhitespace'
                    pToken '.'
                    pWhitespace'
                    anns <- pArgumentsWith '[' ']' $ pAnnotation (name2:names)
                    return $ AFix sort anns
                _ -> return $ AVar (getIdx names name1)

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
        'C' -> pToken 'C' >> return SortConstr
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
            pWhitespace'
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
            pToken '_'
            c2 <- lookahead
            case c2 of
                'g' -> RegionGlobal <$ pSymbol "global"
                'b' -> RegionBottom <$ pSymbol "bottom"
                _ -> pError $ "Expected global or bottom, got: " ++ (c2:[]) 
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
