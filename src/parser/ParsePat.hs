module ParsePat(pat, pat10, apat) where

import HaskellLexer hiding (conid, varid)
import UHA_Syntax(Pattern(..), Name(..))
import ParseCommon
import Parsec

{-
pat  ->  pat0  
pati  ->  pati+1 [conop(n,i) pati+1]  
 |  lpati  
 |  rpati  
lpati  ->  (lpati | pati+1) conop(l,i) pati+1  
lpat6  ->  - (integer | float)  (negative literal)  
rpati  ->  pati+1 conop(r,i) (rpati | pati+1)  

See noRange in ParseCommon for an explanation of the parsing of infix expressions.

-}

pat :: HParser Pattern
pat = addRange $
    do  
        u <- unaryMinusPat
        p <- pat10
        ps <- fmap concat $ many $
            do
                o <- do { n <- conop; return (Pattern_Variable noRange n) }
                u <- unaryMinusPat
                p <- pat10
                return ([o] ++ u ++ [p])
        return $ \r -> Pattern_List noRange (u ++ [p] ++ ps)
        
unaryMinusPat :: HParser [Pattern]
unaryMinusPat = option [] $
    try (do 
        (_, r) <- withRange (special "-.") 
        return [Pattern_Variable noRange (Name_Identifier r [] floatUnaryMinusName)]
    )
    <|>
    do 
        (_, r) <- withRange (special "-") 
        return [Pattern_Variable noRange (Name_Identifier r [] intUnaryMinusName)]
    
{-
pat10   ->  con apat*
         |  apat  
-}

pat10 :: HParser Pattern
pat10 = addRange (
    do  
        n  <- try con    
        ps <- many apat
        return $ \r -> Pattern_Constructor r n ps
    )
    <|>
    apat
    <?> "pattern"
       
{-
apat    ->  var ( "@" apat )?

         |  "(" ")"
         |  "(" pat ")"  (parenthesized pattern)  
         |  "(" pat1 "," ... "," patk ")"  (tuple pattern, k>=2)  

         |  "[" "]" 
         |  "[" pat1 "," ... "," patk "]"  (list pattern, k>=1)  

         |  "_"  (wildcard)  
         |  con  (arity con = 0)  
         |  literal  
-}

apat :: HParser Pattern
apat = addRange (
    do
        v <- try var -- because of parentheses
        option (\r -> Pattern_Variable r v) $ do
            reservedOp "@"
            p <- apat
            return $ \r -> Pattern_As r v p
    <|>
    do
        ps <- parens (commas pat)
        return $ \r -> case ps of
            [] -> Pattern_Constructor r (Name_Special r [] "()") []
            [p] -> Pattern_Parenthesized r p
            _ -> Pattern_Tuple r ps
    <|>
    do
        ps <- brackets (commas pat)
        return $ \r -> case ps of
            [] -> Pattern_Constructor r (Name_Special r [] "[]") []
            _ -> Pattern_List r ps
    <|> 
    do
        reserved "_"
        return $ \r -> Pattern_Wildcard r
    <|>
    do
        n <- con
        return $ \r -> Pattern_Constructor r n []
    <|>
    do
        l <- literal
        return $ \r -> Pattern_Literal r l
    ) <?> "pattern"
