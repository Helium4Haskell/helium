module ParseCommon
    ( withRange, addRange, noRange
    , brackets, commas, parens, commas1
    , tyvar, tycon, modid, conid, var, con, conop, varop, op
    , varid, conid
    , literal
    , semi, lcurly, rcurly
    , intUnaryMinusName, floatUnaryMinusName
    ) where

import HaskellLexer hiding (conid, varid)
import qualified HaskellLexer
import UHA_Utils(noRange)
import UHA_Syntax(Range(..), Position(..), Name(..), Literal(..))
import Parsec

withRange :: HParser a -> HParser (a, Range)
withRange p = addRange (do { x <- p; return (\r -> (x, r)); })

addRange :: HParser (Range -> a) -> HParser a
addRange p =
    do {
        start <- getPosition; 
        f <- p;
        end <- getLastPosition;
        let { r = Range_Range (sourcePosToPosition start) (sourcePosToPosition end); };
        return (f r);
    }

sourcePosToPosition sourcePos =
    Position_Position 
        (sourceName sourcePos) 
        (sourceLine sourcePos)
        (sourceColumn sourcePos)

parens     p = between (special "(") (special ")") p        
brackets   p = between (special "[") (special "]") p
backquotes p = between (special "`") (special "`") p

commas  p = p `sepBy`  special ","
commas1 p = p `sepBy1` special ","

tycon = conid <?> "type constructor"
tyvar = varid <?> "type variable"

{- Lexical syntax -} 

lcurly = special "{"
rcurly = special "}"
semi   = special ";"

conid :: HParser Name
conid = name HaskellLexer.conid

varid :: HParser Name
varid = name HaskellLexer.varid

modid :: HParser Name
modid = conid <?> "module name (starting with upper case character)"

{-
con  ->  conid | ( consym )  (constructor)  
-}

con :: HParser Name
con = name HaskellLexer.conid <|> opName (parens consym)

{-
conop  ->  consym | `conid ` (constructor operator)  
-}

conop :: HParser Name
conop = opName consym <|> name (backquotes HaskellLexer.conid)
        <?> "constructor operator"

{-
var  ->  varid | ( varsym )  (variable)  
-}

var :: HParser Name
var = name HaskellLexer.varid <|> opName (parens varsym)

{-
varop  ->  varsym | `varid ` (variable operator)  
-}

varop :: HParser Name
varop = opName varsym <|> name (backquotes HaskellLexer.varid)
        <?> "operator"

name :: HParser String -> HParser Name
name p = addRange $
    do 
        n <- p
        return (\r -> Name_Identifier r [] n)

opName :: HParser String -> HParser Name
opName p = addRange $
    do 
        n <- p
        return (\r -> Name_Operator r [] n)

{-
op  ->  varop | conop  (operator)  
-}

op = try varop <|> conop

literal = addRange (
    do
        nf <- naturalOrFloat
        return $ \r -> case nf of
            Left n -> Literal_Int r (show n)
            Right f -> Literal_Float r (show f)
    <|>
    do
        c <- charLiteral
        return $ \r -> Literal_Char r [c]
    <|>
    do
        s <- stringLiteral
        return $ \r -> Literal_String r s
    ) <?> "literal"


{-
Expressions and patterns with operators are represented by lists. The Range
of this list is 'noRange' (a range with two unknown positions). The post-processor 
recognises this and will build infix applications out of the list.
The list itself contains expressions (/patterns) and operators. Operators can
be recognised because they also have noRange. Their name, however, does have a range.
The unary minus has 'unaryMinus' as its name to distinguish it from the binary minus.

An example,  "-3+4" is parsed as:

Expression_List <<unknown>,<unknown>> 
    [   Expression_Variable <<unknown>,<unknown>> (Name_Identifier <<1,1>,<1,2>> [] "unaryMinus")
    ,   Expression_Literal <<1,2>,<1,3>> (Literal_Int <<1,2>,<1,3>> "3")
    ,   Expression_Variable <<unknown>,<unknown>> (Name_Identifier <<1,3>,<1,4>> [] "+")
    ,   Expression_Literal <<1,4>,<1,5>> (Literal_Int <<1,4>,<1,5>> "4")
    ]

-}
intUnaryMinusName, floatUnaryMinusName :: String
intUnaryMinusName = "intUnaryMinus"
floatUnaryMinusName = "floatUnaryMinus"

