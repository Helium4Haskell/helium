module ParseDeclExp(decl, decls {- temp -}) where

import HaskellLexer hiding (conid, varid)
import UHA_Syntax(Expression(..), Name(..), Range, Statements, Statement(..), 
                    Alternatives, Alternative(..), Declarations, Declaration(..), Pattern(..),
                    LeftHandSide(..), RightHandSide(..), MaybeDeclarations(..), GuardedExpression(..),
                    FunctionBinding(..), MaybeExpression(..), Qualifier(..))
import ParseType
import Parsec
import ParseCommon
import ParsePat
import UHA_Utils
import qualified CollectFunctionBindings

{-
decls   ->  "{" decl1 ";" ... ";" decln "}"    (n>=0)  
-}

decls :: HParser Declarations
decls =
    do
        ds <- layout "declaration" "\";\"" sepBy1 lcurly rcurly semi decl
        return (CollectFunctionBindings.decls ds)

{- 
decl    ->  vars "::" type  (type signature)  
         |  ( funlhs | pat10 ) rhs          
vars    ->  var1 "," ..."," varn    (n>=1)   
funlhs  ->  var apat*
         |  pat10 varop pat10
         |  "(" funlhs ")" apat *

Rewrite to reduce backtracking:

decl    ->  [[ var ]] decl1
         |  [[ pat10 ]] decl2
         |  funlhs rhs
decl1   ->  "," vars "::" type
         |  "::" type
         |  varop pat10 rhs
         |  apat* rhs
decl2   ->  varop pat10 rhs
         |  rhs
funlhs  ->  [[ var ]] funlhs1
         |  [[ pat10 ]] varop pat10
         |  "(" funlhs ")" apat*
funlhs1 ->  varop pat10
         |  apat*
-}

decl :: HParser Declaration
decl = addRange (
    do 
        nr <- try (withRange var)
        decl1 nr
    <|>
    do
        pr <- try (withRange pat10)
        decl2 pr
    <|>
    do
        l <- funlhs
        b <- normalRhs
        return $ \r -> Declaration_FunctionBindings r
            [FunctionBinding_FunctionBinding r l b]
{-    <|> 
      return ( \r -> Declaration_Empty r )-}
    ) <?> "declaration"

decl1 :: (Name, Range) -> HParser (Range -> Declaration)
decl1 (n, nr) =
    do
        special ","
        ns <- vars
        reservedOp "::"
        t <- type_
        return $ \r -> Declaration_TypeSignature r (n:ns) t
    <|>
    do
        reservedOp "::"
        t <- type_
        return $ \r -> Declaration_TypeSignature r [n] t
    <|>
    do  
        o <- varop
        (p, pr) <- withRange pat10
        b <- normalRhs
        let lr = mergeRanges nr pr
        return $ \r -> Declaration_FunctionBindings r
            [FunctionBinding_FunctionBinding r 
                (LeftHandSide_Infix lr (Pattern_Variable nr n) o p) b]                
    <|>
    do
        (ps, rs) <- fmap unzip (many (withRange apat))
        let lr = if null rs then nr else mergeRanges nr (last rs)
        b <- normalRhs
        return $ \r -> 
            if null rs then
                Declaration_PatternBinding r (Pattern_Variable nr n) b
            else
                Declaration_FunctionBindings r
                    [FunctionBinding_FunctionBinding r 
                        (LeftHandSide_Function lr n ps) b]                

decl2 :: (Pattern, Range) -> HParser (Range -> Declaration)
decl2 (p1, p1r) = 
    do
        o <- varop
        (p2, p2r) <- withRange pat10
        b <- normalRhs
        let lr = mergeRanges p1r p2r
        return $ \r -> Declaration_FunctionBindings r
            [FunctionBinding_FunctionBinding r 
                (LeftHandSide_Infix lr p1 o p2) b]                
    <|>
    do
        b <- normalRhs
        return $ \r -> Declaration_PatternBinding r p1 b        

funlhs :: HParser LeftHandSide
funlhs = addRange $
    do  
        nr <- try (withRange var)
        funlhs1 nr
    <|>
    do
        p1 <- try pat10
        o <- varop
        p2 <- pat10
        return $ \r -> LeftHandSide_Infix r p1 o p2
    <|>
    do
        l <- parens funlhs
        ps <- many apat
        return $ \r -> LeftHandSide_Parenthesized r l ps 

funlhs1 :: (Name, Range) -> HParser (Range -> LeftHandSide)
funlhs1 (n, nr) = 
    do
        o <- varop
        p <- pat10
        return $ \r -> LeftHandSide_Infix r
                        (Pattern_Variable nr n) o p 
    <|>
    do
        ps <- many apat
        return $ \r -> LeftHandSide_Function r n ps

vars :: HParser [Name]
vars = commas1 var

{-
rhs     ->  "=" exp rhs1
         |  gdexp+ rhs1
rhs1    -> ( "where" decls )?        
gdexp   ->  "|" exp0 "=" exp
-}

normalRhs = rhs "="
caseRhs = rhs "->"

-- The string is "->" for a case rhs and "=" for a normal rhs
rhs :: String -> HParser RightHandSide
rhs equals = addRange $
    do
        reservedOp equals
        e <- exp_ 
        mds <- option MaybeDeclarations_Nothing rhs1
        return $ \r -> RightHandSide_Expression r e mds
    <|>                        
    do
        gs <- many1 (gdexp equals)
        mds <- option MaybeDeclarations_Nothing rhs1
        return $ \r -> RightHandSide_Guarded r gs mds

rhs1 :: HParser MaybeDeclarations
rhs1 =
    do 
        reserved "where"
        ds <- decls
        return (MaybeDeclarations_Just ds)
                
gdexp :: String -> HParser GuardedExpression
gdexp equals = addRange $
    do
        reservedOp "|"
        g <- exp0
        reservedOp equals
        e <- exp_
        return $ \r -> GuardedExpression_GuardedExpression r g e
        
{-
exp     ->  exp0 "::" type  (expression type signature)  
         |  exp0  
-}

exp_ = addRange $
    do 
        e <- exp0
        option (\_ -> e) $ 
            do 
                reservedOp "::"
                t <- type_
                return $ \r -> Expression_Typed r e t

{-
expi  ->  expi+1 [op(n,i) expi+1]  
 |  lexpi  
 |  rexpi  
lexpi  ->  (lexpi | expi+1) op(l,i) expi+1  
lexp6  ->  - exp7  
rexpi  ->  expi+1 op(r,i) (rexpi | expi+1)  

Simplified, post-processing 

exp0 -> ( "-" )? exp10 ( op ( "-" )? exp10 )*

See noRange in ParseCommon for an explanation of the parsing of infix expressions.
-}

test p s = runHParser p "" s

exp0 :: HParser Expression
exp0 = addRange (
    do  
        u <- maybeUnaryMinus
        es <- exprChain
        return $ \r -> Expression_List noRange (u ++ es)
    <?> "expression"        
  )

exprChain :: HParser [Expression]
exprChain = 
    do
        e <- exp10
        es <- fmap concat $ many $
            do
                o <- try (do { n <- varop; return (Expression_Variable noRange n) } )
                     <|>
                     do { n <- conop; return (Expression_Constructor noRange n) }
                u <- maybeUnaryMinus
                e <- exp10
                return ([o] ++ u ++ [e])
        return (e:es)

maybeUnaryMinus = option [] (fmap (:[]) unaryMinus)  

unaryMinus :: HParser Expression
unaryMinus = 
    try (do 
        (_, r) <- withRange (special "-.") 
        return (Expression_Variable noRange (Name_Identifier r [] floatUnaryMinusName))
    ) 
    <|>
    do 
        (_, r) <- withRange (special "-") 
        return (Expression_Variable noRange (Name_Identifier r [] intUnaryMinusName))

{-       
exp10   ->  "\" apat1 ... apatn "->" exp  (lambda abstraction, n>=1)  
         |  "let" decls "in" exp  (let expression)  
         |  "if" exp "then" exp "else" exp  (conditional)  
         |  "case" exp "of" alts  (case expression)  
         |  "do" stmts (do expression)  
         |  fexp  
-}

exp10 :: HParser Expression
exp10 = addRange (
    do
        reservedOp "\\"
        ps <- many1 apat
        reservedOp "->"
        e <- exp_
        return $ \r -> Expression_Lambda r ps e
    <|>
    do
        reserved "let"
        ds <- decls
        reserved "in"
        e <- exp_
        return $ \r -> Expression_Let r ds e
    <|>
    do
        reserved "if"
        e1 <- exp_
        reserved "then"
        e2 <- exp_
        reserved "else"
        e3 <- exp_
        return $ \r -> Expression_If r e1 e2 e3
    <|>
    do
        reserved "case"
        e <- exp_
        reserved "of"
        as <- alts
        return $ \r -> Expression_Case r e as
    <|>
    do
        reserved "do"
        ss <- stmts
        return $ \r -> Expression_Do r ss
    ) 
    <|>
    fexp
    <?> "expression"

{-
fexp  -> aexp+
-}

fexp :: HParser Expression    
fexp = addRange $
    do
        (e:es) <- many1 aexp
        if null es then
            return $ \_ -> e
          else
            return $ \r -> Expression_NormalApplication r e es

{-
aexp    ->  var  (variable)  
         |  con
         |  literal  

         |  () 
         |  (op fexp) (left section)
         |  (fexp op) (right section)
         |  ( exp )  (parenthesized expression)  
         |  ( exp1 , ... , expk )  (tuple, k>=2)  

         |  "[" "]" 
         |  "[" exp1 "," ... "," expk "]"
         |  "[" exp1 ( "," exp2 )? ".." exp3? "]"
         |  "[" exp "|" qual1 "," ... "," qualn "]"
-}

operatorAsExpression :: HParser Expression
operatorAsExpression =
    try (fmap (\(n, r) -> Expression_Variable r n) (withRange varop))
    <|>
    fmap ((\(n, r) -> Expression_Constructor r n)) (withRange conop)
    
aexp :: HParser Expression    
aexp = addRange (
    do 
        special "("
        ( -- dit haakje is nodig (snap niet waarom). Arjan
            do 
                u <- unaryMinus
                es <- exprChain
                special ")"
                return $ \r -> Expression_List noRange (u:es)
            <|>                
            do      -- operator followed by optional expression
                    -- either full section (if there is no expression) or 
                    -- a left section (if there is)
                opExpr <- operatorAsExpression
                me <- option Nothing (fmap Just fexp)
                special ")"
                return $ \r -> 
                    Expression_InfixApplication r
                        MaybeExpression_Nothing
                        opExpr
                        (case me of 
                            Nothing -> MaybeExpression_Nothing
                            Just e  -> MaybeExpression_Just e) 
            <|>
            try (do -- right section, expression followed by operator
                    -- or a parenthesized expression (if no operator is found)
                e <- fexp
                mo <- option Nothing (fmap Just operatorAsExpression)
                special ")"
                return $ \r ->
                    case mo of
                        Nothing -> Expression_Parenthesized r e
                        Just opExpr -> 
                            Expression_InfixApplication r
                                (MaybeExpression_Just e)
                                opExpr
                                MaybeExpression_Nothing
            )
            <|>
            do -- unit "()", expression between parenthesis or a tuple
                es <- commas exp_
                special ")"
                return $ \r -> case es of
                    [] -> Expression_Constructor r (Name_Special r [] "()")
                    [e] -> Expression_Parenthesized r e
                    _ -> Expression_Tuple r es
         )
    <|>
    do
        n <- varid
        return $ \r -> Expression_Variable r n
    <|>
    do
        n <- conid
        return $ \r -> Expression_Constructor r n
    <|>
    do 
        l <- literal
        return $ \r -> Expression_Literal r l
    <|>
    do
        special "["
        aexp1
    ) <?> "expression"

{-
Last four cases, rewritten to eliminate backtracking

aexp    -> ...
         | "[" aexp1
aexp1   -> "]" 
         | exp aexp2 "]"
aexp2   -> "|" qual1 "," ... "," qualn
         | ".." exp?
         | "," exp aexp3 
         |               (empty)
aexp3   -> ".." exp?
         | ( "," exp )* 
-}

aexp1 :: HParser (Range -> Expression)
aexp1 =
    do
        special "]"
        return $ \r -> Expression_Constructor r
                        (Name_Special r [] "[]")
    <|>
    do
        e1 <- exp_
        e2 <- aexp2 e1
        special "]"
        return e2
        
aexp2 :: Expression -> HParser (Range -> Expression)    
aexp2 e1 = 
    do
        reservedOp "|"
        qs <- commas1 qual
        return $ \r -> Expression_Comprehension r e1 qs
    <|> 
    do
        reservedOp ".."
        option (\r -> Expression_Enum r e1
                        MaybeExpression_Nothing 
                        MaybeExpression_Nothing) $
            do
                e2 <- exp_
                return $ \r -> Expression_Enum r e1
                                MaybeExpression_Nothing 
                                (MaybeExpression_Just e2) 
    <|>
    do
        special ","
        e2 <- exp_
        aexp3 e1 e2
    <|>
    return (\r -> Expression_List r [e1])

aexp3 :: Expression -> Expression -> HParser (Range -> Expression)    
aexp3 e1 e2 =
    do
        reservedOp ".."
        option (\r -> Expression_Enum r e1 
                        (MaybeExpression_Just e2)  
                        MaybeExpression_Nothing) $
            do
                e3 <- exp_
                return $ \r -> Expression_Enum r e1 
                                (MaybeExpression_Just e2)
                                (MaybeExpression_Just e3) 
    <|>
    do
        es <- many (do { special ","; exp_ })
        return $ \r -> Expression_List r (e1:e2:es)              

{-
stmts  -> "{" stmt1 ";" ... ";" stmtn "}"   (n>=0)  
-}

stmts :: HParser Statements
stmts = 
    layout "statement" "\";\"" sepEndBy lcurly rcurly semi stmt

{-
stmt    ->  "let" decls  
         |  pat "<-" exp  
         |  exp
-}

stmt :: HParser Statement
stmt = addRange $
    do
        reserved "let"
        ds <- decls
        return $ \r -> Statement_Let r ds
    <|>
    do
        p <- try $
            do
                p <- pat
                reservedOp "<-"
                return p
        e <- exp_
        return $ \r -> Statement_Generator r p e
    <|>
    do
        e <- exp_
        return $ \r -> Statement_Expression r e
        
{-
alts    ->  "{" alt1 ";" ... ";" altn "}" (n>=0)  
-}

alts :: HParser Alternatives
alts =
    layout "alternative" "\";\"" sepEndBy lcurly rcurly semi alt

{-
alt -> pat rhs
-}

alt :: HParser Alternative
alt = addRange $
    do
        p <- pat
        b <- caseRhs
        return $ \r -> Alternative_Alternative r p b

{-
qual    ->  "let" decls  (local declaration)  
         |  pat "<-" exp  (generator)  
         |  exp  (guard)  
-}

qual :: HParser Qualifier
qual = addRange $
    do
        reserved "let"
        ds <- decls
        return $ \r -> Qualifier_Let r ds
    <|>
    do
        p <- try $
            do
                p <- pat
                reservedOp "<-"
                return p
        e <- exp_
        return $ \r -> Qualifier_Generator r p e
    <|>
    do
        e <- exp_
        return $ \r -> Qualifier_Guard r e
