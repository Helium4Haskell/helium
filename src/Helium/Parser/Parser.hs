{-| Module      :  Parser
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Parser.Parser
    ( module_, exp_, exp0, type_, atype, contextAndType
    , parseOnlyImports
    ) where

{-
Absent:
- records
- "newtype"
- strictness annotations
- n+k patterns
- [] and (,) and (,,,) etc as (type) constructor
- empty declarations, qualifiers, alternatives or statements
- "qualified", "as" in imports
- import and export lists

Simplified:
- funlhs 
    For example   x:xs +++ ys = ...  is not allowed, parentheses around x:xs necessary
- pattern binding met pat10 i.p.v. pat0 
    For example   (x:xs) = [1..] (parenthesis are obligatory)
- sections: (fexp op) and (op fexp)
    For example   (+2*3)   is not allowed, should be (+(2*3)) 
- fixity declarations only at top-level
-}

import Control.Monad
import Data.Maybe (isJust)
import Helium.Parser.ParseLibrary hiding (satisfy)
import Data.Functor.Identity (Identity)
import Text.ParserCombinators.Parsec
import Text.Parsec.Prim (ParsecT)
import Helium.Parser.Lexer
import Helium.Parser.LayoutRule
import qualified Helium.Utils.Texts as Texts

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range

import qualified Helium.Parser.CollectFunctionBindings as CollectFunctionBindings
import Helium.Utils.Utils

parseOnlyImports :: String -> IO [Name]
parseOnlyImports fullName = do
    contents <- readSourceFile fullName    
    return $ case lexer [] fullName contents of
               Left _ -> []
               Right (toks, _) ->
                 case runHParser onlyImports fullName (layout toks) False {- no EOF -} of
                   Left _ -> []
                   Right imports -> map nameFromImportDeclaration imports

{-
module  
    ->  "module" modid exports? "where" body  
--      |  body  
-}

module_ :: HParser Module
module_ = addRange $
    do
        lexMODULE
        n <- modid
        mes <- exportList 
        lexWHERE
        b <- body
        return (\r -> Module_Module r (MaybeName_Just n) mes b)
    <|>
    do 
        b <- body
        return (\r ->
            Module_Module r MaybeName_Nothing MaybeExports_Nothing b)


{-
exports? -> Nothing
          | Just exports
exports ->   "(" export1 "," ... "," exportn [ , ] ) (n>=0)
-}
exportList :: HParser MaybeExports
exportList =
    do lexLPAREN
       exps <- export `sepBy` lexCOMMAnotFollowedByRParen
       optional lexCOMMA
       lexRPAREN
       return (MaybeExports_Just exps)
    <|>
    return MaybeExports_Nothing
  where
    lexCOMMAnotFollowedByRParen = try (do{lexCOMMA; notFollowedBy lexRPAREN})
    export :: HParser Export
    export = addRange $
      exportVariable <|> exportModule <|> exportTypeOrClass

    exportVariable = do
        varname <- qvar
        return (\range -> Export_Variable range varname)

    exportModule = do
      lexMODULE
      modname <- modid
      return  (\range -> Export_Module range modname)

    exportTypeOrClass = do
      typename <- qtycon
      -- First let's try if constructors/methods are added (e.g. Bool(..) or Bool(True, False)
      do
        lexLPAREN
        do
          lexDOTDOT
          lexRPAREN
          return (\range -> Export_TypeOrClassComplete range typename)
         <|> do
          names <- cname `sepBy` lexCOMMA <|> qvar `sepBy` lexCOMMA
          lexRPAREN
          return (\range -> Export_TypeOrClass range typename (MaybeNames_Just names))
       -- If there are no parens, no constructors are added.
       <|> return (\range -> Export_TypeOrClass range typename MaybeNames_Nothing)

onlyImports :: HParser [ImportDeclaration]
onlyImports = 
    do
        lexMODULE
        _ <- modid
        _ <- exportList 
        lexWHERE
        lexLBRACE <|> lexINSERTED_LBRACE
        many (do { i <- impdecl; semicolon; return i })
    <|>
    do
        lexLBRACE <|> lexINSERTED_LBRACE
        many (do { i <- impdecl; semicolon; return i })
  where
    semicolon = lexSEMI <|> lexINSERTED_SEMI <|> lexINSERTED_RBRACE
    -- the last of the three is a hack to support files that
    -- only contain imports
    
{-
body  ->  "{" topdecls "}"
topdecls  ->  topdecl1 ";" ... ";" topdecln    (n>=0)  
-}

body :: HParser Body
body = addRange $
      withBraces' $ \explicit -> 
        do
          n <- lexNamedHole
          return (\r -> Body_Hole r n)
        <|>
        do 
          (is, ds) <- importsThenTopdecls explicit
          let groupedDecls = CollectFunctionBindings.decls ds
          return $ \r -> Body_Body r is groupedDecls

importsThenTopdecls :: Bool -> 
  ParsecT [Token] SourcePos Identity ([ImportDeclaration], [Declaration])
importsThenTopdecls explicit =
    do
        is <- many (do { i <- impdecl
                       ; if explicit then lexSEMI else lexSEMI <|> lexINSERTED_SEMI 
                       ; return i
                       } )
        ds <- topdeclCombinator topdecl
        return (is, ds)
        
  where
    topdeclCombinator = if explicit then semiSepTerm else semiOrInsertedSemiSepTerm

        
-- JW: Need to add to topdecl '| "class" [scontext =>] tycls tyvar [where cdecls] '
-- First try " class tycon tyvar [where cdecls]" as class constraints do not yet exist
-- in a later phase add them then also data has to be changed to deal with typeclass constraints
-- please note that in ghc already this has some strange behaviour, read semantics carefully...

{-
topdecl  
    ->  "data" simpletype "=" constrs derivings?
     |  "type" simpletype "=" type
     |  "dimension" simpledimension in simpleunit
     |  "unit" simpleunit "derives from" unit "with" decl
     |  "alias" simpleunit = unit
     |  infixdecl
     |  decl  

derivings
    -> "deriving" derivings'

derivings'
    -> tycon 
     | "(" ")"
     | "(" tycon ( "," tycon )* ")"

simpletype  
    ->  tycon tyvar1 ... tyvark  (k>=0)  
-}

{-
    | Data                            
        range                    : Range
        context                  : ContextItems
        simpletype               : SimpleType
        constructors             : Constructors
        derivings                : Names
-}
topdecl :: HParser Declaration
topdecl = addRange (
    do
        lexDATA
        st <- simpleType
        lexASG
        cs <- constrs
        ds <- option [] derivings
        return (\r -> Declaration_Data r [] st cs ds)
    <|>
    do
        lexTYPE
        st <- simpleType
        lexASG
        t <- type_
        return $ \r -> Declaration_Type r st t
    <|>
    do
        lexNEWTYPE
        st <- simpleType
        lexASG
        t <- newconstr
        ds <- option [] derivings
        return $ \r -> Declaration_Newtype r [] st t ds
    <|>
    do
        lexDIMENSION
        sd <- sdim
        lexIN
        su <- sunit
        return $ \r -> Declaration_Dimension r sd su
    <|>
    do
        lexUNIT
        su <- sunit
        lexDERIVES
        lexFROM
        u <- unit
        lexWITH
        f <- decl  
        return $ \r -> Declaration_UnitFromUnit r su u f
    <|>
    do
        lexALIAS
        su <- sunit
        lexASG
        u <- unit
        return $ \r -> Declaration_AliasUnit r su u
    <|>
-- Declaration_Class (Range) (ContextItems) (SimpleType) (MaybeDeclarations)
{-
cdecls :: HParser Declarations
cdecls =
    do
     ds <- withLayout cdecl
     return (CollectFunctionBindings.cdecls ds)
-}
    do
        lexCLASS
        ct <- option [] (try $ do {c <- scontext ; lexDARROW ; return c} )
        st <- simpleType
        ds <- option MaybeDeclarations_Nothing 
                     (try $ do lexWHERE
                               d <-  option MaybeDeclarations_Nothing (try $ do  
                                                                               cds <- cdecls 
                                                                               return (MaybeDeclarations_Just cds))                                                     
                               return d)
        return $ \r -> Declaration_Class r ct st ds
    <|>
-- Declaration_Instance (Range) (ContextItems) (Name) (Types) (MaybeDeclarations)
    do
        lexINSTANCE
        ct <- option [] (try $ do {c <- scontext; lexDARROW ; return c} )
        n  <- qtycls
        ts <- iType
        ds <- option MaybeDeclarations_Nothing (try $ do lexWHERE
                                                         d <- idecls
                                                         let d' = CollectFunctionBindings.decls' d
                                                         return (MaybeDeclarations_Just d'))
        return $ \r -> Declaration_Instance r ct n [ts] ds
    <|>
    infixdecl
    ) 
    <|> addRange (
      do
         n <- lexNamedHole
         jb <- optionMaybe normalRhs
         case jb  of
            Just b ->  return $ \r -> Declaration_PatternBinding r (Pattern_Hole r n) b
            Nothing -> return $ \r -> Declaration_Hole r n
      )
    <|>
    decl
    <?> Texts.parserDeclaration

derivings :: HParser [Name]
derivings = 
    do  lexDERIVING
        ( do cls <- qtycls
             return [cls] )
          <|> (
          do lexLPAREN           
             clss <- qtycls `sepBy` lexCOMMA
             lexRPAREN
             return clss )
    
simpleType :: HParser SimpleType
simpleType =
    addRange (
        do
            c  <- tycon
            vs <- many tyvar
            return $ \r -> SimpleType_SimpleType r c vs
    )
    
{-
infixdecl   ->  fixity [digit] ops  (fixity declaration)  
fixity      ->  "infixl" | "infixr" | "infix"  
ops         ->  op1 "," ... "," opn    (n>=1)  
-}

infixdecl :: HParser (Range -> Declaration)
infixdecl = 
    do
        f <- fixity
        p <- fmap fromInteger (option 9 (fmap read lexInt)) :: HParser Int
        when (p < 0 || p > 9) (fail Texts.parserSingleDigitPriority)
        os <- ops
        return $ \r -> Declaration_Fixity r f (MaybeInt_Just p) os

ops :: HParser Names
ops = commas1 op

fixity :: HParser Fixity
fixity = addRange $ 
    do
        lexINFIXL 
        return $ \r -> Fixity_Infixl r
    <|>
    do
        lexINFIXR 
        return $ \r -> Fixity_Infixr r
    <|>
    do
        lexINFIX 
        return $ \r -> Fixity_Infix r
    

{-
newconstr -> con atype
           | con { var :: type }
-}

newconstr :: HParser Constructor
newconstr = addRange $
    do 
        (n, ts) <- try $ do 
            n <- conid
            (FieldDeclaration_FieldDeclaration r ns t) <- braces fielddecl
            let ts = FieldDeclaration_FieldDeclaration r ns (strictify t)
            return (n, ts)
        return (\r -> Constructor_Record r n [ts])
    <|>
    do 
        n <- conid
        ts <- annotatedType atype
        let ts' = strictify ts
        return (\r -> Constructor_Constructor r n [ts'])
  where
    strictify (AnnotatedType_AnnotatedType r _ t) 
        = AnnotatedType_AnnotatedType r True t
    

{-
constrs  ->  constr1 "|" ... "|" constrn  (n>=1)  
-}

constrs :: HParser Constructors
constrs = constr `sepBy1` lexBAR


{-
constr  ->  btype conop btype  (infix conop)  
         |  con { fielddecl1, ..., fielddecln }  (n>=0)  
         |  con atype1 ... atypek  (arity con = k, k>=0)  
-}
-- TODO: Handle strictness for records
constr :: HParser Constructor
constr = addRange $
    do 
        (t1, n) <- try $ do 
            t1 <- annotatedType btype 
            n <- conop
            return (t1, n)
        t2 <- annotatedType btype
        return (\r -> Constructor_Infix r t1 n t2)
    <|>
    do 
        (n, ts) <- try $ do 
            n <- conid
            ts <- braces (commas fielddecl)
            return (n, ts)
        return (\r -> Constructor_Record r n ts)
    <|>
    do 
        n <- conid
        ts <- many (annotatedType atype)
        return (\r -> Constructor_Constructor r n ts)

{-
fielddecl 	-> 	vars :: (type | ! atype) 
-}

fielddecl :: HParser FieldDeclaration
fielddecl = addRange $
    do
        (n, t) <- try $ do
            n <- commas varid
            lexCOLCOL
            t <- annotatedType type_
            return (n, t)
        return (\r -> FieldDeclaration_FieldDeclaration r n t)

{-
Simplified import:
impdecl -> "import" modid impspec?
impspec -> "hiding" "(" import "," ... ")"
import  -> var
-}

impdecl :: HParser ImportDeclaration
impdecl = addRange (
    do
        lexIMPORT
        q <- option False $ do {lexQUALIFIED; return True }
        m <- modid
        a <- option MaybeName_Nothing $
            do {lexAS; as <- modid; return (MaybeName_Just as)}
        i <- option MaybeImportSpecification_Nothing $
                do{ is <- impspec
                  ; return (MaybeImportSpecification_Just is)
                  }
        return $ \r -> ImportDeclaration_Import r q m a i
    ) <?> Texts.parserImportDeclaration

impspec :: HParser ImportSpecification
impspec = addRange $
    do  
        h <- option False $
            do { lexHIDING; return True }
        lexLPAREN
        is <- import_ `sepBy` lexCOMMAnotFollowedByRParen
        optional lexCOMMA
        lexRPAREN
        return $ \r -> ImportSpecification_Import r h is
    where
        lexCOMMAnotFollowedByRParen = try (do{lexCOMMA; notFollowedBy lexRPAREN})
        

import_ :: HParser Import
import_ = addRange $
    importVariable <|> importTypeOrClass
    where
        importVariable = do
            varname <- var
            return (\range -> Import_Variable range varname)
    
        importTypeOrClass = do
          typename <- tycon
          -- First let's try if constructors/methods are added (e.g. Bool(..) or Bool(True, False)
          do
            lexLPAREN
            do
              lexDOTDOT
              lexRPAREN
              return (\range -> Import_TypeOrClassComplete range typename)
             <|> do
              names <- cname `sepBy` lexCOMMA <|> var `sepBy` lexCOMMA
              lexRPAREN
              return (\range -> Import_TypeOrClass range typename (MaybeNames_Just names))
           -- If there are no parens, no constructors are added.
           <|> return (\range -> Import_TypeOrClass range typename MaybeNames_Nothing)

{-
cdecls -> " {" decl1 ";" .... ";" decln "}"    (n>=0)
-}

{-
cdecl -> vars "::" type  (type signature)
      | (funlhs | var) rhs
-}

cdecls :: HParser Declarations
cdecls =
    do
     ds <- withLayout cdecl
     return (CollectFunctionBindings.decls ds)
     
cdecl :: HParser Declaration
cdecl = addRange (
    try (do
         nr <- withRange var
         cdecl1 nr)
    <|>
    try (
            infixdecl
    )
    <|>
    do
       l <- funlhs
       b <- normalRhs
       return $ \r -> Declaration_FunctionBindings r
           [FunctionBinding_FunctionBinding r l b]
      ) <?> Texts.parserDeclaration
     
    
cdecl1 :: (Name, Range) -> HParser (Range -> Declaration)
cdecl1 (n, _) =
    do
        lexCOMMA
        ns <- vars
        lexCOLCOL
        t <- contextAndType
        return $ \r -> Declaration_TypeSignature r (n:ns) t
    <|>
    do
        lexCOLCOL
        t <- contextAndType
        return $ \r -> Declaration_TypeSignature r [n] t
    <|>
    do
        b <- normalRhs
        return $ \r -> Declaration_FunctionBindings r
            [FunctionBinding_FunctionBinding r (LeftHandSide_Function r n []) b]

{-
idecl -> (funlhs | var) rhs
        |                       (empty)
-}

idecls :: HParser Declarations
idecls =
    do
     ds <- withLayout idecl
     return ds -- (CollectFunctionBindings.decls ds)
     
idecl :: HParser Declaration
idecl = addRange (
    try (do
          (n, _) <- try (withRange var)
          b <- normalRhs
          return $ \r -> Declaration_FunctionBindings r
             [FunctionBinding_FunctionBinding r (LeftHandSide_Function r n []) b])
    <|>
    do
       l <- funlhs
       b <- normalRhs
       return $ \r -> Declaration_FunctionBindings r
           [FunctionBinding_FunctionBinding r l b]
       
      ) <?> Texts.parserDeclaration
                  
{-
decls   ->  "{" decl1 ";" ... ";" decln "}"    (n>=0)  
-}

decls :: HParser Declarations
decls =
    do
        ds <- withLayout decl
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
decl1   ->  "," vars "::" type ("<" unit ">")?
         |  "::" type ("<" unit ">")?
         |  varop pat10 rhs
         |  "@" apat decl2
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
    do fb <- lexCaseFeedback
       return $ \r -> Declaration_FunctionBindings r
          [FunctionBinding_Feedback r fb $ FunctionBinding_Hole r ""]
    <|>
    do
        n <- lexNamedHole
        jb <- optionMaybe normalRhs
        case jb  of
           Just b ->  return $ \r -> Declaration_PatternBinding r (Pattern_Hole r n) b
           Nothing -> return $ \r -> Declaration_Hole r n
    <|>
    do 
        nr <- try (withRange var)
        decl1 nr
    <|>
    do
        pr <- try (withRange pat10)
        decl2 pr
    <|>
    -- do
    --     n <- lexNamedHole
    --     return $ \r -> Declaration_Hole r n
    do
        l <- funlhs
        b <- normalRhs
        return $ \r -> Declaration_FunctionBindings r
            [FunctionBinding_FunctionBinding r l b]
    ) <?> Texts.parserDeclaration

decl1 :: (Name, Range) -> HParser (Range -> Declaration)
decl1 (n, nr) =
    do
        lexCOMMA
        ns <- vars
        lexCOLCOL
        t <- contextAndType
        return $ \r -> Declaration_TypeSignature r (n:ns) t
    <|>
    do
        lexCOLCOL
        t <- contextAndType
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
        lexAT
        (p, pr) <- withRange apat
        let completeRange = mergeRanges nr pr
            asPat = Pattern_As completeRange n p
        decl2 (asPat, completeRange)
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

normalRhs, caseRhs :: HParser RightHandSide
normalRhs = rhs lexASG
caseRhs   = rhs lexRARROW

-- The string is "->" for a case rhs and "=" for a normal rhs
rhs :: HParser () -> HParser RightHandSide
rhs equals = addRange $
    do
        equals
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
        lexWHERE
        ds <- decls
        return (MaybeDeclarations_Just ds)
                
gdexp :: HParser () -> HParser GuardedExpression
gdexp equals = addRange $
    do
        lexBAR
        g <- exp0
        equals
        e <- exp_
        return $ \r -> GuardedExpression_GuardedExpression r g e
        

-- exp_ = addRange (
--    do
--       feedback <- option Nothing (try $ lexFeedback >>= return . Just)
--       e <- expOrg_
--       return (maybe (const e) (\s -> \r -> Expression_Feedback r s e) feedback)
--    ) <?> Texts.parserExpression

{-
exp     ->  exp0 "::" type  (expression type signature)  
         |  exp0 "::" type "<" dimension ">" (expression dimensioned)
         |  exp0  
-}

-- do
--     (e, rs) <- try $ do 
--         e <- aexp
--         rs <- braces (fbind `sepBy` lexCOMMA)
--         return (e, rs)
--     return $ \r -> Expression_RecordUpdate r e rs
-- <|>


exp_ :: ParsecT [Token] SourcePos Identity Expression
exp_ = addRange (
    do
       e <- exp0
       e' <- option (const e) $ 
            do
                rs <- braces (fbind `sepBy` lexCOMMA)
                return $ \r -> Expression_RecordUpdate r e rs
       e'' <- option e' $ 
            do 
                lexCOLCOL
                t <- contextAndType
                return $ \r -> Expression_Typed r (e' r) t
       return $ \r -> e'' r
        
    )
    <?> Texts.parserExpression        

contextAndType :: HParser Type
contextAndType = addRange $ do
    mc <- option Nothing (try $ do { c <- scontext; lexDARROW; return (Just c) })
    t <- type_
    case mc of 
        Nothing -> return $ \_ -> t
        Just c  -> return $ \r -> Type_Qualified r c t
    
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

exp0 :: HParser Expression
exp0 = addRange (
    do  
        u <- maybeUnaryMinus
        es <- exprChain
        return $ \_ -> Expression_List noRange (u ++ es)
    )
    <?> Texts.parserExpression        

exprChain :: HParser [Expression]
exprChain = 
    do
        e <- exp10
        es <- fmap concat $ many $
            do
                o <- operatorAsExpression False
                u <- maybeUnaryMinus
                e' <- exp10
                return ([o] ++ u ++ [e'])
        return (e:es)

maybeUnaryMinus :: ParsecT [Token] SourcePos Identity [Expression]
maybeUnaryMinus = 
    option [] (fmap (:[]) unaryMinus)  
    <?> Texts.parserExpression

unaryMinus :: HParser Expression
unaryMinus = 
    do
        (_, r) <- withRange lexMINDOT 
        return (Expression_Variable noRange (setNameRange floatUnaryMinusName r))
    <|>
    do 
        (_, r) <- withRange lexMIN 
        return (Expression_Variable noRange (setNameRange intUnaryMinusName r))

{-       
exp10   ->  "\" apat1 ... apatn "->" exp  (lambda abstraction, n>=1)  
         |  "let" decls "in" exp  (let expression)  
         |  "if" exp "then" exp "else" exp  (conditional)  
         |  "case" exp "of" alts  (case expression)  
         |  "do" stmts (do expression)  
         |  fexp
         |  uexp
-}

exp10 :: HParser Expression
exp10 = addRange (
    do
        lexBSLASH
        ps <- many1 apat
        lexRARROW
        e <- exp_
        return $ \r -> Expression_Lambda r ps e
    <|>
    (do
        lexLET
        ds <- decls
        lexIN
        e <- exp_
        return $ \r -> Expression_Let r ds e)
    <|>
    do
        lexIF
        e1 <- exp_
        lexTHEN
        e2 <- exp_
        lexELSE
        e3 <- exp_
        return $ \r -> Expression_If r e1 e2 e3
    <|>
    do
        lexCASE
        e <- exp_
        lexOF
        as <- alts
        return $ \r -> Expression_Case r e as
    <|>
    do
        lexDO
        ss <- stmts
        return $ \r -> Expression_Do r ss
    ) 
    {-<|>
    (try uexp)-}
    <|>
    fexp
    <?> Texts.parserExpression

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
 uexp -> qvar <unit> | literal <unit> | (exp) <unit>
 -}

uexp :: HParser Expression
uexp = addRange $
    do
        n <- qvarid
        u <- angles unit
        return $ \r -> Expression_Dimensioned r (Expression_Variable r n) u
    <|>
    do 
        l <- literal
        u <- angles unit
        return $ \r -> Expression_Dimensioned r (Expression_Literal r l) u
    <|>
    do
        e <- parens exp_
        u <- angles unit
        return $ \r -> Expression_Dimensioned r e u

    
{-
aexp    ->  qvar  (variable)  
         |  gcon
         |  literal  

         |  "[" "]" 
         |  "[" exp1 "," ... "," expk "]"
         |  "[" exp1 ( "," exp2 )? ".." exp3? "]"
         |  "[" exp "|" qual1 "," ... "," qualn "]"

         |  () 
         |  (qop fexp) (left section)
         |  (fexp qop) (right section)
         |  ( exp )  (parenthesized expression)  
         |  ( exp1 , ... , expk )  (tuple, k>=2)  
         
Last cases parsed as:

    "(" "-" exprChain ( "," exp_ )* ")"
  | "(" qop fexp ")"
  | "(" fexp qop ")"
  | "(" ( exp_ )<sepBy ","> ")"
-}

operatorAsExpression :: Bool -> HParser Expression
operatorAsExpression storeRange = (do
    (o, r) <- withRange ( fmap Left qvarsym <|> fmap Right qconsym 
                      <|> lexBACKQUOTEs (fmap Left qvarid <|> fmap Right qconid))
    let range = if storeRange then r else noRange                      
    return (case o of
        Left  v -> Expression_Variable    range v
        Right c -> Expression_Constructor range c
     )) <?> Texts.parserOperator
                         
aexp :: HParser Expression    
aexp =
    (try uexp)
    <|>
    addRange (
    do 
        lexLPAREN
        ( -- dit haakje is nodig (snap niet waarom). Arjan
            try (do  -- de try vanwege (-) DEZE PARSER MOET OPNIEUW GESCHREVEN WORDEN !!!
                ue <- do
                    u <- unaryMinus
                    es <- exprChain
                    return (Expression_List noRange (u:es))
                es <- many (do { lexCOMMA; exp_ })
                lexRPAREN
                return $ 
                    if null es then
                        \r -> Expression_Parenthesized r ue
                    else 
                        \r -> Expression_Tuple r (ue:es))
            <|>                
            do      -- operator followed by optional expression
                    -- either full section (if there is no expression) or 
                    -- a left section (if there is)
                opExpr <- operatorAsExpression True
                me <- option Nothing (fmap Just fexp)
                lexRPAREN
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
                mo <- option Nothing (fmap Just (operatorAsExpression True))
                lexRPAREN
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
                lexRPAREN
                return $ \r -> case es of
                    [e] -> Expression_Parenthesized r e
                    _ -> Expression_Tuple r es
         )
    <|>
    do
        n <- qvarid
        return $ \r -> Expression_Variable r n
    <|>
    do
        (n, rs) <- try $ do 
            n <- qconid
            rs <- braces (fbind `sepBy` lexCOMMA)
            return (n, rs)
        return $ \r -> Expression_RecordConstruction r n rs
    <|>
    do
        n <- qconid
        return $ \r -> Expression_Constructor r n
    <|>
    do 
        n <- lexNamedHole
        return $ \r -> Expression_Hole r n
    <|>
    do
        feedback <- lexFeedback
        e        <- aexp
        return $ \r -> Expression_Feedback r feedback e
    <|>
    do
        n <- lexEta
        e <- aexp
        return $ \r -> Expression_Eta r n e
    <|>
    do
        lexeme LexMustUse
        e        <- aexp
        return $ \r -> Expression_MustUse r e
    <|>
    do 
        l <- literal
        return $ \r -> Expression_Literal r l
    <|>
    do
        lexLBRACKET
        aexp1
    ) <?> Texts.parserExpression

fbind :: HParser RecordExpressionBinding
fbind = addRange $ do
    n <- varid
    lexASG
    e <- exp_
    return (\r -> RecordExpressionBinding_RecordExpressionBinding r n e )

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
        lexRBRACKET
        return $ \r -> Expression_Constructor r
                        (Name_Special r [] [] "[]") -- !!!Name
    <|>
    do
        e1 <- exp_
        e2 <- aexp2 e1
        lexRBRACKET
        return e2
        
aexp2 :: Expression -> HParser (Range -> Expression)    
aexp2 e1 = 
    do
        lexBAR
        qs <- commas1 qual
        return $ \r -> Expression_Comprehension r e1 qs
    <|> 
    do
        lexDOTDOT
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
        lexCOMMA
        e2 <- exp_
        aexp3 e1 e2
    <|>
    return (\r -> Expression_List r [e1])

aexp3 :: Expression -> Expression -> HParser (Range -> Expression)    
aexp3 e1 e2 =
    do
        lexDOTDOT
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
        es <- many (do { lexCOMMA; exp_ })
        return $ \r -> Expression_List r (e1:e2:es)              

{-
stmts  -> "{" stmt1 ";" ... ";" stmtn "}"   (n>=0)  
-}

stmts :: HParser Statements
stmts = 
    withLayout stmt

{-
stmt    ->  "let" decls  
         |  pat "<-" exp  
         |  exp
-}

stmt :: HParser Statement
stmt = addRange $
    do
        lexLET
        ds <- decls
        option (\r -> Statement_Let r ds) $ do
            lexIN
            e <- exp_
            return (\r -> Statement_Expression r (Expression_Let r ds e))
    <|>
    do
        p <- try $
            do
                p <- pat
                lexLARROW
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
  do as <- withLayout alt
     return $ CollectFunctionBindings.mergeCaseFeedback as

{-
alt -> pat rhs
-}

alt :: HParser Alternative
alt = addRange $
    do fb <- lexCaseFeedback
       return $ \r -> Alternative_Feedback r fb $ Alternative_Hole r ""
    <|>
    do
       n <- lexNamedHole
       return $ \r -> Alternative_Hole r n
    <|>
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
        lexLET
        ds <- decls
        option (\r -> Qualifier_Let r ds) $ do
            lexIN
            e <- exp_
            return (\r -> Qualifier_Guard r (Expression_Let r ds e))
    <|>
    do
        p <- try $
            do
                p <- pat
                lexLARROW
                return p
        e <- exp_
        return $ \r -> Qualifier_Generator r p e
    <|>
    do
        e <- exp_
        return $ \r -> Qualifier_Guard r e

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
        ps <- fmap concat $ many $
            do
                o <- do { n <- qconop; return (Pattern_Variable noRange n) }
                u' <- unaryMinusPat
                return (o : u')
        return $ \_ -> Pattern_List noRange (u ++ ps)
        
unaryMinusPat :: HParser [Pattern]
unaryMinusPat = 
    do 
        (n, mr) <- withRange (do { lexMINDOT; return floatUnaryMinusName } <|> 
                              do { lexMIN;    return intUnaryMinusName   } )
        (l, lr) <- withRange numericLiteral
        return 
            [ Pattern_Variable noRange (setNameRange n mr)
            , Pattern_Literal lr l
            ]
    <|>
    do
        p <- pat10
        return [p]
    
{-
pat10   ->  con apat*
         |  apat  
-}

pat10 :: HParser Pattern
pat10 = addRange (
    do
        (n, bs) <- try $ do 
            n <- con
            bs <- braces (fpat `sepBy` lexCOMMA)
            return (n, bs)
        return $ \r -> Pattern_Record r n bs
    <|>
    do  
        n  <- try gcon
        ps <- many apat
        return $ \r -> Pattern_Constructor r n ps
    )
    <|>
    apat
    <?> Texts.parserPattern
       
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
         |  "~" apat    (irrefutable pattern)
-}

apat :: HParser Pattern
apat = addRange (
    do
        v <- try var -- because of parentheses
        option (\r -> Pattern_Variable r v) $ do
            lexAT
            p <- apat
            return $ \r -> Pattern_As r v p
    <|>
    do
        ps <- parens (commas pat)
        return $ \r -> case ps of
            [p] -> Pattern_Parenthesized r p
            _ -> Pattern_Tuple r ps
    <|>
    do
        ps <- brackets (commas pat)
        return $ \r -> case ps of
            [] -> Pattern_Constructor r (Name_Special r [] [] "[]") [] -- !!!Name
            _ -> Pattern_List r ps
    <|> 
    do
        lexUNDERSCORE
        return $ \r -> Pattern_Wildcard r
    <|>
    do
        (n, bs) <- try $ do 
            n <- qcon
            bs <- braces (fpat `sepBy` lexCOMMA)
            return (n, bs)
        return $ \r -> Pattern_Record r n bs
    <|>
    do
        n <- gcon
        return $ \r -> Pattern_Constructor r n []
    <|>
    do
        l <- literal
        return $ \r -> Pattern_Literal r l
    <|>
    do  
        lexTILDE
        p <- apat
        return $ \r -> Pattern_Irrefutable r p
    ) <|> phole <?> Texts.parserPattern


fpat :: HParser RecordPatternBinding
fpat = addRange $ do
    n <- varid
    lexASG
    p <- pat
    return (\r -> RecordPatternBinding_RecordPatternBinding r n p )


phole :: HParser Pattern
phole = addRange (
    do
        n <- lexNamedHole
        return $ \r -> Pattern_Hole r n
    )

{-
scontext -> class | "(" class1 "," ... "," classn ")"    (n>=0)
simpleclass -> tycls tyvar
         (other case in Haskell report at 'class' is not supported in Helium
          because we do not have type variable application)
-}

scontext :: HParser ContextItems
scontext = 
    do { c <- simpleclass; return [c] }
    <|>
    parens (commas simpleclass)

simpleclass :: HParser ContextItem
simpleclass = addRange (do
    c <- qtycon
    (v, vr) <- withRange tyvar
    return $ \r -> ContextItem_ContextItem r c [Type_Variable vr v MaybeUnit_Nothing]
    )
    
{-
type  ->  btype ( "->" type )? 
-}

type_ :: HParser Type
type_ = addRange (
    do 
        left <- btype
        option (\_ -> left) $
            do
                (_, rangeArrow) <- withRange lexRARROW
                right <- type_
                return (\r -> Type_Application r False
                        (Type_Constructor rangeArrow (Name_Special rangeArrow [] [] "->") MaybeUnit_Nothing) [left, right]) -- !!!Name
    ) <?> Texts.parserType

{-
btype  ->  atype+
-}

btype :: HParser Type
btype = addRange (
    do
        ts <- many1 atype
        return $ \r -> case ts of
            [t] -> t
            (t:ts') -> Type_Application r True t ts'
            []  -> error "Pattern match failure in Parser.Parser.btype"
    ) <?> Texts.parserType

{-  (inst in Haskell2010)
    iType -> tycon
         |  "(" ")"  (unit type)
         |  "(" type1 "," ... "," typek ")"  (tuple type, k>=2)  
         |  "(" type ")"  (parenthesized constructor)
         |  "[" type "]"  (list type)
-}
iType :: HParser Type
iType = addRange (
    do
        c <- gtycon
        return (\r -> Type_Constructor r c MaybeUnit_Nothing)
    <|>
    do
        ts <- parens (commas type_)
        return (\r -> case ts of
            [] -> Type_Constructor r (Name_Special r [] [] "()") MaybeUnit_Nothing -- !!!Name
            [t] -> Type_Parenthesized r t
            _ -> let n = Name_Special r [] []  -- !!!Name
                            ( "(" ++ replicate (length ts - 1) ',' ++ ")" )
                 in Type_Application r False (Type_Constructor r n MaybeUnit_Nothing) ts
         )
    <|>
    do
        t <- brackets type_
        return $ \r ->
            let n = Name_Special r [] [] "[]" -- !!!Name
            in Type_Application r False (Type_Constructor r n MaybeUnit_Nothing) [t]
    ) <?> Texts.parserType

{-
atype   ->  tycon
         |  tyvar  
         |  "(" ")"  (unit type)  
         |  "(" type1 "," ... "," typek ")"  (tuple type, k>=2)  
         |  "(" type ")"  (parenthesized constructor)  
         |  "[" type "]"  (list type)  
-}

atype :: HParser Type
atype = addRange (
    do
        c <- gtycon
        mu <- optionMaybe (angles unit)
        return $ \r ->
            Type_Constructor r c
                (case mu of
                    Just u -> MaybeUnit_Just u
                    Nothing -> MaybeUnit_Nothing)
    <|>
    do
        c <- tyvar
        mu <- optionMaybe (angles unit)
        return $ \r ->
            Type_Variable r c
                (case mu of
                    Just u -> MaybeUnit_Just u
                    Nothing -> MaybeUnit_Nothing)
    <|>
    do
        ts <- parens (commas type_)
        return (\r -> case ts of
            [] -> Type_Constructor r (Name_Special r [] [] "()") MaybeUnit_Nothing -- !!!Name
            [t] -> Type_Parenthesized r t
            _ -> let n = Name_Special r [] [] -- !!!Name
                            ( "(" ++ replicate (length ts - 1) ',' ++ ")" )
                 in Type_Application r False (Type_Constructor r n MaybeUnit_Nothing) ts
         )
    <|>
    do
        t <- brackets type_
        return $ \r ->
            let n = Name_Special r [] [] "[]" -- !!!Name
            in Type_Application r False (Type_Constructor r n MaybeUnit_Nothing) [t]
    ) <?> Texts.parserType

annotatedType :: HParser Type -> HParser AnnotatedType
annotatedType p = addRange $
    do
        strict <- isJust <$> optionMaybe (lexeme (LexVarSym "!"))
        t <- p
        return (\r -> AnnotatedType_AnnotatedType r strict t)

literal :: ParsecT [Token] SourcePos Identity Literal
literal = addRange (
    do
        i <- lexInt
        return $ \r -> Literal_Int r i
    <|>
    do
        d <- lexDouble
        return $ \r -> Literal_Float r d
    <|>
    do
        c <- lexChar
        return $ \r -> Literal_Char r c
    <|>
    do
        s <- lexString
        return $ \r -> Literal_String r s
    ) <?> Texts.parserLiteral

numericLiteral :: ParsecT [Token] SourcePos Identity Literal
numericLiteral = addRange (
    do
        i <- lexInt
        return $ \r -> Literal_Int r i
    <|>
    do
        d <- lexDouble
        return $ \r -> Literal_Float r d
    ) <?> Texts.parserNumericLiteral

{- sdim
-}

sdim :: HParser SimpleDimension
sdim = addRange
    (do
        n <- conid
        return $ \r -> SimpleDimension_SimpleDimension r n)
    <?> Texts.parserDimension

{- unit -> firstunit
         | firstunit * unit
         | firstunit / firstunit
         | firstunit / firstunit * unit

firstunit -> sunit
         | sunit ^ n
         | "1"
         | "1" ^ n
         | "?"
         | "?" ^ n
         | "(" unit ")"
         | "(" unit ")" ^ n 
-}

sunit :: HParser SimpleUnit
sunit = addRange $
    do
        n <- unitcon
        return $ \r -> SimpleUnit_SimpleUnit r n

uexpo :: Unit -> HParser (Range -> Unit)
uexpo u = 
    do
        lexLPAREN
        m <- optionMaybe lexMIN
        expo <- fmap fromInteger (fmap read lexInt) :: HParser Int
        lexRPAREN
        case m of
            Nothing -> return $ \r -> Unit_Power r u expo
            Just _  -> return $ \r -> Unit_NegPower r u expo
    <|>
    do
        expo <- fmap fromInteger (fmap read lexInt) :: HParser Int
        return $ \r -> Unit_Power r u expo

firstunit :: HParser Unit
firstunit = addRange (
    try (do
        one <- fmap fromInteger (fmap read lexInt) :: HParser Int
        when (one /= 1) (fail Texts.parserType)
        (do
            try(do 
                lexPOWER
                u <- addRange $ return $ \r -> Unit_One r
                uexpo u)
            <|>
            (do
                return $ \r -> Unit_One r)))
    <|>
    do
        lexQUESTION
        (do
            try(do 
                lexPOWER
                u <- addRange $ return $ \r -> Unit_QuestionMark r
                uexpo u)
            <|>
            (do
                return $ \r -> Unit_QuestionMark r))

    <|>
    do
        d <- unitvar
        (do
            try(do 
                lexPOWER
                u <- addRange $ return $ \r -> Unit_Variable r d
                uexpo u)
            <|>
            (do
                return $ \r -> Unit_Variable r d))
    <|>
    do
        d <- sunit
        (do
            try(do 
                lexPOWER
                u <- addRange $ return $ \r -> Unit_Base r d
                uexpo u)
            <|>
            (do
                return $ \r -> Unit_Base r d))
    <|>
    do
        d <- parens unit
        (do
            try(do 
                lexPOWER
                u <- addRange $ return $ \r -> Unit_Parenthesized r d
                uexpo u)
            <|>
            (do
                return $ \r -> Unit_Parenthesized r d))
    )
 

unit :: HParser Unit
unit =
    addRange (
     do
        d <- firstunit
        (do
            try (do
                lexTIMES
                right <- unit
                return $ \r -> Unit_Times r d right)
            <|>
            (do
                lexDIV
                right <- firstunit
                (do
                    try (do
                        lexTIMES
                        timesright <- unit
                        return $ \r -> Unit_Times r (Unit_Div r d right) timesright)
                    <|>
                    do
                        return $ \r -> Unit_Div r d right))
            <|>
            do
                return $ \r -> d)
    ) <?> Texts.parserUnit