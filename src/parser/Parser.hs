module Parser(parseModule) where

{-
Verschillen:
- geen records
- geen classes (class, instance, default...)
- geen irrefutable patterns
- geen "newtype"
- geen strictness annotaties
- geen n+k patterns
- [] en (,) en (,,,) enz niet toegestaan als (type) constructor
- vereenvoudigde funlhs ( bijv. x:xs +++ ys = ...   mag niet, ronde haken om x:xs nodig)
- patroon binding met apat i.p.v. pat0 
        e.g. (x:xs) = [1..] (ronde haakjes zijn nodig in Helium)

- geen sections
- geen lege declaraties, qualifiers, alternatieven of statements
- geen guarded alternatives in case
- geen "where" bij alternatieven
-}

import HaskellLexer hiding (conid, varid)
import Parsec
import ParsecPos

import UHA_Syntax
import UHA_Utils

import ParseType
import ParseImportExport
import ParseCommon
import ParseDeclExp

import qualified CollectFunctionBindings
import Utils

import System

-- For printing an error when there are imports that are not on the top
import IOExts(unsafePerformIO)
import Messages(showPositions)

test p s = runHParser p "" s

parseModule :: String -> IO (Either String Module)
parseModule fullName = parseFile module_ fullName

{-
parseOnlyImports :: String -> IO [ImportDeclaration]
parseOnlyImports fullName = parseFile onlyImports fullName
-}

-- Parse file
parseFile :: HParser a -> String -> IO (Either String a)
parseFile parser fullName =
    do
        contents <- catch (readFile fullName)
            (\ioError -> 
                let message = "Cannot read file " ++ show fullName 
                           ++ " (" ++ show ioError ++ ")"
                in throw message)

        case runHParser parser fullName contents of
            Left parseError -> do
                return (Left ("Parse error: " ++ show parseError))
            Right module_ ->
                return (Right module_)


{-
module  
    ->  "module" modid exports? "where" body  
--      |  body  
-}

module_ :: HParser Module
module_ = addRange $
    do
        reserved "module"
        n <- modid
        mes <- option MaybeExports_Nothing (fmap MaybeExports_Just exports)
        reserved "where"
        b <- body
        return (\r ->
            Module_Module r (MaybeName_Just n) mes b)
    <|>
    do 
        b <- body
        return (\r ->
            Module_Module r MaybeName_Nothing MaybeExports_Nothing b)

onlyImports :: HParser [ImportDeclaration]
onlyImports = 
    do
        reserved "module"
        modid
        option MaybeExports_Nothing (fmap MaybeExports_Just exports)
        reserved "where"
        option () (special "{")
        many (do { i <- impdecl; option () (special ";"); return i })
        
{-
body  ->  "{" topdecls "}"
topdecls  ->  topdecl1 ";" ... ";" topdecln    (n>=0)  
-}

body = addRange $
    do
        ts <- layout "declaration" "\";\"" sepBy1 lcurly rcurly semi topdecl
        let (is, ds) = splitDecls ts
            groupedDecls = CollectFunctionBindings.decls ds
        return $ \r -> Body_Body r is groupedDecls

splitDecls :: [Either ImportDeclaration Declaration] -> ([ImportDeclaration], [Declaration])
splitDecls [] = ([], [])
splitDecls (Left i : rest)  = let (is, ds) = splitDecls rest in (i:is, ds)
splitDecls (Right d : rest) = 
    let (is, ds) = splitDecls rest in
        if not (null is) then
            unsafePerformIO $ do
                putStrLn $ (showPositions (map rangeFromImportDeclaration is)) ++
                    ": Import declarations should all be at the top of the module"
                System.exitWith (ExitFailure 1)
        else
            (is, d:ds)

    
{-
topdecl  
    ->  impdecl  
     |  "data" simpletype "=" constrs
     |  "type" simpletype "=" type
     |  infixdecl
     |  decl  

simpletype  
    ->  tycon tyvar1 ... tyvark  (k>=0)  
-}

topdecl :: HParser (Either ImportDeclaration Declaration)
topdecl = 
    fmap Left impdecl
    <|>
    fmap Right (addRange (
        do
            reserved "data"
            st <- simpleType
            reservedOp "="
            cs <- constrs
            return (\r -> Declaration_Data r [] st cs [])
        <|>
        do
            reserved "type"
            st <- simpleType
            reservedOp "="
            t <- type_
            return $ \r -> Declaration_Type r st t
        <|>
        infixdecl
        )
        <|>
        decl
    ) <?> "declaration"

simpleType :: HParser SimpleType
simpleType =
    addRange (
        do
            c  <- tycon
            vs <- many tyvar
            return $ \r -> SimpleType_SimpleType r c vs
    ) <?> "simple type"
    
{-
infixdecl   ->  fixity [digit] ops  (fixity declaration)  
fixity      ->  "infixl" | "infixr" | "infix"  
ops         ->  op1 "," ... "," opn    (n>=1)  
-}

infixdecl :: HParser (Range -> Declaration)
infixdecl = 
    do
        f <- fixity
        p <- fmap fromInteger (option 9 natural) :: HParser Int
        if p < 0 || p > 9 then fail "priority must be a single digit"
                          else return ()
        os <- ops
        return $ \r -> Declaration_Fixity r f (MaybeInt_Just p) os

ops :: HParser Names
ops = commas1 op

fixity :: HParser Fixity
fixity = addRange $ 
    do
        reserved "infixl" 
        return $ \r -> Fixity_Infixl r
    <|>
    do
        reserved "infixr" 
        return $ \r -> Fixity_Infixr r
    <|>
    do
        reserved "infix" 
        return $ \r -> Fixity_Infix r
    
{-
constrs  ->  constr1 "|" ... "|" constrn  (n>=1)  
-}

constrs :: HParser Constructors
constrs = constr `sepBy1` reservedOp "|"

{-
constr  ->  btype conop btype  (infix conop)  
         |  con atype1 ... atypek  (arity con = k, k>=0)  
-}

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
        n <- con 
        ts <- many (annotatedType atype)
        return (\r -> Constructor_Constructor r n ts)
        
