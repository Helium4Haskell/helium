module ParseImportExport(impdecl, exports) where

import HaskellLexer hiding (conid, varid)
import UHA_Syntax(ImportDeclaration(..), MaybeImportSpecification(..), ImportSpecification(..), 
                    Import(..), Name(..), Range, Exports, Export(..), MaybeName(..),
                    MaybeNames(..))
import Parsec
import ParseCommon

{-
impdecl     ->  "import" "qualified"? modid ( "as" modid )? impspec
impspec     ->  "hiding"? "(" import1 "," ... "," importn ")"    (n>=0)  
             |      (empty)
import      ->  var  
             |  conid ( "(" export1 ")" )?    (n>=0)
import1     ->  ".." | cname1 "," ... "," cnamen 
-}

impdecl :: HParser ImportDeclaration
impdecl = addRange (
    do
        reserved "import"

        {- currently no support for "qualified" -}
        -- q <- option False (do { reserved "qualified"; return True })
        let q = False

        m <- modid
        
        {- currently no support for "as"
        a <- option MaybeName_Nothing $
            do 
                reserved "as" 
                m <- modid
                return (MaybeName_Just m)
        -}
        let a = MaybeName_Nothing
        
        i <- option MaybeImportSpecification_Nothing 
                (fmap MaybeImportSpecification_Just impspec)
        return $ \r -> ImportDeclaration_Import r q m a i
    ) <?> "import declaration"

impspec :: HParser ImportSpecification
impspec = addRange $
    do  
-- Currently, no "hiding" support        h <- option False (do { reserved "hiding"; return True })
        is <- parens (commas import_)
        return $ \r -> ImportSpecification_Import r False is

import_ :: HParser Import
import_ = addRange $
{- what did this do? !!!
    try $ do
        n <- reservedOp "->" <|> parens (reservedOp "->")
        return $ \r -> Import_TypeOrClass r (Name_Special r [] "->") MaybeNames_Nothing
    <|>
-}
    do
        n <- var
        return $ \r -> Import_Variable r n
    <|>
    do 
        n <- conid 
        option (\r -> Import_TypeOrClass r n MaybeNames_Nothing) 
                    (parens (import1 n))

import1 :: Name -> HParser (Range -> Import)
import1 n =
{- Currently no support for ".." notation
    do
        reservedOp ".."
        return $ \r -> Import_TypeOrClassComplete r n
    <|> -}
    do 
        ns <- commas cname
        return $ \r -> Import_TypeOrClass r n (MaybeNames_Just ns)
    
{-
exports ->  "(" export1 "," ... "," exportn ")"    (n>=0)  
export  ->  var  
         |  "module" modid  
         |  conid ( "(" export1 ")" )?    (n>=0)
export1 -> ".." | cname1 "," ... "," cnamen 
cname   ->  var | con  
-}

exports :: HParser Exports
exports =
    parens (commas export_)

export_ :: HParser Export
export_ = addRange (
{- what did this do? !!!
try $ do
        n <- reservedOp "->" <|> parens (reservedOp "->")
        return $ \r -> Export_TypeOrClass r (Name_Special r [] "->") MaybeNames_Nothing
    <|>
-}
    do
        n <- var
        return $ \r -> Export_Variable r n
    <|>
    do
        reserved "module"
        n <- conid
        return $ \r -> Export_Module r n
    <|>
    do 
        n <- conid 
        option (\r -> Export_TypeOrClass r n MaybeNames_Nothing) 
                (parens (export1 n))
    )
export1 :: Name -> HParser (Range -> Export)
export1 n =
{- Currently no support for ".." notation
    do
        reservedOp ".."
        return $ \r -> Export_TypeOrClassComplete r n
    <|>-}
    do 
        ns <- commas cname
        return $ \r -> Export_TypeOrClass r n (MaybeNames_Just ns)

cname :: HParser Name
cname = try var <|> con
    
