-- Utilities to extract data from the syntax tree
module UHA_Utils where

import UHA_Range(noRange, getNameRange)
import UHA_Syntax(Name(..), ImportDeclaration(..))
import Id(Id, idFromString, stringFromId)
import Char
import Types(isTupleConstructor)
import Utils(internalError)

instance Eq Name where
   n1 == n2 = getNameName n1 == getNameName n2

instance Ord Name where
   n1 <= n2 = getNameName n1 <= getNameName n2

instance Show Name where 
    show = getNameName  

--------------------------------------------------------------
-- NameWithRange 

newtype NameWithRange = NameWithRange { nameWithRangeToName :: Name }

instance Show NameWithRange where
   show (NameWithRange name) = 
      show name ++ " at " ++ show (getNameRange name)
   
instance Eq  NameWithRange where
   NameWithRange name1 == NameWithRange name2 = 
      (name1, getNameRange name1) == (name2, getNameRange name2)
      
instance Ord NameWithRange where
   NameWithRange name1 <= NameWithRange name2 = 
      (name1, getNameRange name1) <= (name2, getNameRange name2)
      
--------------------------------------------------------------

getNameName :: Name -> String
getNameName (Name_Identifier _ _ name) = name
getNameName (Name_Operator   _ _ name) = name
getNameName (Name_Special    _ _ name) = name

idFromName :: Name -> Id
idFromName (Name_Special _ _ s) = idFromString s
idFromName (Name_Identifier _ _ s) = idFromString s
idFromName (Name_Operator _ _ s) = idFromString s

nameFromId :: Id -> Name
nameFromId = nameFromString . stringFromId

nameFromString :: String -> Name
nameFromString str@(first:_) 
    | isAlpha first = Name_Identifier noRange [] str 
    | str == "[]" || isTupleConstructor str || str == "->" 
                    = Name_Special noRange [] str
    | otherwise     = Name_Operator noRange [] str
nameFromString _ = internalError "UHA_Utils" "nameFromString" "empty string"

isOperatorName :: Name -> Bool
isOperatorName (Name_Operator _ _ _) = True
isOperatorName _ = False

isConstructor :: Name -> Bool
isConstructor name = 
    case name of
        Name_Operator   _ _ (':':_)   -> True
        Name_Identifier _ _ (first:_) -> isUpper first
        Name_Special    _ _ "()"      -> True
        Name_Special    _ _ "[]"      -> True
        _                             -> False
        
isIdentifierName :: Name -> Bool
isIdentifierName (Name_Identifier _ _ _) = True
isIdentifierName _ = False

showNameAsOperator :: Name -> String
showNameAsOperator name
   | isIdentifierName name = "`"++show name++"`"
   | otherwise             = show name

showNameAsVariable :: Name -> String
showNameAsVariable name
   | isOperatorName name = "("++show name++")"
   | otherwise           = show name

stringFromImportDeclaration :: ImportDeclaration -> String
stringFromImportDeclaration importDecl =
    case importDecl of
        ImportDeclaration_Import _ _ n _ _ -> getNameName n
        ImportDeclaration_Empty _ -> 
            internalError "UHA_Utils" "stringFromImportDeclaration" "empty import declaration"


