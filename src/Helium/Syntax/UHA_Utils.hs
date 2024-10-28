{-# OPTIONS_GHC -fno-warn-orphans #-}
{-| Module      :  UHA_Utils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    Utilities to extract data from the syntax tree
-}

module Helium.Syntax.UHA_Utils where

--import Helium.UHA_Range(noRange, getNameRange)

import Helium.Syntax.UHA_Range  --altered for Holmes
import Data.Maybe     --added for Holmes
import Helium.Syntax.UHA_Syntax --added for Holmes
import Helium.Lvm.Common.Id(Id, idFromString, stringFromId)
--import Data.Char
import Data.List(intercalate)

import Helium.Top.Top.Types
import Helium.Utils.Utils(internalError)


instance Eq Name where
   n1 == n2 = getNameName n1 == getNameName n2

instance Ord Name where
   n1 <= n2 = getNameName n1 <= getNameName n2

instance Show Name where
    show name = getNameName name

--------------------------------------------------------------
-- NameWithRange 

newtype NameWithRange = NameWithRange { nameWithRangeToName :: Name }

instance Show NameWithRange where
   show (NameWithRange name) = 
      getNameName name ++ " at " ++ show (getNameRange name)
   
instance Eq  NameWithRange where
   NameWithRange name1 == NameWithRange name2 = 
      (name1, getNameRange name1) == (name2, getNameRange name2)
      
instance Ord NameWithRange where
   NameWithRange name1 <= NameWithRange name2 = 
      (name1, getNameRange name1) <= (name2, getNameRange name2)
      
--------------------------------------------------------------

getNameName :: Name -> String -- !!!Name
getNameName (Name_Identifier _ qs o name) = intercalate "." (qs ++ [name])
getNameName (Name_Operator   _ qs o name) = intercalate "." (qs ++ [name])
getNameName (Name_Special    _ qs o name) = intercalate "." (qs ++ [name])

getOnlyName :: Name -> String -- !!!Name
getOnlyName (Name_Identifier _ _ _ name) = name
getOnlyName (Name_Operator   _ _ _ name) = name
getOnlyName (Name_Special    _ _ _ name) = name

-- added for Holmes
getHolmesName :: String -> Name -> String -- !!!Name
getHolmesName altname (Name_Identifier range _ _ name) = getFrom range altname ++ "." ++ name
getHolmesName altname (Name_Operator   range _ _ name) = getFrom range altname ++ "." ++ name
getHolmesName altname (Name_Special    range _ _ name) = getFrom range altname ++ "." ++ name

getFrom :: Range -> [Char] -> [Char]
getFrom range altname = if result == "" then altname else result
        where
             result = snd $ checkRange range
             checkRange _ = fromMaybe ("","") moduleFI
             moduleFI = modulesFromImportRange range

getModuleName :: Module -> String       -- added for Holmes
getModuleName (Module_Module _ MaybeName_Nothing _ _) = ""
getModuleName (Module_Module _ (MaybeName_Just name) _ _) = show name

showWholeName :: Name -> String
showWholeName (Name_Identifier _ qs o name) = intercalate "." (qs ++ [name])  ++ " from " ++ o
showWholeName (Name_Operator   _ qs o name) = intercalate "." (qs ++ [name])  ++ " from " ++ o
showWholeName (Name_Special    _ qs o name) = intercalate "." (qs ++ [name])  ++ " from " ++ o

idFromName :: Name -> Id -- !!!Name
idFromName = idFromString . getNameName

nameFromId :: Id -> Name
nameFromId = nameFromString . stringFromId

nameFromString :: String -> Name -- !!!Name
nameFromString = nameFromBareString . getQualifier
    where
        nameFromBareString :: ([String], String) -> Name
        nameFromBareString (quals, s@(first:_))
            | myIsAlpha first = Name_Identifier noRange quals [] s 
            | s == "[]" || isTupleConstructor s || s == "->" 
                            = Name_Special noRange quals [] s
            | otherwise     = Name_Operator noRange quals [] s
        nameFromBareString _ = internalError "UHA_Utils" "nameFromString" "empty string"

isOperatorName :: Name -> Bool -- !!!Name
isOperatorName (Name_Operator{}) = True
isOperatorName _ = False

isConstructor :: Name -> Bool -- !!!Name
isConstructor name = 
    case name of
        Name_Operator   _ _ _ (':':_)   -> True
        Name_Identifier _ _ _ (first:_) -> myIsUpper first
        Name_Special    _ _ _ "()"      -> True
        Name_Special    _ _ _ "[]"      -> True
        _                               -> False
        
isIdentifierName :: Name -> Bool -- !!!Name
isIdentifierName (Name_Identifier{}) = True
isIdentifierName _ = False

showNameAsOperator :: Name -> String
showNameAsOperator name
   | isIdentifierName name = "`"++show name++"`"
   | otherwise             = show name

showNameAsVariable :: Name -> String
showNameAsVariable name
   | isOperatorName name = "("++show name++")"
   | otherwise           = show name

nameFromImportDeclaration :: ImportDeclaration -> Name
nameFromImportDeclaration importDecl =
    case importDecl of
        ImportDeclaration_Import _ _ n _ _ -> n
        ImportDeclaration_Empty _ -> 
            internalError "UHA_Utils" "nameFromImportDeclaration" "empty import declaration"

-- TODO: daan
intUnaryMinusName, floatUnaryMinusName, enumFromName, enumFromToName, enumFromThenName, enumFromThenToName :: Name
intUnaryMinusName   = nameFromString "Prelude.negate"
floatUnaryMinusName = nameFromString "$floatUnaryMinus"
enumFromName        = nameFromString "Prelude.enumFrom"
enumFromToName      = nameFromString "Prelude.enumFromTo"
enumFromThenName    = nameFromString "Prelude.enumFromThen"
enumFromThenToName  = nameFromString "Prelude.enumFromThenTo"

patternVars :: Pattern -> [Name]
patternVars p = case p of
    Pattern_Literal _ _                 -> []
    Pattern_Variable _ n                -> [n]
    Pattern_Constructor _ _ ps          -> concatMap patternVars ps
    Pattern_Parenthesized _ pat         -> patternVars pat
    Pattern_InfixConstructor _ p1 _ p2  -> concatMap patternVars [p1, p2]
    Pattern_List _ ps                   -> concatMap patternVars  ps
    Pattern_Tuple _ ps                  -> concatMap patternVars  ps
    Pattern_Negate _ _                  -> []
    Pattern_As _ n pat                  -> n : patternVars pat
    Pattern_Wildcard _                  -> []
    Pattern_Irrefutable _ pat           -> patternVars pat
    Pattern_NegateFloat _ _             -> []
    _ -> internalError "UHA_Utils" "patternVars" "unsupported kind of pattern"

--Extract the name(s) of a declaration
nameOfDeclaration :: Declaration -> Names
nameOfDeclaration d = case d of
    Declaration_Class            _ _ (SimpleType_SimpleType _ n _) _   -> [n]
    Declaration_Data             _ _ (SimpleType_SimpleType _ n _) _ _ -> [n]
    Declaration_Default          _ _                                   -> [] --What does the Default do, it is not created by the parser...
    Declaration_Empty            _                                     -> []
    Declaration_Fixity           _ _ _ ns                              -> ns
    Declaration_FunctionBindings _ fb                                  -> [head $ concatMap nameOfFunctionBinding fb]
    Declaration_Instance         _ _ n _ _                             -> [n]
    Declaration_Newtype          _ _ (SimpleType_SimpleType _ n _) _ _ -> [n]
    Declaration_PatternBinding   _ _ _                                 -> [] --Not entirely sure whether this is correct or not (a directly declared pattern is a binding to the names in the pattern...)
    Declaration_Type             _ (SimpleType_SimpleType _ n _) _     -> [n]
    Declaration_TypeSignature    _ ns _                                -> ns
    Declaration_Hole             _ _                                   -> []
    
nameOfFunctionBinding :: FunctionBinding -> Names
nameOfFunctionBinding (FunctionBinding_FunctionBinding _ lhs _) = nameOfLeftHandSide lhs
nameOfFunctionBinding (FunctionBinding_Hole _ _)                = []
nameOfFunctionBinding (FunctionBinding_Feedback _ _ fb)         = nameOfFunctionBinding fb -- Check: Bastiaan
            
nameOfLeftHandSide :: LeftHandSide -> Names
nameOfLeftHandSide lhs = case lhs of
    LeftHandSide_Function _ n _      -> [n]
    LeftHandSide_Infix _ _ n _       -> [n]
    LeftHandSide_Parenthesized _ l _ -> nameOfLeftHandSide l

setNameOrigin :: String -> Name -> Name -- !!!Name
setNameOrigin orig (Name_Identifier range qual _ name) = Name_Identifier range qual orig name
setNameOrigin orig (Name_Operator   range qual _ name) = Name_Operator   range qual orig name
setNameOrigin orig (Name_Special    range qual _ name) = Name_Special    range qual orig name

getNameOrigin :: Name -> String
getNameOrigin (Name_Identifier _ _ orig _) = orig
getNameOrigin (Name_Operator   _ _ orig _) = orig
getNameOrigin (Name_Special    _ _ orig _) = orig

getQualifier :: String -> ([String], String)
getQualifier = getQualifier' []
    where
        getQualifier' quals s@(fir:_) 
            | myIsUpper fir = let (qual, rest) = span isLetter s in
                                case rest of
                                    '.':rest' -> getQualifier' (qual : quals) rest' 
                                    _         -> (quals, s)
            | otherwise = (quals, s)
        getQualifier' _ _ = ([],"")

unQualifyString :: String -> String
unQualifyString = snd . getQualifier

removeQualified :: Name -> Name
removeQualified = addQualified []

addQualified :: [String] -> Name -> Name
addQualified _      (Name_Identifier range _ orig []) = Name_Identifier range [] orig []
addQualified _      (Name_Operator range _ orig [])   = Name_Operator range [] orig []
addQualified _      (Name_Special range _ orig [])    = Name_Special range [] orig []
addQualified qual (Name_Identifier range _ orig name) = Name_Identifier range qual orig name
addQualified qual (Name_Operator range _ orig name)   = Name_Operator range qual orig name
addQualified qual (Name_Special range _ orig name)    = Name_Special range qual orig name

getQualified :: Name -> [String]
getQualified (Name_Identifier _ qual _ name) = qual ++ [name]
getQualified (Name_Operator   _ qual _ name) = qual ++ [name]
getQualified (Name_Special    _ qual _ name) = qual ++ [name]

getQualifiedFromString :: String -> [String]
getQualifiedFromString str = qual ++ [name]
    where
        (qual, name) = getQualifier str

isQualified :: Name -> Bool 
isQualified (Name_Identifier _ [] _ _) = False
isQualified (Name_Operator _ [] _ _)   = False
isQualified (Name_Special _ [] _ _)    = False
isQualified _ = True

isQualifiedString :: String -> Bool
isQualifiedString [] = False
isQualifiedString s@(fir:_)
            | myIsUpper fir = let (_, rest) = span isLetter s in
                            case rest of
                                '.':_ -> True
                                _         -> False
            | otherwise = False

convertString :: (Name -> Name) -> String -> String
convertString f = getNameName . f . nameFromString 

convertTpScheme :: (Name -> Name) -> TpScheme -> TpScheme
convertTpScheme f (Quantification (xs, qm, (Qualification (pre, ty)))) = Quantification (xs, qm, (Qualification (map (convertPredicate f) pre,convertTp f ty)))

convertTpInScheme :: (Tp -> Tp) -> TpScheme -> TpScheme
convertTpInScheme f (Quantification (xs, qm, (Qualification (pre, ty)))) = (Quantification (xs, qm, (Qualification (pre, f ty))))

convertTp :: (Name -> Name) -> Tp -> Tp
convertTp _ t@(TVar _) = t
convertTp f (TCon str) = TCon $ convertString f str
convertTp f (TApp t1 t2) = TApp (convertTp f t1) (convertTp f t2)

convertPredicate :: (Name -> Name) -> Predicate -> Predicate
convertPredicate f (Predicate n tp) = Predicate (getNameName $ f $ nameFromString n) (convertTp f tp)
-------------------------------------
-- Got these from the lexer.
isLetter :: Char -> Bool
isLetter '\'' = True
isLetter '_'  = True
isLetter c    = myIsAlphaNum c

-- write our own isLower.. so that we don't accept funny symbols
myIsLower :: Char -> Bool
myIsLower c = c >= 'a' && c <= 'z'

myIsUpper :: Char -> Bool
myIsUpper c = c >= 'A' && c <= 'Z'

myIsDigit :: Char -> Bool
myIsDigit c = c >= '0' && c <= '9'

myIsAlpha :: Char -> Bool
myIsAlpha c = myIsLower c || myIsUpper c

myIsAlphaNum :: Char -> Bool
myIsAlphaNum c = myIsLower c || myIsUpper c || myIsDigit c
