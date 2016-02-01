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
import Lvm.Common.Id(Id, idFromString, stringFromId)
import Data.Char

import Top.Types(isTupleConstructor)
import Helium.Utils.Utils(internalError)


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

getNameName :: Name -> String -- !!!Name
getNameName (Name_Identifier _ _ name) = name
getNameName (Name_Operator   _ _ name) = name
getNameName (Name_Special    _ _ name) = name

-- added for Holmes
getHolmesName :: String -> Name -> String -- !!!Name
getHolmesName altname (Name_Identifier range _ name) = getFrom range altname ++ "." ++ name
getHolmesName altname (Name_Operator   range _ name) = getFrom range altname ++ "." ++ name
getHolmesName altname (Name_Special    range _ name) = getFrom range altname ++ "." ++ name

getFrom :: Range -> [Char] -> [Char]
getFrom range altname = if result == "" then altname else result
        where
             result = snd $ checkRange range
             checkRange _ = fromMaybe ("","") moduleFI
             moduleFI = modulesFromImportRange range

getModuleName :: Module -> String       -- added for Holmes
getModuleName (Module_Module _ MaybeName_Nothing _ _) = ""
getModuleName (Module_Module _ (MaybeName_Just name) _ _) = show name

idFromName :: Name -> Id -- !!!Name
idFromName (Name_Special _ _ s) = idFromString s
idFromName (Name_Identifier _ _ s) = idFromString s
idFromName (Name_Operator _ _ s) = idFromString s

nameFromId :: Id -> Name
nameFromId = nameFromString . stringFromId

nameFromString :: String -> Name -- !!!Name
nameFromString str@(first:_) 
    | isAlpha first = Name_Identifier noRange [] str 
    | str == "[]" || isTupleConstructor str || str == "->" 
                    = Name_Special noRange [] str
    | otherwise     = Name_Operator noRange [] str
nameFromString _ = internalError "UHA_Utils" "nameFromString" "empty string"

isOperatorName :: Name -> Bool -- !!!Name
isOperatorName (Name_Operator{}) = True
isOperatorName _ = False

isConstructor :: Name -> Bool -- !!!Name
isConstructor name = 
    case name of
        Name_Operator   _ _ (':':_)   -> True
        Name_Identifier _ _ (first:_) -> isUpper first
        Name_Special    _ _ "()"      -> True
        Name_Special    _ _ "[]"      -> True
        _                             -> False
        
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

stringFromImportDeclaration :: ImportDeclaration -> String
stringFromImportDeclaration importDecl =
    case importDecl of
        ImportDeclaration_Import _ _ n _ _ -> getNameName n
        ImportDeclaration_Empty _ -> 
            internalError "UHA_Utils" "stringFromImportDeclaration" "empty import declaration"

-- TODO: daan
intUnaryMinusName, floatUnaryMinusName, enumFromName, enumFromToName, enumFromThenName, enumFromThenToName :: Name
intUnaryMinusName   = nameFromString "$negate"
floatUnaryMinusName = nameFromString "$floatUnaryMinus"
enumFromName        = nameFromString "$enumFrom"
enumFromToName      = nameFromString "$enumFromTo"
enumFromThenName    = nameFromString "$enumFromThen"
enumFromThenToName  = nameFromString "$enumFromThenTo"

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
    
