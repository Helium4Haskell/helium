module ParseType(type_, atype, btype, annotatedType) where

import HaskellLexer hiding (conid, varid)
import UHA_Syntax(Type(..), Name(..), AnnotatedType(..))
import Parsec
import ParseCommon

{-
type  ->  btype ( "->" type )? 
-}

type_ :: HParser Type
type_ = addRange (
    do 
        left <- btype
        option (\_ -> left) $
            do
                (_, rangeArrow) <- withRange (reservedOp "->")
                right <- type_
                return (\r -> Type_Application r False
                        (Type_Constructor rangeArrow (Name_Special rangeArrow [] "->")) [left, right])
    ) <?> "type"

{-
btype  ->  atype+
-}

btype :: HParser Type
btype = addRange (
    do
        ts <- many1 atype
        return $ \r -> case ts of
            [t] -> t
            (t:ts) -> Type_Application r True t ts
    ) <?> "type"

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
        c <- tycon
        return (\r -> Type_Constructor r c)
    <|>
    do
        c <- tyvar
        return (\r -> Type_Variable r c)
    <|>
    do
        ts <- parens (commas type_)
        return (\r -> case ts of
            [] -> Type_Constructor r (Name_Special r [] "()")
            [t] -> Type_Parenthesized r t
            _ -> let n = Name_Special r [] 
                            ( "(" ++ replicate (length ts - 1) ',' ++ ")" )
                 in Type_Application r False (Type_Constructor r n) ts
         )
    <|>
    do
        t <- brackets type_
        return $ \r ->
            let n = Name_Special r [] "[]"
            in Type_Application r False (Type_Constructor r n) [t]
    ) <?> "type"

annotatedType :: HParser Type -> HParser AnnotatedType
annotatedType p = addRange $
    do
        t <- p
        return (\r -> AnnotatedType_AnnotatedType r False t)
