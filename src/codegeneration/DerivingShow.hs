module DerivingShow(derivingShow, nameOfShowFunction, typeOfShowFunction, showFunctionOfType) where

import qualified UHA_Syntax as UHA
import UHA_Utils
import CoreUtils
import Core
import Id
import Utils
import Types

nameOfShowFunction :: UHA.Name -> UHA.Name
nameOfShowFunction (UHA.Name_Identifier r m n) = UHA.Name_Identifier r m ("show" ++ n)
nameOfShowFunction _ = internalError "DerivingShow" "nameOfShowFunction" "name of type must be an identifier"

typeOfShowFunction :: UHA.Name -> UHA.Names -> TpScheme
typeOfShowFunction name names =
    -- Build type from type name and parameters.
    -- e.g. data T a b = ...  ===> (0 -> String) -> (1 -> String) -> (T 0 1 -> String)
    let vars  = map TVar (take (length names) [0..])
        types = vars ++ [foldl TApp (TCon (getNameName name)) vars]
    in generalize [] (foldr1 (.->.) (map (.->. stringType) types))

derivingShow :: UHA.Declaration -> CoreDecl
-- !!! commentaar
derivingShow (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ name names) constructors _) =
    let typeString = show (typeOfShowFunction name names)
    in
    DeclValue 
        { declName = idFromString ("show" ++ getNameName name)
        , declAccess = public
        , valueEnc = Nothing
        , valueValue = foldr Lam 
                (Let 
                    (Strict (Bind valueId (Var valueId)))
                    (Match valueId
                        (map makeAlt constructors)
                    )
                )    
                (map idFromName names ++ [valueId])
        , declCustoms = [ customType typeString ] 
        }
    where
        valueId = idFromString "value$"

-- type T a b = (b, a) 
--   ===>
-- showT :: (a -> String) -> (b -> String) -> T a b -> String
-- showT a b = showTuple2 b a 
derivingShow decl@(UHA.Declaration_Type _ (UHA.SimpleType_SimpleType _ name names) type_) =
    let typeString = show (typeOfShowFunction name names)
    in
    DeclValue 
        { declName = idFromString ("show" ++ getNameName name)
        , declAccess = public
        , valueEnc = Nothing
        , valueValue = foldr Lam 
                (showFunctionOfType False type_)
                (map idFromName names)
        , declCustoms = [ customType typeString ] 
        }


makeAlt :: UHA.Constructor -> Alt
makeAlt c =
    Alt 
        (constructorToPat id types)
        (showConstructor id types)
    where
        (id, types) = nameAndTypes c

showConstructor :: Id -> [UHA.Type] -> Expr
showConstructor c ts =
    Ap (Var (idFromString "primConcat")) $ coreList 
        (  (if null ts then [] else [stringToCore "("])
        ++ [stringToCore (stringFromId c)]
        ++ concat
               [ [stringToCore " ", Ap (showFunctionOfType False t) (Var (idFromNumber i))]
               | (t, i) <- zip ts [1..] 
               ]
        ++ (if null ts then [] else [stringToCore ")"])
        )

showFunctionOfType :: Bool -> UHA.Type -> Expr
showFunctionOfType isMainType t =
    case t of
        UHA.Type_Variable _ n -> 
            if isMainType then var "showPolymorphic" else Var (idFromName n) 
            
        -- show Strings not as List of Char but using showString
        UHA.Type_Application _ _ 
                    ( UHA.Type_Constructor _ (UHA.Name_Identifier _ _ "[]") ) 
                    [ UHA.Type_Constructor _ (UHA.Name_Identifier _ _ "Char") ] ->
            var "showString"
            
        UHA.Type_Constructor _ n -> 
            var ("show" ++ checkForPrimitive (getNameName n))
        UHA.Type_Application _ _ f xs -> 
            foldl Ap (showFunctionOfType isMainType f) (map (showFunctionOfType isMainType) xs)
        UHA.Type_Parenthesized _ t -> 
            showFunctionOfType isMainType t
        _ -> internalError "DerivingShow" "showFunctionOfType" "unsupported type"

checkForPrimitive :: String -> String
checkForPrimitive name =
    case name of 
        "[]" -> "List"
        "()" -> "Unit"
        "->" -> "Function"
        ('(':commasAndClose) -> 
            let arity = length commasAndClose
            in 
                if arity > 10 then
                    internalError "DerivingShow" "checkForPrimitive" "can't generate show function for tuples greater than 10"
                else
                    "Tuple" ++ show arity -- !!!
        _ -> name 
        
idFromNumber :: Int -> Id
idFromNumber i = idFromString ("v$" ++ show i)

constructorToPat :: Id -> [UHA.Type] -> Pat
constructorToPat id ts =
    PatCon (ConId id) [ idFromNumber i | i <- [1..length ts] ]
                
nameAndTypes :: UHA.Constructor -> (Id, [UHA.Type])
nameAndTypes c =
    case c of
        UHA.Constructor_Constructor _    n ts -> (idFromName n, map annotatedTypeToType ts      )
        UHA.Constructor_Infix       _ t1 n t2 -> (idFromName n, map annotatedTypeToType [t1, t2])

annotatedTypeToType :: UHA.AnnotatedType -> UHA.Type
annotatedTypeToType (UHA.AnnotatedType_AnnotatedType _ _ t) = t
