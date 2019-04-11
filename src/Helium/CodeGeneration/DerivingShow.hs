{-| Module      :  DerivingShow
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.DerivingShow
    ( dataShowFunction
    , typeShowFunction
    , dataDictionary
    , typeOfShowFunction, showFunctionOfType
    ) where

import qualified Helium.Syntax.UHA_Syntax as UHA
import Helium.Syntax.UHA_Utils
import Helium.CodeGeneration.CoreUtils
import Helium.ModuleSystem.ImportEnvironment
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Lvm.Core.Expr
import Lvm.Core.Utils
import Lvm.Common.Id
import Helium.Utils.Utils
import Top.Types
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Helium.Utils.QualifiedTypes.Constants

-- Show function for a data type declaration
dataShowFunction :: ClassEnvironment -> TypeSynonymEnvironment -> UHA.Declaration -> [String] -> [Custom] -> Expr
dataShowFunction classEnv tse (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ name names) constructors _) qual origin =
    let typeString = show (typeOfShowFunction name qual names)
        nameId     = idFromString ("show" ++ (unQualifyName . getNameName) name)
        valueId    = idFromString "value$"
        in
        foldr Lam 
        (Let 
            (Strict (Bind valueId (Var valueId)))
            (Match valueId
                (map (makeAlt classEnv tse) constructors)
            )
        )   
        ( (map idFromName names ++ [valueId])
        ++ [idFromString "$instanceDictShow", valueId])
dataShowFunction _ _ _ _ _ = error "not supported"

--TODO Fix qual
-- Show Dictionary for a data type declaration
dataDictionary :: ClassEnvironment -> TypeSynonymEnvironment -> UHA.Declaration -> [String] -> [Custom] -> CoreDecl
dataDictionary classEnv tse decl@(UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ name names) _ _) qual origin =
    DeclValue 
    { declName    = idFromString ("$dictShow$" ++ getNameName name)
    , declAccess  = public
    , valueEnc    = Nothing
    , valueValue  = makeShowDictionary (length names)
    , declCustoms = [ custom "type" ("DictShow$" ++ getNameName name)] 
                ++ map (custom "typeVariable" . getNameName) names
                ++ map (\n -> custom "superInstance" ("Show-" ++ getNameName n)) names
                ++ origin
    }
  where
    makeShowDictionary :: Int -> Expr
    makeShowDictionary nrOfArgs =
       let 
           showBody = dataShowFunction classEnv tse decl qual origin
           ids  = map idFromName names
           list = map idFromString ["showsPred", "showList", "showDef"]
           declarations = zipWith Bind list [Var $ idFromString "default$Show$showsPrec", Var $ idFromString "default$Show$showList", showBody]
           body = Let (Rec declarations) (foldl Ap (Con $ ConId $ idFromString "DictShow") $ map Var list)
       in foldr Lam body ids
dataDictionary _ _ _ _ _ = error "not supported"

-- Show function for a type synonym
-- type T a b = (b, a) 
--   ===>
-- showT :: (a -> String) -> (b -> String) -> T a b -> String
-- showT a b = showTuple2 b a 
typeShowFunction :: ClassEnvironment -> TypeSynonymEnvironment -> UHA.Declaration -> [String] -> [Custom] -> Decl Expr
typeShowFunction classEnv tse (UHA.Declaration_Type _ (UHA.SimpleType_SimpleType _ name names) type_) qual origin =
    let typeString = show (typeOfShowFunction name qual names) in
    DeclValue 
    { declName    = idFromString ("show" ++ (unQualifyName . getNameName) name)
    , declAccess  = public
    , valueEnc    = Nothing
    , valueValue  = foldr (Lam . idFromName) (showFunctionOfType classEnv tse False type_) names
    , declCustoms = [ custom "type" typeString ] ++ origin
    }
typeShowFunction _ _ _ _ _ = error "not supported"

-- Convert a data type constructor to a Core alternative
makeAlt :: ClassEnvironment -> TypeSynonymEnvironment -> UHA.Constructor -> Alt
makeAlt classEnv tse c = Alt (constructorToPat ident types) (showConstructor classEnv tse ident types)
  where
    (ident, types) = nameAndTypes c
    
    nameAndTypes :: UHA.Constructor -> (Id, [UHA.Type])
    nameAndTypes c' =
        case c' of
            UHA.Constructor_Constructor _    n ts -> (idFromName n, map annotatedTypeToType ts      )
            UHA.Constructor_Infix       _ t1 n t2 -> (idFromName n, map annotatedTypeToType [t1, t2])
            UHA.Constructor_Record _ _ _          -> error "not supported"
    constructorToPat :: Id -> [UHA.Type] -> Pat
    constructorToPat ident' ts =
        PatCon (ConId ident') [ idFromNumber i | i <- [1..length ts] ]
        
    annotatedTypeToType :: UHA.AnnotatedType -> UHA.Type
    annotatedTypeToType (UHA.AnnotatedType_AnnotatedType _ _ t) = t

-- Show expression for one constructor
showConstructor :: ClassEnvironment -> TypeSynonymEnvironment -> Id -> [UHA.Type] -> Expr
showConstructor classEnv tse c ts -- name of constructor and paramater types
    | isConOp && length ts == 2 = 
        Ap (Var (idFromString "$primConcat")) $ coreList 
            [   stringToCore "("
            ,   Ap (Ap (var "show") (showFunctionOfType classEnv tse False (ts!!0))) (Var (idFromNumber 1))
            ,   stringToCore name
            ,   Ap (Ap (var "show") (showFunctionOfType classEnv tse False (ts!!1))) (Var (idFromNumber 2))
            ,   stringToCore ")"
            ]
    | otherwise =
        Ap (Var (idFromString "$primConcat")) $ coreList 
            (  (if null ts then [] else [stringToCore "("])
            ++ (if isConOp then parens else id) [stringToCore name]
            ++ concat
                   [ [stringToCore " ", Ap (Ap (var "show") (showFunctionOfType classEnv tse False t)) (Var (idFromNumber i))]
                   | (t, i) <- zip ts [1..] 
                   ]
            ++ (if null ts then [] else [stringToCore ")"])
            )
  where
    name = stringFromId c
    isConOp = head name == ':'
    parens s = [ stringToCore "(" ] ++ s ++ [ stringToCore ")" ]

-- What show function to call for a specific type. Returns a Core expression
-- If this function is called for the main function, type variables are printed
-- using showPolymorphic. Otherwise, a show function for the type variable
-- should be available
showFunctionOfType :: ClassEnvironment -> TypeSynonymEnvironment -> Bool -> UHA.Type -> Expr
showFunctionOfType classEnv tse isMainType = sFOT 0
  where
    expandTS :: UHA.Type -> UHA.Type
    expandTS t@(UHA.Type_Constructor _ n) = case M.lookup n tse of
        Just (i, g) -> makeTypeFromTp (g $ take i (map TCon variableList))
        Nothing -> t
    expandTS t = t
    sFOT nrOfArguments tp  =
        let 
            t = expandTS tp
        in 
      case t of
        UHA.Type_Variable _ n             -> if isMainType then var "$dictShow$Int" else Var (idFromName n) 
        -- show Strings not as List of Char but using showString
        UHA.Type_Application _ _ 
                    ( UHA.Type_Constructor _ (UHA.Name_Special    _ _ _ "[]") ) -- !!!Name
                    [ UHA.Type_Constructor _ (UHA.Name_Identifier _ _ _ "Char") ] -- !!!Name
                ->  Ap (var "$dictShow$[]") (var "$dictShow$Char" )
        UHA.Type_Constructor _ n         -> 
            let conname = (unQualifyName . getNameName) n
            in checkForPrimitiveDict nrOfArguments classEnv conname
        UHA.Type_Application _ _ f xs    -> foldl Ap (sFOT (length xs) f) (map (sFOT 0) xs )
        UHA.Type_Parenthesized _ t'      -> showFunctionOfType classEnv tse isMainType t'
        _ -> internalError "DerivingShow" "showFunctionOfType" "unsupported type"

-- Some primitive types have funny names and their Show function has a different name
checkForPrimitiveDict :: Int -> ClassEnvironment -> String -> Expr
checkForPrimitiveDict nrOfArguments classEnv name =
    case name of 
        "[]" -> var "$dictShow$[]"
        "()" -> var "$dictShow$()"
        "->" -> let dict = foldl Ap (Con $ ConId $ idFromString "DictShow") functions
                    showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore "<<function>>"
                    functions = [Var $ idFromString "default$Show$showsPrec", Var $ idFromString "default$Show$showList", showFunction]
                in Lam (idFromString "d1") $ Lam (idFromString "d2") dict
        ('(':commasAndClose) -> 
            let arity = length commasAndClose in 
                if arity > 10 then
                    internalError "DerivingShow" "checkForPrimitive" "No show functions for tuples with more than 10 elements"
                else
                    var $ "$dictShow$(" ++ replicate (arity-1) ',' ++ ")"
        _ -> 
            let 
                showInstances :: Instances
                showInstances = snd $ fromJust $ M.lookup "Show" classEnv
                dict = var $ "$dictShow$" ++ name 
                isTCon :: Tp -> String -> Bool
                isTCon (TCon n) s = n == s
                isTCon (TApp t _) s = isTCon t s 
                isTCon (TVar _) _ = False
                pred = find (\((Predicate n t), _)-> isTCon t name ) showInstances
            in if isJust pred then 
                    dict 
                else 
                    let dict = foldr Lam (foldl Ap (Con $ ConId $ idFromString "DictShow") functions) $ take nrOfArguments [idFromString ("d" ++ show i) | i <- [0..]]
                        showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore ("<<type " ++ name ++ ">>")              
                        functions = [Var $ idFromString "default$Show$showsPrec", Var $ idFromString "default$Show$showList", showFunction]
                    in dict
        
idFromNumber :: Int -> Id
idFromNumber i = idFromString ("v$" ++ show i)

nameOfShowFunction :: UHA.Name -> UHA.Name
nameOfShowFunction (UHA.Name_Identifier r m o n) = UHA.Name_Identifier r m o ("show" ++ n) -- !!!Name
nameOfShowFunction _ = internalError "DerivingShow" "nameOfShowFunction" "name of type must be an identifier"

typeOfShowFunction :: UHA.Name -> [String] -> UHA.Names -> TpScheme
typeOfShowFunction name qual names =
    -- Build type from type name and parameters.
    -- e.g. data T a b = ...  ===> (0 -> String) -> (1 -> String) -> (T 0 1 -> String)
    let vars  = map TVar (take (length names) [0..])
        types = vars ++ [foldl TApp (TCon (getNameName (addQualified qual name))) vars]
    in generalizeAll ([] .=>. foldr1 (.->.) (map (.->. stringQualType) types))

