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
import Helium.Utils.QualifiedTypes
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

-- Show function for a data type declaration. For some reason, it uses only little information.
dataShowFunction :: ImportEnvironment -> UHA.Declaration -> [String] -> [Custom] -> Expr
dataShowFunction env (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ _) constructors _) _ _ =
    let -- typeString = show (typeOfShowFunction name qual names)
        -- nameId     = idFromString ("show" ++ (getNameName) name)
        valueId    = idFromString "value$"
        in
        foldr Lam 
        (Let 
            (Strict (Bind valueId (Var valueId)))
            (Match valueId
                (map (makeAlt env) constructors)
            )
        )   
        ( [idFromString "$instanceDictPrelude.Show", valueId])
dataShowFunction _ _ _ _ = error "not supported"

-- Show Dictionary for a data type declaration
dataDictionary :: ImportEnvironment -> UHA.Declaration -> [String] -> [Custom] -> UHA.Name -> CoreDecl
dataDictionary env declp@(UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ names) _ _) qual origin qualname = 
    DeclValue 
    { declName    = idFromString ("$dictPrelude.Show$" ++ getNameName qualname)
    , declAccess  = public
    , valueEnc    = Nothing
    , valueValue  = makeShowDictionary (length names)
    , declCustoms = [ custom "type" ("DictPrelude.Show$" ++ getNameName qualname)] 
                ++ map (custom "typeVariable" . getNameName) names
                ++ map (\n -> custom "superInstance" ("Prelude.Show-" ++ getNameName n)) names
                ++ origin
    }
  where
    makeShowDictionary :: Int -> Expr
    makeShowDictionary _ =
       let 
           showBody = dataShowFunction env declp qual origin
           ids  = map idFromName names
           list = map idFromString ["showsPred", "showList", "showDef"]
           declarations = zipWith Bind list [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showBody]
           body = Let (Rec declarations) (foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") $ map Var list)
       in foldr Lam body ids
dataDictionary _ _ _ _ _ = error "not supported"

-- Show function for a type synonym
-- type T a b = (b, a) 
--   ===>
-- showT :: (a -> String) -> (b -> String) -> T a b -> String
-- showT a b = showTuple2 b a 
typeShowFunction :: ImportEnvironment -> UHA.Declaration -> [String] -> [Custom] -> Decl Expr
typeShowFunction env (UHA.Declaration_Type _ (UHA.SimpleType_SimpleType _ name names) type_) qual origin =
    let 
        typeString = show (typeOfShowFunction name qual names)
        -- classEnv = classEnvironment env
    in
    DeclValue 
    { declName    = idFromString ("show" ++ (getNameName) name)
    , declAccess  = public
    , valueEnc    = Nothing
    , valueValue  = foldr (Lam . idFromName) (showFunctionOfType env False type_) names
    , declCustoms = [ custom "type" typeString ] ++ origin
    }
typeShowFunction _ _ _ _ = error "not supported"

-- Convert a data type constructor to a Core alternative
makeAlt :: ImportEnvironment -> UHA.Constructor -> Alt
makeAlt env c = Alt (constructorToPat ident types) (showConstructor env ident types)
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
showConstructor :: ImportEnvironment -> Id -> [UHA.Type] -> Expr
showConstructor env c ts -- name of constructor and paramater types
    | isConOp && length ts == 2 = 
        Ap (Var (idFromString "$primConcat")) $ coreList 
            [   stringToCore "("
            ,   Ap (Ap (var "show") (showFunctionOfType env False (ts!!0))) (Var (idFromNumber 1))
            ,   stringToCore name
            ,   Ap (Ap (var "show") (showFunctionOfType env False (ts!!1))) (Var (idFromNumber 2))
            ,   stringToCore ")"
            ]
    | otherwise =
        Ap (Var (idFromString "$primConcat")) $ coreList 
            (  (if null ts then [] else [stringToCore "("])
            ++ (if isConOp then parens else id) [stringToCore name]
            ++ concat
                   [ [stringToCore " ", Ap (Ap (var "show") (showFunctionOfType env False t)) (Var (idFromNumber i))]
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
showFunctionOfType :: ImportEnvironment -> Bool -> UHA.Type -> Expr
showFunctionOfType env isMainType = sFOT 0
  where
    -- classEnv = classEnvironment env
    tse      = typeSynonyms env
    expandTS :: UHA.Type -> UHA.Type
    expandTS t@(UHA.Type_Constructor _ n) = case M.lookup (toQualTyCon env n) tse of
        Just (i, g) -> makeTypeFromTp (g $ take i (map TCon variableList))
        Nothing -> t
    expandTS t = t
    sFOT nrOfArguments tp  =
        let 
            t = expandTS tp
        in 
      case t of
        UHA.Type_Variable _ n             -> if isMainType then var "$dictPrelude.Show$LvmLang.Int" else Var (idFromName n) 
        -- show Strings not as List of Char but using showString
        UHA.Type_Application _ _ 
                    ( UHA.Type_Constructor _ (UHA.Name_Special    _ _ _ "[]") ) -- !!!Name
                    [ UHA.Type_Constructor _ (UHA.Name_Identifier _ _ _ "Char") ] -- !!!Name
                ->  Ap (var "$dictPrelude.Show$[]") (var "$dictPrelude.Show$LvmLang.Char" )
        UHA.Type_Constructor _ n         -> 
            let conname = getNameName n
            in checkForPrimitiveDict nrOfArguments env conname
        UHA.Type_Application _ _ f xs    -> foldl Ap (sFOT (length xs) f) (map (sFOT 0) xs )
        UHA.Type_Parenthesized _ t'      -> showFunctionOfType env isMainType t'
        _ -> internalError "DerivingShow" "showFunctionOfType" "unsupported type"

-- Some primitive types have funny names and their Show function has a different name
checkForPrimitiveDict :: Int -> ImportEnvironment -> String -> Expr
checkForPrimitiveDict nrOfArguments env name =
    case name of 
        "[]" -> var "$dictPrelude.Show$[]"
        "()" -> var "$dictPrelude.Show$()"
        "->" -> let dict = foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") functions
                    showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore "<<function>>"
                    functions = [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showFunction]
                in Lam (idFromString "d1") $ Lam (idFromString "d2") dict
        ('(':commasAndClose) -> 
            let arity = length commasAndClose in 
                if arity > 10 then
                    internalError "DerivingShow" "checkForPrimitive" "No show functions for tuples with more than 10 elements"
                else
                    var $ "$dictPrelude.Show$(" ++ replicate (arity-1) ',' ++ ")"
        _ -> 
            let 
                classEnv = classEnvironment env
                showInstances :: Instances
                showInstances = snd $ fromJust $ M.lookup "Prelude.Show" classEnv
                qualname = getNameName $ toQualTyCon env (nameFromString name)
                dict = var $ "$dictPrelude.Show$" ++ qualname 
                locIsTCon :: Tp -> String -> Bool
                locIsTCon (TCon n) s = n == s
                locIsTCon (TApp t _) s = locIsTCon t s 
                locIsTCon (TVar _) _ = False
                prd = find (\((Predicate _ t), _)-> locIsTCon t qualname ) showInstances
            in if isJust prd then 
                    dict
                else
                    let locDict = foldr Lam (foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") functions) $ take nrOfArguments [idFromString ("d" ++ show i) | i <- [(0::Integer)..]]
                        showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore ("<<type " ++ qualname ++ ">>")
                        functions = [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showFunction]
                    in locDict
        
idFromNumber :: Int -> Id
idFromNumber i = idFromString ("v$" ++ show i)

{--
nameOfShowFunction :: UHA.Name -> UHA.Name
nameOfShowFunction (UHA.Name_Identifier r m o n) = UHA.Name_Identifier r m o ("show" ++ n) -- !!!Name
nameOfShowFunction _ = internalError "DerivingShow" "nameOfShowFunction" "name of type must be an identifier"
--}

typeOfShowFunction :: UHA.Name -> [String] -> UHA.Names -> TpScheme
typeOfShowFunction name qual names =
    -- Build type from type name and parameters.
    -- e.g. data T a b = ...  ===> (0 -> String) -> (1 -> String) -> (T 0 1 -> String)
    let vars  = map TVar (take (length names) [0..])
        types = vars ++ [foldl TApp (TCon (getNameName (addQualified qual name))) vars]
    in generalizeAll ([] .=>. foldr1 (.->.) (map (.->. stringQualType) types))

