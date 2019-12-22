{-| Module      :  DerivingShow
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.DerivingShow
    ( dataDictionary
    )
where

import qualified Helium.Syntax.UHA_Syntax      as UHA
import           Helium.Syntax.UHA_Utils
import           Helium.CodeGeneration.CoreUtils
import           Helium.CodeGeneration.DerivingUtils
import           Helium.ModuleSystem.ImportEnvironment
import           Helium.StaticAnalysis.Miscellaneous.TypeConversion
import           Helium.Utils.QualifiedTypes
import           Helium.Utils.Utils
import           Helium.Utils.QualifiedTypes.Constants
import           Lvm.Core.Expr
import qualified Lvm.Core.Type                 as Core
import           Lvm.Core.Utils
import           Lvm.Common.Id
import qualified Data.Map                      as M
import           Data.Maybe
import           Data.List
import           Top.Types


typeDictShow :: Core.Type
typeDictShow = Core.TCon $ Core.TConTypeClassDictionary $ idFromString "Show"

typeDictFor :: Core.Type -> Core.Type
typeDictFor = Core.TAp typeDictShow

typeList :: Core.Type
typeList = Core.TCon $ Core.TConDataType $ idFromString "[]"

typeString :: Core.Type
typeString = Core.TAp typeList typeChar

typeChar :: Core.Type
typeChar = Core.TCon $ Core.TConDataType $ idFromString "Char"

-- Show Dictionary for a data type declaration
dataDictionary :: ImportEnvironment -> UHA.Declaration -> [Custom] -> UHA.Name -> CoreDecl
dataDictionary env decla@(UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ names) _ _) origin qualname = DeclValue
    { declName    = idFromString ("$dictPrelude.Show$" ++ getNameName qualname)
    , declAccess  = public
    , declType    = foldr (\(typeArg, idx) -> Core.TForall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
                          (Core.typeFunction argTypes dictType)
                        $ zip names [1 ..]
    , valueValue  = makeShowDictionary
    , declCustoms = [custom "type" ("DictPrelude.Show$ " ++ getNameName qualname)]
                    ++ map (custom "typeVariable" . getNameName)                     names
                    ++ map (\n -> custom "superInstance" ("Prelude.Show-" ++ getNameName n)) names
                    ++ origin
    }
  where
    tse = typeSynonyms env
    argTypes :: [Core.Type]
    argTypes = zipWith (\_ idx -> typeDictFor $ Core.TVar idx) names [1 ..]
    dictType = typeDictFor dataType
    dataType = Core.typeApplyList (Core.TCon $ Core.typeConFromString $ getNameName qualname)
        $ zipWith (\_ idx -> Core.TVar idx) names [1 ..]
    makeShowDictionary :: Expr
    makeShowDictionary =
        let showBody = dataShowFunction env dictType dataType decla
            ids      = zipWith (\n idx -> let arg = idFromName n in Variable arg $ typeDictFor $ Core.TVar idx)
                               names
                               [1 ..]
            fields =
                    [ ApType (Var $ idFromString "default$Prelude.Show$showsPrec") dataType
                    , ApType (Var $ idFromString "default$Prelude.Show$showList")  dataType
                    , showBody
                    ]
            body = foldr (Lam False) (foldl Ap (ApType (Con $ ConId $ idFromString "DictPrelude.Show") dataType) fields) ids
        in  foldr (\(typeArg, idx) -> Forall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
                  body
                  (zip names [1 ..])
dataDictionary _ _ _ _ = error "pattern match failure in CodeGeneration.Deriving.dataDictionary"

-- Show function for a data type declaration
dataShowFunction :: ImportEnvironment -> Core.Type -> Core.Type -> UHA.Declaration -> Expr
dataShowFunction env dictType dataType (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ names) constructors _)
    = foldr
        (Lam False)
        (Let (Strict (Bind (Variable valueId dataType) (Var valueId)))
             (Match valueId (map (makeAlt env typeArgs) constructors))
        )
        [Variable (idFromString "$instanceDictPrelude.Show") dictType, Variable valueId dataType]
  where
    tse = typeSynonyms env
    valueId  = idFromString "value$"
    typeArgs = M.fromList (zipWith (\name idx -> (name, Core.TVar idx)) names [1 ..])
dataShowFunction _ _ _ _ = error "pattern match failure in CodeGeneration.Deriving.dataShowFunction"

-- -- Show Dictionary for a data type declaration
-- dataDictionary :: ImportEnvironment -> UHA.Declaration -> [String] -> [Custom] -> UHA.Name -> CoreDecl
-- dataDictionary env declp@(UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ names) _ _) qual origin qualname =
--     DeclValue
--     { declName    = idFromString ("$dictPrelude.Show$" ++ getNameName qualname)
--     , declAccess  = public
--     , valueEnc    = Nothing
--     , valueValue  = makeShowDictionary (length names)
--     , declCustoms = [ custom "type" ("DictPrelude.Show$" ++ getNameName qualname)]
--                 ++ map (custom "typeVariable" . getNameName) names
--                 ++ map (\n -> custom "superInstance" ("Prelude.Show-" ++ getNameName n)) names
--                 ++ origin
--     }
--   where
--     makeShowDictionary :: Int -> Expr
--     makeShowDictionary _ =
--        let
--            showBody = dataShowFunction env declp qual origin
--            ids  = map idFromName names
--            list = map idFromString ["showsPred", "showList", "showDef"]
--            declarations = zipWith Bind list [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showBody]
--            body = Let (Rec declarations) (foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") $ map Var list)
--        in foldr Lam body ids
-- dataDictionary _ _ _ _ _ = error "not supported"

-- Convert a data type constructor to a Core alternative
makeAlt :: ImportEnvironment -> M.Map UHA.Name Core.Type -> UHA.Constructor -> Alt
makeAlt env m c = Alt (constructorToPat ident types) (showConstructor env ident types)
  where
    tse = typeSynonyms env
    (ident, types) = nameAndTypes env "Prelude.Show$" m c
    constructorToPat ident' ts = PatCon (ConId ident') (M.elems m) [ idFromNumber i | i <- [1 .. length ts] ]

-- Show expression for one constructor
showConstructor :: ImportEnvironment -> Id -> [(Core.Type, Expr)] -> Expr
showConstructor env c ts
    | -- name of constructor and paramater types
      isConOp && length ts == 2 = Ap primconcat $ coreList
        typeString
        [ stringToCore "("
        , Ap (cshow $ ts !! 0) (Var (idFromNumber 1))
        , stringToCore name
        , Ap (cshow $ ts !! 1) (Var (idFromNumber 2))
        , stringToCore ")"
        ]
    | otherwise = Ap primconcat $ coreList
        typeString
        (  (if null ts then [] else [stringToCore "("])
        ++ (if isConOp then parens else id) [stringToCore name]
        ++ concat [ [stringToCore " ", Ap (cshow te) (Var (idFromNumber i))] | (te, i) <- zip ts [1 ..] ]
        ++ (if null ts then [] else [stringToCore ")"])
        )
  where
    cshow (t, e) = Ap (ApType (var "show") t) e
    primconcat = ApType (Var (idFromString "$primConcat")) typeChar
    name       = stringFromId c
    isConOp    = head name == ':'
    parens s = [stringToCore "("] ++ s ++ [stringToCore ")"]

idFromNumber :: Int -> Id
idFromNumber i = idFromString ("v$" ++ show i)

-- showConstructor :: ImportEnvironment -> Id -> [UHA.Type] -> Expr
-- showConstructor env c ts -- name of constructor and paramater types
--     | isConOp && length ts == 2 =
--         Ap (Var (idFromString "$primConcat")) $ coreList
--             [   stringToCore "("
--             ,   Ap (Ap (var "show") (showFunctionOfType env False (ts!!0))) (Var (idFromNumber 1))
--             ,   stringToCore name
--             ,   Ap (Ap (var "show") (showFunctionOfType env False (ts!!1))) (Var (idFromNumber 2))
--             ,   stringToCore ")"
--             ]
--     | otherwise =
--         Ap (Var (idFromString "$primConcat")) $ coreList
--             (  (if null ts then [] else [stringToCore "("])
--             ++ (if isConOp then parens else id) [stringToCore name]
--             ++ concat
--                    [ [stringToCore " ", Ap (Ap (var "show") (showFunctionOfType env False t)) (Var (idFromNumber i))]
--                    | (t, i) <- zip ts [1..]
--                    ]
--             ++ (if null ts then [] else [stringToCore ")"])
--             )
--   where
--     name = stringFromId c
--     isConOp = head name == ':'
--     parens s = [ stringToCore "(" ] ++ s ++ [ stringToCore ")" ]

-- What show function to call for a specific type. Returns a Core expression
-- If this function is called for the main function, type variables are printed
-- using showPolymorphic. Otherwise, a show function for the type variable
-- should be available
-- showFunctionOfType :: ImportEnvironment -> Bool -> UHA.Type -> Expr
-- showFunctionOfType env isMainType = sFOT 0
--   where
--     -- classEnv = classEnvironment env
--     tse      = typeSynonyms env
--     expandTS :: UHA.Type -> UHA.Type
--     expandTS t@(UHA.Type_Constructor _ n) = case M.lookup (toQualTyCon env n) tse of
--         Just (i, g) -> makeTypeFromTp (g $ take i (map TCon variableList))
--         Nothing -> t
--     expandTS t = t
--     sFOT nrOfArguments tp  =
--         let
--             t = expandTS tp
--         in
--       case t of
--         UHA.Type_Variable _ n             -> if isMainType then var "$dictPrelude.Show$LvmLang.Int" else Var (idFromName n)
--         -- show Strings not as List of Char but using showString
--         UHA.Type_Application _ _
--                     ( UHA.Type_Constructor _ (UHA.Name_Special    _ _ _ "[]") ) -- !!!Name
--                     [ UHA.Type_Constructor _ (UHA.Name_Identifier _ _ _ "Char") ] -- !!!Name
--                 ->  Ap (var "$dictPrelude.Show$[]") (var "$dictPrelude.Show$LvmLang.Char" )
--         UHA.Type_Constructor _ n         ->
--             let conname = getNameName n
--             in checkForPrimitiveDict nrOfArguments env conname
--         UHA.Type_Application _ _ f xs    -> foldl Ap (sFOT (length xs) f) (map (sFOT 0) xs )
--         UHA.Type_Parenthesized _ t'      -> showFunctionOfType env isMainType t'
--         _ -> internalError "DerivingShow" "showFunctionOfType" "unsupported type"

-- -- Some primitive types have funny names and their Show function has a different name
-- checkForPrimitiveDict :: Int -> ImportEnvironment -> String -> Expr
-- checkForPrimitiveDict nrOfArguments env name =
--     case name of
--         "[]" -> var "$dictPrelude.Show$[]"
--         "()" -> var "$dictPrelude.Show$()"
--         "->" -> let dict = foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") functions
--                     showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore "<<function>>"
--                     functions = [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showFunction]
--                 in Lam (idFromString "d1") $ Lam (idFromString "d2") dict
--         ('(':commasAndClose) ->
--             let arity = length commasAndClose in
--                 if arity > 10 then
--                     internalError "DerivingShow" "checkForPrimitive" "No show functions for tuples with more than 10 elements"
--                 else
--                     var $ "$dictPrelude.Show$(" ++ replicate (arity-1) ',' ++ ")"
--         _ ->
--             let
--                 classEnv = classEnvironment env
--                 showInstances :: Instances
--                 showInstances = snd $ fromJust $ M.lookup "Prelude.Show" classEnv
--                 qualname = getNameName $ toQualTyCon env (nameFromString name)
--                 dict = var $ "$dictPrelude.Show$" ++ qualname
--                 locIsTCon :: Tp -> String -> Bool
--                 locIsTCon (TCon n) s = n == s
--                 locIsTCon (TApp t _) s = locIsTCon t s
--                 locIsTCon (TVar _) _ = False
--                 prd = find (\((Predicate _ t), _)-> locIsTCon t qualname ) showInstances
--             in if isJust prd then
--                     dict
--                 else
--                     let locDict = foldr Lam (foldl Ap (Con $ ConId $ idFromString "DictPrelude.Show") functions) $ take nrOfArguments [idFromString ("d" ++ show i) | i <- [(0::Integer)..]]
--                         showFunction = Lam (idFromString "d") $ Lam (idFromString "p") $ stringToCore ("<<type " ++ qualname ++ ">>")
--                         functions = [Var $ idFromString "default$Prelude.Show$showsPrec", Var $ idFromString "default$Prelude.Show$showList", showFunction]
--                     in locDict

typeOfShowFunction :: UHA.Name -> [String] -> UHA.Names -> TpScheme
typeOfShowFunction name qual names =
    -- Build type from type name and parameters.
    -- e.g. data T a b = ...  ===> (0 -> String) -> (1 -> String) -> (T 0 1 -> String)
    let vars  = map TVar (take (length names) [0..])
        types = vars ++ [foldl TApp (TCon (getNameName (addQualified qual name))) vars]
    in generalizeAll ([] .=>. foldr1 (.->.) (map (.->. stringQualType) types))
