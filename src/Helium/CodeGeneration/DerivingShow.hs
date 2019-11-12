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
import           Lvm.Core.Expr
import qualified Lvm.Core.Type                 as Core
import           Lvm.Core.Utils
import           Lvm.Common.Id
import qualified Data.Map                      as M

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
dataDictionary :: TypeSynonymEnvironment -> UHA.Declaration -> CoreDecl
dataDictionary tse decla@(UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ name names) _ _) = DeclValue
    { declName    = idFromString ("$dictShow$" ++ getNameName name)
    , declAccess  = public
    , declType    = foldr (\(typeArg, idx) -> Core.TForall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
                          (Core.typeFunction argTypes dictType)
                        $ zip names [1 ..]
    , valueValue  = makeShowDictionary
    , declCustoms = [custom "type" ("Dict$Show " ++ getNameName name)]
                    ++ map (custom "typeVariable" . getNameName)                     names
                    ++ map (\n -> custom "superInstance" ("Show-" ++ getNameName n)) names
    }
  where
    argTypes :: [Core.Type]
    argTypes = zipWith (\_ idx -> typeDictFor $ Core.TVar idx) names [1 ..]
    dictType = typeDictFor dataType
    dataType = Core.typeApplyList (Core.TCon $ Core.typeConFromString $ getNameName name)
        $ zipWith (\_ idx -> Core.TVar idx) names [1 ..]
    makeShowDictionary :: Expr
    makeShowDictionary =
        let showBody = dataShowFunction dictType dataType tse decla
            ids      = zipWith (\n idx -> let arg = idFromName n in Variable arg $ typeDictFor $ Core.TVar idx)
                               names
                               [1 ..]
            fields =
                    [ ApType (Var $ idFromString "default$Show$showsPrec") dataType
                    , ApType (Var $ idFromString "default$Show$showList")  dataType
                    , showBody
                    ]
            body = foldr (Lam False) (foldl Ap (ApType (Con $ ConId $ idFromString "Dict$Show") dataType) fields) ids
        in  foldr (\(typeArg, idx) -> Forall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
                  body
                  (zip names [1 ..])
dataDictionary _ _ = error "pattern match failure in CodeGeneration.Deriving.dataDictionary"

-- Show function for a data type declaration
dataShowFunction :: Core.Type -> Core.Type -> TypeSynonymEnvironment -> UHA.Declaration -> Expr
dataShowFunction dictType dataType tse (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ _ names) constructors _)
    = foldr
        (Lam False)
        (Let (Strict (Bind (Variable valueId dataType) (Var valueId)))
             (Match valueId (map (makeAlt tse typeArgs) constructors))
        )
        [Variable (idFromString "$instanceDictShow") dictType, Variable valueId dataType]
  where
    valueId  = idFromString "value$"
    typeArgs = M.fromList (zipWith (\name idx -> (name, Core.TVar idx)) names [1 ..])
dataShowFunction _ _ _ _ = error "pattern match failure in CodeGeneration.Deriving.dataShowFunction"

-- Convert a data type constructor to a Core alternative
makeAlt :: TypeSynonymEnvironment -> M.Map UHA.Name Core.Type -> UHA.Constructor -> Alt
makeAlt tse m c = Alt (constructorToPat ident types) (showConstructor ident types)
  where
    (ident, types) = nameAndTypes "Show$" tse m c
    constructorToPat ident' ts = PatCon (ConId ident') (M.elems m) [ idFromNumber i | i <- [1 .. length ts] ]

-- Show expression for one constructor
showConstructor :: Id -> [(Core.Type, Expr)] -> Expr
showConstructor c ts
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
