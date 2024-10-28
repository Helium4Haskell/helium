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
import           Helium.Lvm.Core.Expr
import qualified Helium.Lvm.Core.Type                 as Core
import           Helium.Lvm.Core.Utils
import           Helium.Lvm.Common.Id
import qualified Data.Map                      as M
import           Data.Maybe
import           Data.List
import           Helium.Top.Top.Types


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
    { declName    = name
    , declAccess  = Export name
    , declModule  = Nothing
    , declType    = foldr (\typeArg -> Core.TForall (Core.Quantor $ Just $ getNameName typeArg) Core.KStar)
                          (Core.typeFunction argTypes dictType)
                          names
    , valueValue  = makeShowDictionary
    , declCustoms = [custom "type" ("DictPrelude.Show$ " ++ getNameName qualname)]
                    ++ map (custom "typeVariable" . getNameName)                     names
                    ++ map (\n -> custom "superInstance" ("Prelude.Show-" ++ getNameName n)) names
                    ++ origin
    }
  where
    name = idFromString ("$dictPrelude.Show$" ++ getNameName qualname)
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
        in  foldr (\typeArg -> Forall (Core.Quantor $ Just $ getNameName typeArg) Core.KStar)
                  body
                  names
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

typeOfShowFunction :: UHA.Name -> [String] -> UHA.Names -> TpScheme
typeOfShowFunction name qual names =
    -- Build type from type name and parameters.
    -- e.g. data T a b = ...  ===> (0 -> String) -> (1 -> String) -> (T 0 1 -> String)
    let vars  = map TVar (take (length names) [0..])
        types = vars ++ [foldl TApp (TCon (getNameName (addQualified qual name))) vars]
    in generalizeAll ([] .=>. foldr1 (.->.) (map (.->. stringQualType) types))
