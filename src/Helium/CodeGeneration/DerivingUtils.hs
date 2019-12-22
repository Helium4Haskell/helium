{-| Module      :  DerivingUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.DerivingUtils where

import qualified Data.Maybe                    as M
import qualified Data.Map.Strict               as M
import qualified Helium.Syntax.UHA_Syntax      as UHA
import           Helium.Syntax.UHA_Utils
import           Helium.CodeGeneration.CoreUtils
import           Helium.ModuleSystem.ImportEnvironment
import           Helium.StaticAnalysis.Miscellaneous.TypeConversion
import           Helium.Utils.QualifiedTypes
import           Lvm.Core.Expr
import qualified Lvm.Core.Type                 as Core
import           Lvm.Common.Id
import           Top.Types
import           Helium.Utils.Utils

nameAndTypes
    :: ImportEnvironment -> String -> M.Map UHA.Name Core.Type -> UHA.Constructor -> (Id, [(Core.Type, Expr)])
nameAndTypes env tpn m c = case c of
    UHA.Constructor_Constructor _ n ts -> (idFromName n, map annotatedTypeToType ts)
    UHA.Constructor_Infix _ t1 n t2    -> (idFromName n, map annotatedTypeToType [t1, t2])
    UHA.Constructor_Record{}           -> error "pattern match failure in CodeGeneration.DerivingEq.nameAndTypes"
  where
    tse = typeSynonyms env
    annotatedTypeToType :: UHA.AnnotatedType -> (Core.Type, Expr)
    annotatedTypeToType (UHA.AnnotatedType_AnnotatedType _ _ t) 
        = (uhaTypetoCoreType m t, eqFunForType tpn tse m (convertTypeToQualified env t))


typeConstructorToTypeConstant :: UHA.Name -> Core.TypeConstant
typeConstructorToTypeConstant un = case un of
    UHA.Name_Identifier _ _ _ n -> Core.TConDataType $ idFromString n
    UHA.Name_Special    _ _ _ n -> case n of
        "->" -> Core.TConFun
        "()" -> Core.TConTuple 0
        '(' : str | dropWhile (== ',') str == ")" -> Core.TConTuple (length str)
        "[]" -> Core.TConDataType $ idFromString n
        _    -> internalError "DerivingUtils" "typeConstructorToTypeConstant" "unsupported name in typeconstant"
    _ -> internalError "DerivingUtils" "typeConstructorToTypeConstant" "unsupported typeconstant"


uhaTypetoCoreType :: M.Map UHA.Name Core.Type -> UHA.Type -> Core.Type
uhaTypetoCoreType m t = case t of
    UHA.Type_Variable    _ n      -> M.fromJust $ M.lookup n m
    UHA.Type_Constructor _ n      -> Core.TCon $ typeConstructorToTypeConstant n
    UHA.Type_Application _ _ f xs -> foldl Core.TAp (uhaTypetoCoreType m f) (map (uhaTypetoCoreType m) xs)
    _                             -> internalError "DerivingUtils" "uhaTypetoCoreType" "unsupported type"

eqFunForType :: String -> TypeSynonymEnvironment -> M.Map UHA.Name Core.Type -> UHA.Type -> Expr
eqFunForType tpn tse m t = case expandTS tse t of
    UHA.Type_Constructor _ n      -> var ("$dict" ++ tpn ++ show n)
    UHA.Type_Application _ _ f xs -> foldl Ap test (map (eqFunForType tpn tse m) xs)
        where test = foldl ApType (eqFunForType tpn tse m f) (map (uhaTypetoCoreType m) xs)
    UHA.Type_Variable _ n -> var (show n)
    -- UHA.Type_Parenthesized _ ty -> eqFunForType m ty
    _                     -> internalError "DerivingUtils" "eqFunForType" "unsupported type"

expandTS :: TypeSynonymEnvironment -> UHA.Type -> UHA.Type
expandTS tse t@(UHA.Type_Constructor _ n) = case M.lookup n tse of
    Just (i, g) -> makeTypeFromTp (g $ take i (map TCon variableList))
    Nothing     -> t
expandTS _ t = t
