module Helium.Utils.QualifiedTypes where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils

import Top.Types


import qualified Data.Map as M
---------------------------------------------------------
-- Convert UHA types to qualified
toQualTyCon :: M.Map Name (Int, Name) -> Name -> Name
toQualTyCon _ n@(Name_Special _ _ _ _) = n
toQualTyCon env n = case M.lookup n env of
    Nothing         -> n
    Just (_, qualn) -> qualn

convertSimpleTypeToQualified :: M.Map Name (Int, Name) -> SimpleType -> SimpleType
convertSimpleTypeToQualified env (SimpleType_SimpleType range name tv) = SimpleType_SimpleType range (toQualTyCon env name) tv

convertTypeToQualified :: M.Map Name (Int, Name) -> Type -> Type
convertTypeToQualified env = convertType (toQualTyCon env)

convertType :: (Name -> Name) -> Type -> Type
convertType f (Type_Application ran pref func arg)
    = Type_Application ran pref (convertType f func) (map (convertType f) arg)
convertType f tv@(Type_Variable _ _) = tv
convertType f (Type_Qualified ran con ty)
    = Type_Qualified ran con (convertType f ty)
convertType f (Type_Forall ran tv ty )
    = Type_Forall ran tv (convertType f ty)
convertType f (Type_Exists ran tv ty )
    = Type_Exists ran tv (convertType f ty) 
convertType f (Type_Parenthesized ran ty)
    = Type_Parenthesized ran (convertType f ty)
convertType f (Type_Constructor ran na) = 
    Type_Constructor ran (f na)

convertContextItemToQualified :: M.Map Name (Int, Name) -> ContextItem -> ContextItem
convertContextItemToQualified env (ContextItem_ContextItem ran name types)
    = ContextItem_ContextItem ran name (map (convertTypeToQualified env) types)

---------------------------------------------------------
-- Convert Top types to qualified
convertTpToQualified :: M.Map Name (Int, Name) -> Tp -> Tp
convertTpToQualified env = convertTp (toQualTyCon env)

convertTpSchemeToQualified :: M.Map Name (Int, Name) -> TpScheme -> TpScheme
convertTpSchemeToQualified env = convertTpScheme (toQualTyCon env)

convertTp :: (Name -> Name) -> Tp -> Tp
convertTp _ t@(TVar _) = t
convertTp f (TCon str) = TCon . getNameName . f . nameFromString $ str
convertTp f (TApp t1 t2) = TApp (convertTp f t1) (convertTp f t2)

convertTpScheme :: (Name -> Name) -> TpScheme -> TpScheme
convertTpScheme f (Quantification (xs, qm, (Qualification (pre, ty)))) = Quantification (xs, qm, (Qualification (pre,convertTp f ty)))

---------------------------------------------------------
-- Unqualify types
convertMap :: M.Map Name (Int, Name) -> M.Map Name Name
convertMap env = 
    let newlist = [(qualn, key) | (key, (_, qualn)) <- M.toList env]
        newenv  = M.fromListWith combineNames newlist
        --Always take the first, except when the second is unqualified
        combineNames n1 n2 | isQualified n2 = n1
                           | otherwise      = n2
    in newenv

fromQualName :: M.Map Name Name -> Name -> Name
fromQualName _ n@(Name_Special _ _ _ _) = n
fromQualName env n = case M.lookup n env of
    Nothing         -> n
    Just newn -> newn

unqualifyTpScheme :: M.Map Name (Int, Name) -> TpScheme -> TpScheme
unqualifyTpScheme env = convertTpScheme (fromQualName $ convertMap env)

unqualifyTp :: M.Map Name (Int, Name) -> Tp -> Tp
unqualifyTp env = convertTp (fromQualName $ convertMap env)
---------------------------------------------------------
-- Qualified base types which are defined in LvmLang.core
     
{-Since we use qualified types now, all references to intType, charType, stringType, floatType and boolType should be changed to these-}
intQualType, charQualType, stringQualType, floatQualType, boolQualType :: Tp
intQualType    = TCon "LvmLang.Int"
charQualType   = TCon "LvmLang.Char"
stringQualType = TCon "LvmLang.String"
floatQualType  = TCon "LvmLang.Float"
boolQualType   = TCon "LvmLang.Bool"

isQualIOType :: Tp -> Bool
isQualIOType (TApp (TCon "LvmLang.IO") _) = True 
isQualIOType _ = False



