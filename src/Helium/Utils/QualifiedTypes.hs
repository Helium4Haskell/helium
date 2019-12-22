module Helium.Utils.QualifiedTypes where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Data.Maybe()
import Helium.ModuleSystem.ImportEnvironment

import Top.Types

import qualified Data.Map as M
---------------------------------------------------------
-- Convert UHA types to qualified

-- Gets a mapping of names to their fully qualified counterparts
getNameEnvironment :: ImportEnvironment -> M.Map Name Name
getNameEnvironment env = M.union (classNameEnvironment env) (fmap snd $ typeConstructors env)

-- The same as getNameEnvironment, except names map to (Int, Name), which is needed
-- for convertMap
getNameEnvironmentInts :: ImportEnvironment -> M.Map Name (Int, Name)
getNameEnvironmentInts env = M.union (M.map ((,) 0) $ classNameEnvironment env) (typeConstructors env)

-- Converts the name of a type constructor to a fully qualified version.
toQualTyCon :: ImportEnvironment -> Name -> Name
toQualTyCon _ n@(Name_Special _ _ _ _) = n
toQualTyCon env n = M.findWithDefault n n (getNameEnvironment env)

-- Converts the name of a class to a fully qualified version.
convertClassNameToQualified :: ImportEnvironment -> Name -> Name
convertClassNameToQualified env n = M.findWithDefault n n (getNameEnvironment env)

-- Converts SimpleType to a fully qualified version.
convertSimpleTypeToQualified :: ImportEnvironment -> SimpleType -> SimpleType
convertSimpleTypeToQualified env (SimpleType_SimpleType range name tv) = SimpleType_SimpleType range (toQualTyCon env name) tv

-- Converts Type to a fully qualified version.
convertTypeToQualified :: ImportEnvironment -> Type -> Type
convertTypeToQualified env = convertType (toQualTyCon env)

-- Converts all names in a type using some function :: Name -> Name.
convertType :: (Name -> Name) -> Type -> Type
convertType f (Type_Application ran pref func arg)
    = Type_Application ran pref (convertType f func) (map (convertType f) arg)
convertType _ tv@(Type_Variable _ _) = tv
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

-- Converts ContextItem to a fully qualified version.
convertContextItemToQualified :: ImportEnvironment-> ContextItem -> ContextItem
convertContextItemToQualified env (ContextItem_ContextItem ran name types)
    = ContextItem_ContextItem ran (convertClassNameToQualified env name) (map (convertTypeToQualified env) types)

---------------------------------------------------------
-- Convert Top types to qualified
convertTpToQualified :: ImportEnvironment -> Tp -> Tp
convertTpToQualified env = convertTp (toQualTyCon env)

convertTpSchemeToQualified :: ImportEnvironment -> TpScheme -> TpScheme
convertTpSchemeToQualified env = convertTpScheme (toQualTyCon env)

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
    Nothing   -> n
    Just newn -> newn

-- Unqualify a name based on an ImportEnvironment.
unQualifyName :: ImportEnvironment -> Name -> Name
unQualifyName = fromQualName . convertMap . getNameEnvironmentInts

-- Unqualify a name based on a ClassNameEnvironment
unQualifyClassName :: ClassNameEnvironment -> Name -> Name
unQualifyClassName = fromQualName . convertMap . M.map ((,) 0)

-- Unqualify Top types
unqualifyTpScheme :: M.Map Name (Int, Name) -> TpScheme -> TpScheme
unqualifyTpScheme env = convertTpScheme (fromQualName $ convertMap env)

unqualifyTp :: M.Map Name (Int, Name) -> Tp -> Tp
unqualifyTp env = convertTp (fromQualName $ convertMap env)

-- Checks whether or not a type is of type (IO a)
isQualIOType :: Tp -> Bool
isQualIOType (TApp (TCon "LvmLang.IO") _) = True 
isQualIOType _ = False