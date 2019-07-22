module Helium.Utils.QualifiedTypes.Constants where

import Top.Types

---------------------------------------------------------
-- Qualified base types which are defined in LvmLang.core
     
{-Since we use qualified types now, all references to intType, charType, stringType, floatType and boolType should be changed to these-}
intQualType, charQualType, stringQualType, floatQualType, boolQualType :: Tp
intQualType    = TCon "LvmLang.Int"
charQualType   = TCon "LvmLang.Char"
stringQualType = TCon "LvmLang.String"
floatQualType  = TCon "LvmLang.Float"
boolQualType   = TCon "LvmLang.Bool"