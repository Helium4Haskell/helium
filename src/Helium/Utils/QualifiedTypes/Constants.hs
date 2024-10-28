module Helium.Utils.QualifiedTypes.Constants where

import Helium.Top.Top.Types
--import Lvm.Constants
-- not sure where this file is lvm.constants
---------------------------------------------------------
-- Qualified base types which are defined in LvmLang.core
     
{-Since we use qualified types now, all references to intType, charType, stringType, floatType and boolType should be changed to these-}
intQualType, charQualType, stringQualType, floatQualType, boolQualType :: Tp
intQualType    = TCon "Int"
charQualType   = TCon "Char"
stringQualType = TCon "String"
floatQualType  = TCon "Float"
boolQualType   = TCon "Bool"
