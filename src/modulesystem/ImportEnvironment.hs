module ImportEnvironment where

import EnvironmentSynonyms
import UHA_Syntax  ( Names, Name )
import SortedAssocList
import Types
import Messages () -- for instance

data ImportEnvironment = 
     ImportEnvironment { -- types
                         typeConstructors  :: TypeConstructorEnvironment
                       , typeSynonyms      :: TypeSynonymEnvironment
                       , typeEnvironment   :: TypeEnvironment
                          -- values
                       , valueConstructors :: ConstructorEnvironment
                       }

emptyEnvironment :: ImportEnvironment
emptyEnvironment = ImportEnvironment { typeConstructors  = empty
                                     , typeSynonyms      = []
                                     , typeEnvironment   = empty
                                     , valueConstructors = empty
                                     }
                                              
addTypeConstructor :: Name -> Int -> ImportEnvironment -> ImportEnvironment                      
addTypeConstructor name int importenv = 
   importenv {typeConstructors = add name int (typeConstructors importenv)} 

-- add a type synonym also to the type constructor environment   
addTypeSynonym :: Name -> (Int,Tps -> Tp) -> ImportEnvironment -> ImportEnvironment                      
addTypeSynonym name (arity, function) importenv = 
   importenv { typeSynonyms     = (name, arity, function) : (typeSynonyms importenv)
             , typeConstructors = add name arity (typeConstructors importenv)
             } 

addType :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addType name tpscheme importenv = 
   importenv {typeEnvironment = add name tpscheme (typeEnvironment importenv)} 
   
addValueConstructor :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addValueConstructor name tpscheme importenv = 
   importenv {valueConstructors = add name tpscheme (valueConstructors importenv)} 

combineImportEnvironments :: ImportEnvironment -> ImportEnvironment -> ImportEnvironment
combineImportEnvironments (ImportEnvironment tcs1 tss1 te1 vcs1) (ImportEnvironment tcs2 tss2 te2 vcs2) = 
   ImportEnvironment 
      (tcs1 `combine` tcs2) 
      (tss1 ++ tss2)
      (te1  `combine` te2 )
      (vcs1 `combine` vcs2)

tempConverter :: ConstructorEnvironment -> TypeConstructorEnvironment -> TypeEnvironment -> AssocList Name (Int,Tps -> Tp) -> ImportEnvironment
tempConverter vcs tcs te ass = ImportEnvironment (tcs `combine` mapElt fst ass) [ (n,i,f) | (n,(i,f)) <- toList ass ] te vcs
