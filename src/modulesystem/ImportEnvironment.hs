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
                                     , typeSynonyms      = empty
                                     , typeEnvironment   = empty
                                     , valueConstructors = empty
                                     }
                                              
addTypeConstructor :: Name -> Int -> ImportEnvironment -> ImportEnvironment                      
addTypeConstructor name int importenv = 
   importenv {typeConstructors = add name int (typeConstructors importenv)} 

-- add a type synonym also to the type constructor environment   
addTypeSynonym :: Name -> (Int,Tps -> Tp) -> ImportEnvironment -> ImportEnvironment                      
addTypeSynonym name tuple importenv = 
   importenv { typeSynonyms     = add name tuple (typeSynonyms importenv)
             , typeConstructors = add name (fst tuple) (typeConstructors importenv)
             } 

addType :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addType name tpscheme importenv = 
   importenv {typeEnvironment = add name tpscheme (typeEnvironment importenv)} 
   
addValueConstructor :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addValueConstructor name tpscheme importenv = 
   importenv {valueConstructors = add name tpscheme (valueConstructors importenv)} 
