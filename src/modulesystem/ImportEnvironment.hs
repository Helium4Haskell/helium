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

temporaryConverter :: ConstructorEnvironment -> TypeConstructorEnvironment -> TypeEnvironment -> AssocList Name (Int,Tps -> Tp) -> ImportEnvironment
temporaryConverter vcs tcs te ass = ImportEnvironment (tcs `combine` mapElt fst ass) [ (n,i,f) | (n,(i,f)) <- toList ass ] te vcs

instance Show ImportEnvironment where
   show (ImportEnvironment tcs tss te vcs) = 
      let tclist = let datas    = map f . filter p . toList $ tcs
                         where p = (`notElem` syns) . fst
                               f (n,i) = "   data "++show n++concatMap (\t -> " " ++ [t])  (take i ['a'..])
                       syns = [ n | (n,i,f) <- tss ]
                       synonyms = map (\(n,i,f) -> "   type "++show n++" "++pretty i f) tss
                         where pretty i f = let list = take i [ TCon [c] | c <- ['a'..]]
                                            in concatMap (\t -> show t ++ " ") list ++ "= " ++ show (f list)
                   in case datas ++ synonyms of 
                         [] -> []
                         xs -> "Type Constructors:" : xs
          vclist = case toList vcs of
                      [] -> []
                      xs -> "Constructors:" : map (\(n,ts) -> "   " ++ show n ++ " :: "++show ts) xs 
          telist = case toList te of
                      [] -> []
                      xs -> "Types:" : map (\(n,ts) -> "   " ++ show n ++ " :: "++show ts) xs 
      in unlines (concat [tclist,vclist,telist])
      
