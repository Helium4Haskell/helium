module ImportEnvironment where

import FiniteMap
import UHA_Syntax  ( Names, Name )
import Types
import OperatorTable
import Messages -- instance Show Name

type TypeEnvironment             = FiniteMap Name TpScheme
type ValueConstructorEnvironment = FiniteMap Name TpScheme
type TypeConstructorEnvironment  = FiniteMap Name Int
type TypeSynonymEnvironment      = FiniteMap Name (Int, Tps -> Tp)

type ImportEnvironments = [ImportEnvironment]
data ImportEnvironment  = 
     ImportEnvironment { -- types
                         typeConstructors  :: TypeConstructorEnvironment
                       , typeSynonyms      :: TypeSynonymEnvironment
                       , typeEnvironment   :: TypeEnvironment       
                         -- values
                       , valueConstructors :: ValueConstructorEnvironment
                       , operatorTable     :: OperatorTable
                       }

emptyEnvironment :: ImportEnvironment
emptyEnvironment = ImportEnvironment { typeConstructors  = emptyFM
                                     , typeSynonyms      = emptyFM
                                     , typeEnvironment   = emptyFM
                                     , valueConstructors = emptyFM
                                     , operatorTable     = []
                                     }
                                              
addTypeConstructor :: Name -> Int -> ImportEnvironment -> ImportEnvironment                      
addTypeConstructor name int importenv = 
   importenv {typeConstructors = addToFM (typeConstructors importenv) name int} 

-- add a type synonym also to the type constructor environment   
addTypeSynonym :: Name -> (Int,Tps -> Tp) -> ImportEnvironment -> ImportEnvironment                      
addTypeSynonym name (arity, function) importenv = 
   importenv { typeSynonyms     = addToFM (typeSynonyms importenv)     name (arity, function)
             , typeConstructors = addToFM (typeConstructors importenv) name arity 
             } 

addType :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addType name tpscheme importenv = 
   importenv {typeEnvironment = addToFM (typeEnvironment importenv) name tpscheme} 

addToTypeEnvironment :: TypeEnvironment -> ImportEnvironment -> ImportEnvironment
addToTypeEnvironment new importenv =
   importenv {typeEnvironment = typeEnvironment importenv `plusFM` new} 

   
addValueConstructor :: Name -> TpScheme -> ImportEnvironment -> ImportEnvironment                      
addValueConstructor name tpscheme importenv = 
   importenv {valueConstructors = addToFM (valueConstructors importenv) name tpscheme} 

addOperator :: String -> (Int,Assoc) -> ImportEnvironment -> ImportEnvironment  
addOperator name pair importenv = 
   importenv {operatorTable = (name,pair) : operatorTable importenv } 
   
setValueConstructors :: FiniteMap Name TpScheme -> ImportEnvironment -> ImportEnvironment  
setValueConstructors new importenv = importenv {valueConstructors = new} 

setTypeConstructors :: FiniteMap Name Int -> ImportEnvironment -> ImportEnvironment     
setTypeConstructors new importenv = importenv {typeConstructors = new}

setTypeSynonyms :: FiniteMap Name (Int,Tps -> Tp) -> ImportEnvironment -> ImportEnvironment  
setTypeSynonyms new importenv = importenv {typeSynonyms = new}

setTypeEnvironment :: FiniteMap Name TpScheme -> ImportEnvironment -> ImportEnvironment 
setTypeEnvironment new importenv = importenv {typeEnvironment = new}

setOperatorTable :: OperatorTable -> ImportEnvironment -> ImportEnvironment 
setOperatorTable new importenv = importenv {operatorTable = new}

getOrderedTypeSynonyms :: ImportEnvironment -> OrderedTypeSynonyms
getOrderedTypeSynonyms importEnvironment = 
   let synonyms = let insert name tuple fm = addToFM fm (show name) tuple
                  in foldFM insert emptyFM (typeSynonyms importEnvironment)
       ordering = fst (getTypeSynonymOrdering synonyms)
   in (ordering, synonyms)

combineImportEnvironments :: ImportEnvironment -> ImportEnvironment -> ImportEnvironment
combineImportEnvironments (ImportEnvironment tcs1 tss1 te1 vcs1 ot1) (ImportEnvironment tcs2 tss2 te2 vcs2 ot2) = 
   ImportEnvironment 
      (tcs1 `plusFM` tcs2) 
      (tss1 `plusFM` tss2)
      (te1  `plusFM` te2 )
      (vcs1 `plusFM` vcs2)
      (ot1 ++ ot2)
      
{-
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
      -}
