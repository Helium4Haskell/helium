module ImportEnvironment where

import Data.FiniteMap
import UHA_Syntax  ( Names, Name )
import UHA_Utils
import Top.Types
import OperatorTable
import Messages -- instance Show Name
import TS_CoreSyntax
import List (sortBy, partition, groupBy)

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
                         -- other
                       , typingStrategies  :: Core_TypingStrategies 
                       }

emptyEnvironment :: ImportEnvironment
emptyEnvironment = ImportEnvironment { typeConstructors  = emptyFM
                                     , typeSynonyms      = emptyFM
                                     , typeEnvironment   = emptyFM
                                     , valueConstructors = emptyFM
                                     , operatorTable     = emptyFM
                                     , typingStrategies  = [] 
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

addOperator :: Name -> (Int,Assoc) -> ImportEnvironment -> ImportEnvironment  
addOperator name pair importenv = 
   importenv {operatorTable = addToFM (operatorTable importenv) name pair  } 
   
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

addTypingStrategies :: Core_TypingStrategies -> ImportEnvironment -> ImportEnvironment  
addTypingStrategies new importenv = importenv {typingStrategies = new ++ typingStrategies importenv}

removeTypingStrategies :: ImportEnvironment -> ImportEnvironment  
removeTypingStrategies importenv = importenv {typingStrategies = []}

getSiblings :: ImportEnvironment -> [[String]]
getSiblings importenv = 
   [ xs | Siblings xs <- typingStrategies importenv ]

combineImportEnvironments :: ImportEnvironment -> ImportEnvironment -> ImportEnvironment
combineImportEnvironments (ImportEnvironment tcs1 tss1 te1 vcs1 ot1 xs1) (ImportEnvironment tcs2 tss2 te2 vcs2 ot2 xs2) = 
   ImportEnvironment 
      (tcs1 `plusFM` tcs2) 
      (tss1 `plusFM` tss2)
      (te1  `plusFM` te2 )
      (vcs1 `plusFM` vcs2)
      (ot1  `plusFM` ot2)
      (xs1 ++ xs2)
      
instance Show ImportEnvironment where
   show (ImportEnvironment tcs tss te vcs ot _) = 
      unlines (concat [ fixities
                      , datatypes
                      , typesynonyms
                      , valueConstructors
                      , functions
                      ])
    where
    
       fixities =    
          let sorted  = let cmp (name, (prio, assoc)) = (10 - prio, assoc, not (isOperatorName name), name)
                        in sortBy (\x y -> cmp x `compare` cmp y) (fmToList ot)
              grouped = groupBy (\x y -> snd x == snd y) sorted
              list = let f ((name, (prio, assoc)) : rest) =
                            let names  = name : map fst rest 
                                prefix = (case assoc of
                                             AssocRight -> "infixr"
                                             AssocLeft  -> "infixl"
                                             AssocNone  -> "infix "
                                         )++" "++ show prio ++ " "
                            in prefix ++ foldr1 (\x y -> x++", "++y) (map showNameAsOperator names)
                     in map f grouped          
          in showWithTitle "Fixity declarations" list
       
       datatypes = 
          let allDatas = filter ((`notElem` keysFM tss). fst) (fmToList tcs)
              (xs, ys) = partition (isIdentifierName . fst) allDatas
              list     = map f (ys++xs)
              f (n,i)  = unwords ("data" : (showNameAsVariable n) : take i variableList)
          in showWithTitle "Data types" list
       
       typesynonyms =
          let (xs, ys)    = partition (isIdentifierName . fst) (fmToList tss)
              list        = map f (ys++xs)
              f (n,(i,g)) = let tcons =  take i (map TCon variableList)
                            in unwords ("type" : showNameAsVariable n : map show tcons ++ ["=", show (g tcons)])               
          in showWithTitle "Type synonyms" list  
                 
       valueConstructors =
          let (xs, ys) = partition (isIdentifierName . fst) (fmToList vcs)
              list     = map (\(n,t) -> showNameAsVariable n ++ " :: "++show t) (ys++xs)         
          in showWithTitle "Value constructors" list    
                 
       functions = 
          let (xs, ys) = partition (isIdentifierName . fst) (fmToList te)
              list     = map (\(n,t) -> showNameAsVariable n ++ " :: "++show t) (ys++xs)
          in showWithTitle "Functions" list                  
       
       showWithTitle title xs
          | null xs   = []
          | otherwise = (title++":") : map ("   "++) xs
       
instance Ord Assoc where
  x <= y = let f AssocLeft  = 0
               f AssocRight = 1
               f AssocNone  = 2
           in f x <= f y
