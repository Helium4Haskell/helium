{-| Module      :  ImportEnvironment
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module ImportEnvironment where

import Data.FiniteMap
import Utils (internalError)
import UHA_Syntax  ( Names, Name )
import UHA_Utils
import Top.Types
import OperatorTable
import Messages -- instance Show Name
import RepairHeuristics (Siblings)
import TS_CoreSyntax
import Data.List (sortBy, partition, groupBy)
import Data.Maybe (catMaybes)

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
                         -- type classes
                       , classEnvironment  :: ClassEnvironment
                         -- other
                       , typingStrategies  :: Core_TypingStrategies 
                       }

emptyEnvironment :: ImportEnvironment
emptyEnvironment = ImportEnvironment 
   { typeConstructors  = emptyFM
   , typeSynonyms      = emptyFM
   , typeEnvironment   = emptyFM
   , valueConstructors = emptyFM
   , operatorTable     = emptyFM
   , classEnvironment  = emptyClassEnvironment
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

setClassEnvironment :: ClassEnvironment -> ImportEnvironment -> ImportEnvironment
setClassEnvironment new importenv = importenv { classEnvironment = new }

addTypingStrategies :: Core_TypingStrategies -> ImportEnvironment -> ImportEnvironment  
addTypingStrategies new importenv = importenv {typingStrategies = new ++ typingStrategies importenv}

removeTypingStrategies :: ImportEnvironment -> ImportEnvironment  
removeTypingStrategies importenv = importenv {typingStrategies = []}

getSiblingGroups :: ImportEnvironment -> [[String]]
getSiblingGroups importenv = 
   [ xs | Siblings xs <- typingStrategies importenv ]

getSiblings :: ImportEnvironment -> Siblings
getSiblings importenv =
   let f s = [ (s, ts) | ts <- findTpScheme (nameFromString s) ]
       findTpScheme n = 
          catMaybes [ lookupFM (valueConstructors importenv) n
                    , lookupFM (typeEnvironment   importenv) n
                    ]
   in map (concatMap f) (getSiblingGroups importenv) 
			
combineImportEnvironments :: ImportEnvironment -> ImportEnvironment -> ImportEnvironment
combineImportEnvironments (ImportEnvironment tcs1 tss1 te1 vcs1 ot1 ce1 xs1) (ImportEnvironment tcs2 tss2 te2 vcs2 ot2 ce2 xs2) = 
   ImportEnvironment 
      (tcs1 `plusFM` tcs2) 
      (tss1 `plusFM` tss2)
      (te1  `plusFM` te2 )
      (vcs1 `plusFM` vcs2)
      (ot1  `plusFM` ot2)
      (plusFM_C combineClassDecls ce1 ce2) 
      (xs1 ++ xs2)

-- Bastiaan:
-- For the moment, this function combines class-environments.
-- The only instances that are added to the standard instances 
-- are the derived Show instances (Show has no superclasses).
-- If other instances are added too, then the class environment
-- should be split into a class declaration environment, and an
-- instance environment.
combineClassDecls :: ([[Char]],[(Predicate,[Predicate])]) -> 
                     ([[Char]],[(Predicate,[Predicate])]) ->
                     ([[Char]],[(Predicate,[Predicate])])
combineClassDecls (super1, inst1) (super2, inst2)
   | super1 == super2 = (super1, inst1 ++ inst2)
   | otherwise        = internalError "ImportEnvironment.hs" "combineClassDecls" "cannot combine class environments"

-- Bastiaan:
-- Create a standard class environment, extended with "Show" instances for the type constructors that 
-- are present in the import environment
createClassEnvironment :: ImportEnvironment -> ClassEnvironment
createClassEnvironment importenv = 
   let donts = [ "IO", "IOMode", "Handle", "->" ] -- not in Show
       stds  = [ "()", "Int", "Float", "Bool", "Char", "[]" ] -- standard in Show
       fm    = delListFromFM (typeConstructors importenv)
             $ keysFM (typeSynonyms importenv) ++ map nameFromString (donts ++ stds)
       extraShowInstances = [ makeShowInstance nrOfArgs (show name) | (name, nrOfArgs) <- fmToList fm ]
   in addToFM_C combineClassDecls standardClasses "Show" ([], extraShowInstances)

makeShowInstance :: Int -> String -> (Predicate, Predicates)
makeShowInstance nrOfArgs tp =
   let tps = take nrOfArgs [ TVar i | i <- [0..] ] 
   in ( Predicate "Show" (foldl TApp (TCon tp) tps)
      , [ Predicate "Show" x | x <- tps ] 
      )

instance Show ImportEnvironment where
   show (ImportEnvironment tcs tss te vcs ot ce _) = 
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
