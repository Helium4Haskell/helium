module TypeClasses where

import TypeBasics
import TypeSubstitution
import TypeUnification
import List  ( nub, sort )
import Maybe ( catMaybes )

----------------------------------------------------------------------  
-- type classes

type ClassPredicates = [ClassPredicate]
type ClassPredicate  = (String,Tps)

type InstanceRules          = (InstanceDeclarations, SuperClassDeclarations)                         
type InstanceDeclarations   = [InstanceDeclaration]
type InstanceDeclaration    = (ClassPredicate, ClassPredicates)
type SuperClassDeclarations = [SuperClassDeclaration]
type SuperClassDeclaration  = (ClassPredicate, ClassPredicates)

-- Uitzonderings-gevallen: tuple -> oneindig, Show String   
-- Show, Eq, Ord, Num
-- Int, Float, Bool, Char   (wat voor String en Show?????)
-- List

-- There are three main ways of reduction:
--    1) Eliminate duplicate constraints
--            {Eq t, Eq t} => {Eq t}
--    2) Use instance declaration
--            {Eq Int} => {}              if instance Eq Int where ...             
--            {Eq [a]} => {Eq a}          if instance Eq a => Eq [a] where ...
--    3) Use class declaration
--            {Ord a,Eq a} => {Ord a}     if class Eq a => Ord a where ...
contextReduction :: InstanceRules -> ClassPredicates -> ClassPredicates 
contextReduction (instanceDeclarations,superClassDeclarations) = 
   useClassDecl . noDuplicates . concatMap useInstanceDecl
   
   where 
         -- 1) Eliminate duplicate constraints
         noDuplicates :: ClassPredicates -> ClassPredicates
         noDuplicates = nub
         
         -- 2) Use instance declaration
         useInstanceDecl :: ClassPredicate -> ClassPredicates
         useInstanceDecl tuple@(className,tps) = 
            let rules = filter ((className==) . fst . fst) instanceDeclarations
                tps'  = map freezeVariablesInType tps
                tryToFit ((_,args),xs) = 
                   case mgu (tupleType tps') (tupleType args) of
                      Left _    -> Nothing
                      Right sub -> Just [ (c,map unfreezeVariablesInType (sub |-> zs)) | (c,zs) <- xs ]
            in case catMaybes (map tryToFit rules) of 
                  result:_ -> concatMap useInstanceDecl result
                  _        -> [tuple]
         
         -- 3) Use class declaration
         useClassDecl :: ClassPredicates -> ClassPredicates
         useClassDecl classPredicates = 
            let op ((className,tps),xs) ps = 
                   let ps' = filter ((className==) . fst) ps
                       toBeRemoved = concatMap tryToFit ps'
                       tryToFit (_,args) = 
                          case mgu (tupleType tps) (tupleType $ map freezeVariablesInType args) of 
                             Left _    -> []
                             Right sub -> [ (c,map unfreezeVariablesInType (sub |-> zs)) | (c,zs) <- xs ]
                   in filter (`notElem` toBeRemoved) ps
            in foldr op classPredicates superClassDeclarations
            
isGround :: ClassPredicate -> Bool
isGround = null . ftv . snd

isTautological :: InstanceRules -> ClassPredicate -> Bool
isTautological instanceRules cpred =
   null (contextReduction instanceRules [cpred])

showClassPredicates :: ClassPredicates -> String
showClassPredicates [] = ""
showClassPredicates xs = 
   let showPredicate (s,tps) = let f tp = parIf (priorityOfType tp < 2) (show tp)
                               in unwords (s : map f tps)
       commaGlue a b = a ++ ", " ++ b
       parIf b s     = if b then "("++s++")" else s
   in (++" => ") . parIf (length xs > 1) . foldr1 commaGlue . sort . map showPredicate $ xs
   
-------------------------------------------------------
-- standard type classes

standardInstanceRules :: InstanceRules
standardInstanceRules = (standardInstanceDeclarations, standardSuperClassDeclarations)

standardInstanceDeclarations :: InstanceDeclarations
standardInstanceDeclarations = 
   [ ( (className, [groundType]) , [] )
   | className  <- ["Show", "Eq", "Ord"]
   , groundType <- [intType, floatType, boolType, charType]
   ] ++
   [ ( (className, [listType (TVar 0)]) , [(className, [(TVar 0)])] )
   | className  <- ["Show", "Eq", "Ord"]
   ]

standardSuperClassDeclarations :: SuperClassDeclarations
standardSuperClassDeclarations = 
   [ (("Ord", [TVar 0]), [("Eq", [TVar 0])]) ]
   
{- test functions      


q = {- inst' 1000 $ -} gen' [] --[1] 
  {- contextReduction -} ([("Eq",[tupleType [intType .->. intType,listType (listType charType),TVar 0 ]])]) (TVar 0 .->. TVar 1)

                    
z = contextReduction standardInstanceRules 
--        (Context [("Eq",[listType (TVar 30)])])
       ([ (c,[listType $ TVar 30]) | c <- ["Ord","Eq","Ord","Eq"] ] )
--     (Context [("Eq",[tupleType [intType .->. intType,listType (listType charType),TVar 30 ]])]) 
--(TVar 0 .->. TVar 1)

-- the easy way: just expand the types in the context
contextReductionWithTypeSynonyms :: OrderedTypeSynonyms -> InstanceRules -> Context -> Context                      
contextReductionWithTypeSynonyms orderedTypeSynonyms instanceRules (Context preds) =
   let newContext = Context [ (c,map (expandType orderedTypeSynonyms) tps) | (c,tps) <- preds]
   in contextReduction instanceRules newContext      

-}
