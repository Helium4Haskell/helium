module TypeDebugInfoWriter (writeDebugInfoTree) where

import Top.Types
import Top.ComposedSolvers.Tree
import Top.ComposedSolvers.TreeWalk
import Top.Constraints.ExtraConstraints
import TypeConstraints
import TypeErrors
import ConstraintInfo
import DoublyLinkedTree
import TypeDebugInfo
import UHA_Syntax
import UHA_Source
import Messages
import HeliumMessages
import OneLiner
import Utils (internalError)
import Data.FiniteMap

writeDebugInfoTree :: Substitution s => s -> FiniteMap Int (Scheme Predicates) 
                    -> TypeErrors
                    -> Tree (TypeConstraint ConstraintInfo) 
                    -> DoublyLinkedTree LocalInfo -> String -> String -> IO ()
writeDebugInfoTree substitution sigmaMap typeErrors ctree tree fn1 fn2 = 
   let defs    = getDefinitionRanges tree
       errs    = let f x = (map convertRange (getRanges x), showMessage x)
                 in map f (substitution |-> sortMessages typeErrors)
       entries = convertInfoTree substitution sigmaMap expls tree
       cs      = flattenTree topDownTreeWalk ctree
       expls   = [ (tp, sigma) | TC2 (Instantiate tp sigma _) <- cs ]
   in writeTypeDebugInfo fn1 $
      TypeDebugInfo { tiFileName    = show fn2
                    , tiDefinitions = defs
                    , tiTypeErrors  = errs
                    , tiEntries     = entries
                    }

getDefinitionRanges :: DoublyLinkedTree LocalInfo -> [DefinitionInfo]
getDefinitionRanges tree = 
   f (attribute tree) ++ concatMap getDefinitionRanges (children tree)
 where
   f :: LocalInfo -> [DefinitionInfo]
   f local =
      case self local of 
         UHA_Decl (Declaration_FunctionBindings range (FunctionBinding_FunctionBinding _ lhs _:_)) -> 
            [([show (nameOfLHS lhs)], convertRange range)]
         UHA_Decl (Declaration_PatternBinding range pat _) ->
            [(map show (namesOfPat pat), convertRange range)]
         _ -> []
         
   nameOfLHS :: LeftHandSide -> Name
   nameOfLHS lhs = 
      case lhs of 
         LeftHandSide_Function _ name _     -> name 
         LeftHandSide_Infix _ _ name _      -> name 
         LeftHandSide_Parenthesized _ lhs _ -> nameOfLHS lhs
   
   namesOfPat :: Pattern -> Names
   namesOfPat pat = 
      case pat of 
         Pattern_As _ n p -> n : namesOfPat p 
         Pattern_Constructor _ n ps -> n : concatMap namesOfPat ps
         Pattern_InfixConstructor _ p1 n p2 -> namesOfPat p1 ++ [n] ++ namesOfPat p2
         Pattern_List _ ps -> concatMap namesOfPat ps
         Pattern_Parenthesized _ p -> namesOfPat p
         Pattern_Tuple _ ps -> concatMap namesOfPat ps
         Pattern_Variable _ n -> [n]
         _ -> []

convertInfoTree :: Substitution s => s -> FiniteMap Int (Scheme Predicates) -> [(Tp,Sigma Predicates)] 
                -> DoublyLinkedTree LocalInfo -> FiniteMap EntryId Entry
convertInfoTree substitution sigmaMap expls = 
   listToFM . snd . rec Nothing (0::Int) 
 where
   rec parent unique tree
      | skipSource $ self $ attribute tree =
           let (unique', ts) = foldr (op parent) (unique, []) (children tree)
               (lists, cs) = unzip ts
           in (unique', concat lists)
      | otherwise = 
           let (unique', ts) = foldr (op (Just unique)) (unique+1, []) (children tree)
               (lists, cs) = unzip ts
               new = convertLocal parent unique cs (attribute tree)
           in (unique', new : concat lists)
      
   op parent sub (i, xs) =
      let (i', ys) = rec parent i sub
      in (i', (ys, i):xs)
      
   convertLocal :: Maybe Int -> Int -> [Int] -> LocalInfo -> (EntryId, Entry)
   convertLocal parent i subs local =
      let uha = self local
          maybeOriginal = 
             case [ sigma | (tp, sigma) <- expls, Just tp == assignedType local ] of 
                [sigma] -> 
                   let err = internalError "ConstraintInfo.hs" "convertLocal" "cannot find type scheme in type scheme map"
                       scheme = case sigma of 
                                   SigmaVar i    -> lookupWithDefaultFM sigmaMap err i
                                   SigmaScheme x -> x
                   in Just (substitution |-> scheme)        
                _ -> Nothing
          entry = Entry { getRange       = convertRange (rangeOfSource uha)
                        , getDescription = getDescr uha
                        , getNonTerminal = descriptionOfSource uha
                        , getPretty      = showOneLine 80 (oneLinerSource uha)
                        , getMType       = substitution |-> assignedType local
                        , getMOriginal   = maybeOriginal
                        , getMono        = ftv (substitution |-> monos local)
                        , getParent      = fmap makeEntryId parent
                        , getSubTerms    = map makeEntryId subs
                        }
      in (makeEntryId i, entry)

convertRange :: Range -> (Pos, Pos)
convertRange (Range_Range p1 p2) = 
   let f (Position_Position _ x y) = (x, y)
       f Position_Unknown          = (0, 0)
   in (f p1, f p2)

skipSource :: UHA_Source -> Bool
skipSource uha = 
   case uha of
      UHA_Decls _ -> True
      UHA_Decl (Declaration_PatternBinding _ _ _) -> False
      UHA_Decl (Declaration_FunctionBindings _ _) -> False
      UHA_Decl _ -> True      
      _ -> False
 
getDescr :: UHA_Source -> String
getDescr uha =
   case uha of
      UHA_Expr e ->
         case e of
            Expression_Case _ _ _ -> "case expression"
            Expression_Comprehension _ _ _ -> "list comprehension"
            Expression_Constructor _ _-> "constructor"
            Expression_Do _ _ -> "do expression"
            Expression_Enum _ _ _ _ -> "list enumeration"
            Expression_If _ _ _ _ -> "conditional expression"
            Expression_InfixApplication _ _ _ _ -> "infix application"
            Expression_Lambda _ _ _ -> "lambda abstraction"
            Expression_Let _ _ _ -> "let expression"
            Expression_List _ _ -> "list expression"
            Expression_Literal _ _ -> "literal constant"
            Expression_Negate _ _ -> "negation"
            Expression_NegateFloat _ _ -> "float negation"
            Expression_NormalApplication _ _ _ -> "function application"
            Expression_Parenthesized _ _ -> "parenthesized expression"
            Expression_Tuple _ _ -> "tuple"
            Expression_Typed _ _ _ -> "expression with type annotation"
            Expression_Variable _ _ -> "variable"
            _ -> "some expression"
      UHA_Pat p -> "some pattern"
      UHA_Stat s -> "some statement"
      UHA_Qual q -> "some qualifier"
      UHA_FB fb -> "some function binding"
      UHA_RHS rhs -> "some right-hand side"
      UHA_Decl d -> "some declaration"
      UHA_Decls ds -> "some declarations"
      UHA_Def n -> "some definition"