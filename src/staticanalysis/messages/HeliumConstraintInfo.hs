module HeliumConstraintInfo where

import UHA_Syntax
import UHA_Utils
import OneLiner
import Top.Types
import TypeErrors
import Messages
import List
import Top.ComposedSolvers.Tree
import Maybe
import UHA_Range
import Utils (internalError)
import DoublyLinkedTree
import UHA_Source
import Char (toLower, isDigit)
import Data.FiniteMap
import LiftedConstraints
import RepairHeuristics
import TieBreakerHeuristics
import OnlyResultHeuristics
import Top.TypeGraph.Heuristics

data HeliumConstraintInfo =
   CInfo { location      :: String
         , sources       :: (UHA_Source, Maybe UHA_Source {- term -}) 
         , typepair      :: (Tp,Tp)        
         , localInfo     :: InfoTree
         , properties    :: Properties          
         }

convertErrorRange :: HeliumConstraintInfo -> Range
convertErrorRange cinfo = 
   let (source, term) = sources cinfo
   in maybe (rangeOfSource source) rangeOfSource term
        
type InfoTrees = [InfoTree]
type InfoTree = DoublyLinkedTree LocalInfo
                            
data LocalInfo = 
     LocalInfo { self           :: UHA_Source  
               , assignedType   :: Maybe Tp
               , monos          :: FiniteMap Name Tp
               }
                 
type Properties = [Property]
data Property   = FolkloreConstraint
                | PositionInTreeWalk Int
                | ConstraintPhaseNumber Int
                | HasTrustFactor Float
                | IsImported Name
                | IsLiteral String
                | ApplicationEdge Bool{-is binary-} [LocalInfo]{-info about terms-}
                | IsTupleEdge
                | ExplicitTypedBinding
                | FuntionBindingEdge Int
                | OriginalTypeScheme TpScheme
                | Negation Bool{- is int negation -}
                | NegationResult
                | IsUserConstraint Int {- user-constraint-group unique number -} Int {- constraint number within group -}
                | WithTypeError TypeError
                | WithHint TypeErrorInfo
                | Unifier Int {- the unifier -}
                | ReductionErrorInfo Predicate
                | IsEmptyInfixApplication
                | FromBindingGroup

instance HasTrustFactor HeliumConstraintInfo where
   trustFactor cinfo =
      let ntFactor = case (self . attribute . localInfo) cinfo of
                        UHA_Pat  _ -> 3.0
                        UHA_Decl _ -> 3.0
                        UHA_FB   _ -> 3.0
                        _          -> 1.0
      in product (ntFactor : [ factor | HasTrustFactor factor <- properties cinfo ])

instance HasDirection HeliumConstraintInfo where
   isTopDown cinfo = not . null $ [ () | FolkloreConstraint   <- properties cinfo ]

instance MaybeImported HeliumConstraintInfo where
   maybeImportedName cinfo = 
      case [ name | IsImported name <- properties cinfo ] of
         []  -> Nothing
         n:_ -> Just (show n)

instance HasTwoTypes HeliumConstraintInfo where
   getTwoTypes = typepair

instance MaybeLiteral HeliumConstraintInfo where
   maybeLiteral cinfo =
      case [ literal | IsLiteral literal <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just t

instance IsPattern HeliumConstraintInfo where
   isPattern cinfo = 
      case (self . attribute . localInfo) cinfo of 
         UHA_Pat _ -> True
         _         -> False

instance MaybeApplication HeliumConstraintInfo where
   maybeNumberOfArguments = 
      fmap (length . snd) . maybeApplicationEdge
      
   maybeApplicationEdge cinfo = 
      case [ (b, zip (map self infoTrees) (map fromJust tps)) 
           | ApplicationEdge b infoTrees <- properties cinfo 
           , let tps = map assignedType infoTrees
           , all isJust tps
           ] of
         [] -> Nothing
         (b, xs):_ -> 
            Just (b, [ (oneLinerSource self, tp, rangeOfSource self)  
                     | (self, tp) <- xs
                     ])
   
instance MaybeNegation HeliumConstraintInfo where
   maybeNegation cinfo = case [ i | Negation i <- properties cinfo ] of
      []  -> Nothing
      t:_ -> Just t 

instance IsExprVariable HeliumConstraintInfo where
   isExprVariable cinfo =
      not (null [ () | FromBindingGroup <- properties cinfo ])
      || isJust (maybeImportedName cinfo) 
   isEmptyInfixApplication cinfo = 
      not (null [ () | IsEmptyInfixApplication <- properties cinfo ])

instance IsFunctionBinding HeliumConstraintInfo where
   isExplicitlyTyped cinfo = 
      not . null $ [ () | ExplicitTypedBinding <- properties cinfo ]
   maybeFunctionBinding cinfo = 
      case [ t | FuntionBindingEdge t <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just t 
   
instance IsTupleEdge HeliumConstraintInfo where
   isTupleEdge cinfo = 
      not . null $ [ () | IsTupleEdge <- properties cinfo ]
      
instance WithHints HeliumConstraintInfo where
  fixHint s        = addProperty (WithHint (TypeErrorHint "probable fix" (MessageString s)))
  becauseHint s    = addProperty (WithHint (TypeErrorHint "because" (MessageString s)))
  typeErrorForTerm = makeTypeErrorForTerm

instance SetReduction HeliumConstraintInfo where
  setReduction p = addProperty (ReductionErrorInfo p)

instance OriginalTypeScheme HeliumConstraintInfo where
   setTypeScheme = addProperty . OriginalTypeScheme

instance Show HeliumConstraintInfo where
   show = location

type ConstraintSet  = Tree  (TypeConstraint HeliumConstraintInfo)
type ConstraintSets = Trees (TypeConstraint HeliumConstraintInfo)

-- from the old instance declaration
isReductionErrorInfo = isJust . maybeReductionErrorPredicate
maybeReductionErrorPredicate cinfo = 
   case [ p | ReductionErrorInfo p <- properties cinfo ] of
      [x] -> Just x
      _   -> Nothing
isFolkloreConstraint cinfo = not . null $ [ () | FolkloreConstraint <- properties cinfo ]

makeTypeError :: HeliumConstraintInfo -> TypeError
makeTypeError cinfo | isReductionErrorInfo cinfo = 
   let err = internalError "HeliumConstraintInfo" "makeTypeError" "..."
       (_, tp) = typepair cinfo
   in makeReductionError       
        (case convertSources (sources cinfo) of (_,tree):_ -> tree ; _ -> err) 
        (case maybeOriginalTypeScheme cinfo of Just (b,ts) -> (ts, tp) ; _ -> err)
        standardClasses
        (case maybeReductionErrorPredicate cinfo of Just p -> p ; _ -> err)
   
makeTypeError cinfo =
 let oneliner = MessageString ("Type error in " ++ location cinfo)
     reason   = if isFolkloreConstraint cinfo
                  then "Expected type"
                  else "Does not match"
     (t1, t2) = typepair cinfo
     (msgtp1, msgtp2) = case maybeOriginalTypeScheme cinfo of
        Nothing     -> (Left t1, Left t2)
        Just (b,ts)
             | b    -> (Right ts, Left t2)
             | True -> (Left t2, Right ts)
     oneliners = [ (s, MessageOneLineTree (oneLinerSource source)) | (s, source) <- convertSources (sources cinfo)]
     table = UnificationErrorTable oneliners msgtp1 msgtp2
     extra = -- documentationLink (info cinfo)
             [ hint | WithHint hint <- properties cinfo ]
          ++ [ IsFolkloreTypeError | isFolkloreConstraint cinfo ]
 in case [t | WithTypeError t <- properties cinfo] of
      typeError : _ -> typeError
      _             -> TypeError (convertErrorRange cinfo) oneliner table extra



   
-- not a nice solution!
makeTypeErrorForTerm :: (Bool,Bool) -> Int -> OneLineTree -> (Tp,Tp) -> Range -> HeliumConstraintInfo -> HeliumConstraintInfo
makeTypeErrorForTerm (isInfixApplication,isPatternApplication) argumentNumber termOneLiner (t1, t2) range cinfo =
   case makeTypeError cinfo of

      TypeError _ oneliner (UnificationErrorTable sources ftype _) infos ->
         let newSources = filter onlyExpression sources ++ [ (function, functionPretty)
                                                           , ("type", functionType)
                                                           , (subterm, MessageOneLineTree termOneLiner)
                                                           ]
             onlyExpression = (\x -> x=="expression" || x=="pattern") . fst
             function | isPatternApplication = "constructor"
                      | otherwise            = if isInfixApplication then "operator" else "function"
             functionPretty = case filter (\(x, _) -> x=="term" || x=="operator" || x=="constructor") sources of
                                 (_, x):_ -> x
                                 _        -> internalError "TypeGraphConstraintInfo.hs"
                                                           "makeTypeErrorForTerm"
                                                           "unexpected empty list"
             functionType = either (\tp -> MessageType ([] .=>. tp)) MessageTypeScheme ftype
             subterm
                | isInfixApplication = if argumentNumber == 0 then "left operand" else "right operand"
                | otherwise          = ordinal False (argumentNumber + 1) ++ " argument"
         in addProperty (WithTypeError (TypeError range oneliner (UnificationErrorTable newSources (Left t1) (Left t2)) infos)) cinfo

      typeError -> cinfo
   
addProperty :: Property -> HeliumConstraintInfo -> HeliumConstraintInfo
addProperty property cinfo = 
   let old = properties cinfo
   in cinfo { properties = property : old }

maybeOriginalTypeScheme :: HeliumConstraintInfo -> Maybe (Bool,TpScheme)
maybeOriginalTypeScheme cinfo = 
   let flipped = case (self . attribute . localInfo) cinfo of
                    UHA_Expr (Expression_Typed _ _ _) -> False
                    _                                 -> True
   in case [ s | OriginalTypeScheme s <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just (flipped, t)
         
{-                
browseInfoTree :: Substitution substitution => substitution -> InfoTree -> IO ()
browseInfoTree substitution infoTree = 
   do putStrLn . unlines $       
         [ bgCyan $ fgBlack $ descriptionOfSource source ++ " at " ++ show (rangeOfSource source)
         , showOneLine 60 (oneLinerSource source) 
         , "type : " ++ theType ++ "\n" ++ unlines monoContext
         , commands
         ]
      waitForCommand  

  where 
     source  = (self . attribute) infoTree
     theType = case (assignedType . attribute) infoTree of
                  Just tp -> show (sub |-> (substitution |-> tp))
                  Nothing -> "none"
     usedContext = let ftvType = ftv (substitution |-> assignedType (attribute infoTree))
                       split is tuples = 
                          case partition (any (`elem` is). ftv . snd) tuples of
                             ([], _) -> []
                             (_, []) -> tuples
                             (as,bs) -> as ++ split (ftv (map snd as)) bs
                   in split ftvType [ (s, substitution |-> tp) 
                                    | (name, tp) <- fmToList (monos (attribute infoTree)), let s = show name, s /= "_" 
                                    ]
     sub = let ftvList = ftv (substitution |-> ((assignedType . attribute) infoTree)) `union`
                         ftv (map snd usedContext)
           in listToSubstitution $ zip ftvList (map TCon variableList)
     hasParent = isJust (parent infoTree) 
     nrOfChildren = length (children infoTree) 
     monoContext = let pre = "   with " : repeat "        "
                   in zipWith (++) pre [ s ++ " :: " ++ show (sub |-> tp) | (s, tp) <- usedContext ]
     commands = (if hasParent then fgCyan "U" ++ " Up   " else "") ++
                (case nrOfChildren of
                    0 -> ""
                    1 -> fgCyan "1" ++ " Select child   "
                    n -> fgCyan ("1-"++show n)++" Select child   ") ++
                (fgCyan "Q" ++ " Quit")
     waitForCommand =
        do command <- getLine
           case map toLower command of 
              ""  -> waitForCommand
              "q" -> putStrLn "[Leaving type-view]"
              "u" | hasParent -> browseInfoTree substitution (fromJust (parent infoTree))
              number | all isDigit number -> 
                 let i = (read number) :: Int
                 in if i > 0 && i <= nrOfChildren 
                      then browseInfoTree substitution (selectChild (i-1) infoTree)
                      else waitForCommand
              _ -> waitForCommand

bgCyan s  = "\ESC[46m" ++ s ++ bgDefault
bgBlue s  = "\ESC[44m" ++ s ++ bgDefault
fgBlack s = "\ESC[30m" ++ s ++ fgDefault
fgCyan s  = "\ESC[36m" ++ s ++ fgDefault
bgDefault = "\ESC[49m"
fgDefault = "\ESC[39m" -}