module HeliumConstraintInfo where

import UHA_Syntax
import UHA_Utils
import OneLiner
import Types
import TypeErrors
import Messages
import TypeGraphConstraintInfo
import ConstraintInfo
import TypeConstraints
import List
import Tree
import Maybe
import UHA_Range
import Utils (internalError)
import DoublyLinkedTree
import UHA_Source

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
               }
                 
type Properties = [Property]
data Property   = FolkloreConstraint
                | PositionInTreeWalk Int
                | ConstraintPhaseNumber Int
                | HasTrustFactor Float
                | IsImported
                | IsLiteral Literal
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

instance Show HeliumConstraintInfo where
   show = location

type ConstraintSet  = Tree  (TypeConstraint HeliumConstraintInfo)
type ConstraintSets = Trees (TypeConstraint HeliumConstraintInfo)

instance ConstraintInfo HeliumConstraintInfo where                                  
                                   
   setOriginalTypeScheme scheme   = addProperty (OriginalTypeScheme scheme) 
   setConstraintPhaseNumber phase = addProperty (ConstraintPhaseNumber phase)
   setReductionError predicate    = addProperty (ReductionErrorInfo predicate)
     
      
instance TypeGraphConstraintInfo HeliumConstraintInfo where
   setNewTypeError typeError = addProperty (WithTypeError typeError)
   setNewHint hint = addProperty (WithHint hint)
   getPosition cinfo = case [ i | PositionInTreeWalk i <- properties cinfo ] of
                         [ i ] -> Just i
                         _     -> Nothing
   getConstraintPhaseNumber cinfo = case [ i | ConstraintPhaseNumber i <- properties cinfo ] of
                                       [i] -> Just i
                                       _   -> Nothing
   getTrustFactor cinfo =
      let ntFactor = case (self . attribute . localInfo) cinfo of
                        UHA_Pat  _ -> 3.0
                        UHA_Decl _ -> 3.0
                        UHA_FB   _ -> 3.0
                        _          -> 1.0
      in product (ntFactor : [ factor | HasTrustFactor factor <- properties cinfo ])

   isFolkloreConstraint   cinfo = not . null $ [ () | FolkloreConstraint   <- properties cinfo ]
   isExplicitTypedBinding cinfo = not . null $ [ () | ExplicitTypedBinding <- properties cinfo ]
   isTupleEdge            cinfo = not . null $ [ () | IsTupleEdge          <- properties cinfo ]
   isNegationResult       cinfo = not . null $ [ () | NegationResult       <- properties cinfo ]
   isExprVariable         cinfo =
         not (null [ () | FromBindingGroup <- properties cinfo ]) ||
         isJust (maybeImportedFunction cinfo)            
   
   maybeUserConstraint cinfo = case [ (i1, i2) | IsUserConstraint i1 i2 <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t

   maybeImportedFunction cinfo = case [ () | IsImported <- properties cinfo ] of
             []  -> Nothing
             t:_ -> case (self . attribute . localInfo) cinfo of
                       UHA_Expr (Expression_Variable _ name) -> Just name
                       _ -> Nothing
             
   maybeLiteral cinfo = case [ literal | IsLiteral literal <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t
   maybeApplicationEdge cinfo = case [ (b, zip (map self infoTrees) (map fromJust tps)) 
                                     | ApplicationEdge b infoTrees <- properties cinfo 
                                     , let tps = map assignedType infoTrees
                                     , all isJust tps
                                     ] of
             []        -> Nothing
             (b, xs):_ -> Just (b, [ (oneLinerSource self, tp, rangeOfSource self) | (self, tp) <- xs])
   maybeFunctionBinding cinfo = case [ t | FuntionBindingEdge t <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t            
   maybeNegation cinfo = case [ i | Negation i <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t            
   maybeUnifier cinfo = case [ i | Unifier i <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t            
   getTwoTypes = typepair

   setFolkloreConstraint = addProperty FolkloreConstraint
         
   isReductionErrorInfo = isJust . maybeReductionErrorPredicate
   maybeReductionErrorPredicate cinfo = 
      case [ p | ReductionErrorInfo p <- properties cinfo ] of
         [x] -> Just x
         _   -> Nothing

   makeTypeError cinfo | isReductionErrorInfo cinfo = 
      let err = internalError "HeliumConstraintInfo" "makeTypeError" "..."
          (_, tp) = typepair cinfo
      in makeReductionError 
           (convertErrorRange cinfo) 
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
        oneliners = [ (s, MessageOneLineTree tree) | (s, tree) <- convertSources (sources cinfo)]
        table = UnificationErrorTable oneliners msgtp1 msgtp2
        extra = -- documentationLink (info cinfo)
                [ hint | WithHint hint <- properties cinfo ]
             ++ [ IsFolkloreTypeError | isFolkloreConstraint cinfo ]
    in case [t | WithTypeError t <- properties cinfo] of
         typeError : _ -> typeError
         _             -> TypeError (convertErrorRange cinfo) oneliner table extra

   isPattern cinfo = 
      case (self . attribute . localInfo) cinfo of 
         UHA_Pat _ -> True
         _         -> False

   isEmptyInfixApplication cinfo = 
      not (null [ () | IsEmptyInfixApplication <- properties cinfo ])
      
      

{- documentationLink :: InfoSource -> TypeErrorInfo
documentationLink (nt, alt, nr, _) =
   HasDocumentationLink . concat $
      [ drop 2 (show nt)
      , "-"
      , drop 3 (show alt)
      , "-"
      , show nr
      ] -}
   
addProperty :: Property -> HeliumConstraintInfo -> HeliumConstraintInfo
addProperty property cinfo = 
   let old = properties cinfo
   in cinfo { properties = property : old }

setPosition :: Int -> TypeConstraint HeliumConstraintInfo -> TypeConstraint HeliumConstraintInfo
setPosition = fmap . addProperty . PositionInTreeWalk

maybeOriginalTypeScheme cinfo = 
   let flipped = case (self . attribute . localInfo) cinfo of
                    UHA_Expr (Expression_Typed _ _ _) -> False
                    _                                 -> True
   in case [ s | OriginalTypeScheme s <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just (flipped, t)
         
                
