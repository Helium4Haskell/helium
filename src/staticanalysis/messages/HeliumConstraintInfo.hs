module HeliumConstraintInfo where

import UHA_Syntax
import OneLiner
import Types
import TypeErrors
import Messages
import TypeGraphConstraintInfo
import ConstraintInfo
import TypeConstraints
import List
import Tree

data HeliumConstraintInfo =
   CInfo { info       :: InfoSource
         , location   :: String
         , errorrange :: Range
         , sources    :: [(String, OneLineTree)]
         , typepair   :: (Tp,Tp)
         , properties :: Properties          
         }

type Properties = [Property]
data Property   = FolkloreConstraint
                | PositionInTreeWalk Int
                | ConstraintPhaseNumber Int
                | HighlyTrusted
                | SuperHighlyTrusted
                | IsImported Name
                | IsLiteral Literal
                | ApplicationEdge Bool{-is binary-} [(OneLineTree, Tp, Range)]{-info about terms-}
                | IsTupleEdge
                | ExplicitTypedBinding
                | FuntionBindingEdge Int
                | OriginalTypeScheme TpScheme
                | Negation Bool{- is int negation -}
                | NegationResult
                | IsUserConstraint Int {- user-constraint-group unique number -} Int {- constraint number within group -}
                | WithTypeError TypeError
                | WithHint TypeErrorInfo
                | SubTermRange Range
                | Unifier Int {- the unifier -}

instance Show HeliumConstraintInfo where
   show = show . getInfoSource

type ConstraintSet  = Tree  (TypeConstraint HeliumConstraintInfo)
type ConstraintSets = Trees (TypeConstraint HeliumConstraintInfo)

instance ConstraintInfo HeliumConstraintInfo where                                  
                                   
   setOriginalTypeScheme scheme   = addProperty (OriginalTypeScheme scheme)           
   setConstraintPhaseNumber phase = addProperty (ConstraintPhaseNumber phase)

instance TypeGraphConstraintInfo HeliumConstraintInfo where

   getInfoSource = info
   setNewTypeError typeError = addProperty (WithTypeError typeError)
   setNewHint hint = addProperty (WithHint hint)
   getPosition cinfo = case [ i | PositionInTreeWalk i <- properties cinfo ] of
                         [ i ] -> Just i
                         _     -> Nothing
   getConstraintPhaseNumber cinfo = case [ i | ConstraintPhaseNumber i <- properties cinfo ] of
                                       [i] -> Just i
                                       _   -> Nothing
   getTrustFactor cinfo | isSuperHighlyTrusted          = Just 10000
                        | isHighlyTrusted               = Just 10
                        | nt `elem` [ NTPattern
                                    , NTDeclaration
                                    , NTFunctionBinding
                                    ]                   = Just 3
                        | otherwise                     = Nothing
       where isHighlyTrusted      = not (null [ () |      HighlyTrusted <- properties cinfo ])
             isSuperHighlyTrusted = not (null [ () | SuperHighlyTrusted <- properties cinfo ])
             (nt,_,_,_) = info cinfo

   isFolkloreConstraint   cinfo = not . null $ [ () | FolkloreConstraint   <- properties cinfo ]
   isExplicitTypedBinding cinfo = not . null $ [ () | ExplicitTypedBinding <- properties cinfo ]
   isTupleEdge            cinfo = not . null $ [ () | IsTupleEdge          <- properties cinfo ]
   isNegationResult       cinfo = not . null $ [ () | NegationResult       <- properties cinfo ]
   
   maybeUserConstraint cinfo = case [ (i1, i2) | IsUserConstraint i1 i2 <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t

   maybeImportedFunction cinfo = case [ name | IsImported name <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t
   maybeLiteral cinfo = case [ literal | IsLiteral literal <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t
   maybeApplicationEdge cinfo = case [ (b,tuple) | ApplicationEdge b tuple <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just t
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

   maybeOriginalTypeScheme cinfo = case [ s | OriginalTypeScheme s <- properties cinfo ] of
             []  -> Nothing
             t:_ -> Just (b,t)
        where b = not (x1 == NTExpression && x2 == AltTyped && x3 == 0)
              (x1, x2, x3, x4) = getInfoSource cinfo
   setFolkloreConstraint = addProperty FolkloreConstraint

   getErrorRange cinfo =
      case [ r | SubTermRange r <- properties cinfo ] of
         []  -> errorrange cinfo
         r:_ -> r

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
        oneliners = [ (s, MessageOneLineTree tree) | (s, tree) <- sources cinfo]
        table = UnificationErrorTable oneliners msgtp1 msgtp2
        extra = documentationLink (info cinfo)
              : [ hint | WithHint hint <- properties cinfo ]
             ++ [ IsFolkloreTypeError | isFolkloreConstraint cinfo ]
    in case [t | WithTypeError t <- properties cinfo] of
         typeError : _ -> typeError
         _             -> TypeError (getErrorRange cinfo) oneliner table extra

documentationLink :: InfoSource -> TypeErrorInfo
documentationLink (nt, alt, nr, _) =
   HasDocumentationLink . concat $
      [ drop 2 (show nt)
      , "-"
      , drop 3 (show alt)
      , "-"
      , show nr
      ]
   
addProperty :: Property -> HeliumConstraintInfo -> HeliumConstraintInfo
addProperty property info = let old = properties info
                            in info { properties = property : old }

setPosition :: Int -> TypeConstraint HeliumConstraintInfo -> TypeConstraint HeliumConstraintInfo
setPosition = fmap . addProperty . PositionInTreeWalk


