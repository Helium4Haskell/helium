module HeliumConstraintInfo where

import ConstraintTree
import UHA_Syntax
import OneLiner
import Types
import TypeErrors
import Messages
import TypeGraphConstraintInfo
import ConstraintInfo
import Constraints
import List

{-
instance Substitutable HeliumConstraintInfo where
   sub |-> cinfo = let f (WithTypeError te) = WithTypeError (sub |-> te)
                       f p = p
                   in cinfo {typepair = sub |-> typepair cinfo , properties = map f (properties cinfo)}
   ftv cinfo = ftv (typepair cinfo) `union` ftv [ te | WithTypeError te <- properties cinfo ]
-}

data HeliumConstraintInfo = 
   CInfo { info       :: InfoSource
         , location   :: String
         , errorrange :: Range
         , sources    :: [(String, Tree)]
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
                | ApplicationEdge Bool{-is binary-} [(Tree,Tp)]{-info about terms-}
                | IsTupleEdge
                | ExplicitTypedBinding
                | FuntionBindingEdge Int
                | OriginalTypeScheme TpScheme
                | Size Int
                | Negation Int
                | NegationResult
                | WithTypeError TypeError    
                | WithHint TypeErrorInfo
  
instance Show HeliumConstraintInfo where
   show = show . getInfoSource

type ConstraintSet  = ConstraintTree  HeliumConstraintInfo
type ConstraintSets = ConstraintTrees HeliumConstraintInfo

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
             (nt,_,_) = info cinfo
    
   isFolkloreConstraint   cinfo = not . null $ [ () | FolkloreConstraint   <- properties cinfo ]
   isExplicitTypedBinding cinfo = not . null $ [ () | ExplicitTypedBinding <- properties cinfo ]
   isTupleEdge            cinfo = not . null $ [ () | IsTupleEdge          <- properties cinfo ]
   isNegationResult       cinfo = not . null $ [ () | NegationResult       <- properties cinfo ]

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
   getTwoTypes = typepair
   getSize cinfo     = case [ i | Size i <- properties cinfo ] of
                   []  -> Nothing
                   t:_ -> Just t

   maybeOriginalTypeScheme cinfo = case [ s | OriginalTypeScheme s <- properties cinfo ] of   
             []  -> Nothing
             t:_ -> Just (b,t)
        where b = not (x1 == NTExpression && x2 == AltTyped && x3 == "expression")
              (x1,x2,x3) = getInfoSource cinfo  
   setFolkloreConstraint = addProperty FolkloreConstraint
   

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
        table    = UnificationErrorTable (sources cinfo) msgtp1 msgtp2
        info =  [ hint | WithHint hint <- properties cinfo ] 
             ++ [ IsFolkloreTypeError | isFolkloreConstraint cinfo ] 
    in case [t | WithTypeError t <- properties cinfo] of
         typeError : _ -> typeError
         _             -> TypeError (errorrange cinfo) oneliner table info   
   
addProperty :: Property -> HeliumConstraintInfo -> HeliumConstraintInfo
addProperty property info = let old = properties info
                            in info { properties = property : old }

setPosition :: Int -> Constraint HeliumConstraintInfo -> Constraint HeliumConstraintInfo
setPosition i c = case c of
                    Equiv        a t1    t2 -> Equiv (f a) t1 t2
                    ImplInstance a t1 ms t2 -> ImplInstance (f' a) t1 ms t2
                    ExplInstance a t1    t2 -> ExplInstance (f' a) t1 t2
                    _                       -> c
   where f info = addProperty (PositionInTreeWalk i) info
         f' a = \(t1,t2) -> f (a (t1,t2))
