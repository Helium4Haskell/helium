module HeliumConstraintInfo where

import ConstraintTree
import UHA_Syntax
import OneLiner
import Types
import Messages
import TypeGraphConstraintInfo
import ConstraintInfo
import Constraints
import List

instance Substitutable HeliumConstraintInfo where
   sub |-> cinfo = let f (WithTypeError te) = WithTypeError (sub |-> te)
                       f p = p
                   in cinfo {typepair = sub |-> typepair cinfo , properties = map f (properties cinfo)}
   ftv cinfo = ftv (typepair cinfo) `union` ftv [ te | WithTypeError te <- properties cinfo ]

data HeliumConstraintInfo = 
   CInfo { info       :: InfoSource
         , location   :: String
         , errorrange :: Range
         , sources    :: SourceDocs
         , typepair   :: (Tp,Tp)
         , properties :: Properties          
         }
          
type Properties = [Property]
data Property   = FolkloreConstraint
                | PositionInTreeWalk Int
                | HighlyTrusted
                | SuperHighlyTrusted
                | UnifierTypeVariable Int
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
                | WithHint Hint            
   
instance Eq   Literal where _ == _ = True -- NEE!
instance Show Literal where show _ = "<literal>"

instance Show HeliumConstraintInfo where
   show = show . getInfoSource

type ConstraintSet  = ConstraintTree  HeliumConstraintInfo
type ConstraintSets = ConstraintTrees HeliumConstraintInfo

instance ConstraintInfo HeliumConstraintInfo where                                  
                                   
   setOriginalTypeScheme scheme         = addProperty (OriginalTypeScheme scheme)           
    
instance TypeGraphConstraintInfo HeliumConstraintInfo where


   makeTypeError cinfo =
    case [ te | WithTypeError te <- properties cinfo ] of
      [ te ] -> setHint hint te
      _      -> TypeError (isFolkloreConstraint cinfo) 
                          (location cinfo) 
                          (errorrange cinfo) 
                          (sources cinfo) 
                          (maybeOriginalTypeScheme cinfo,t1,t2)
                          hint
    where (t1,t2) = typepair cinfo 
          hint = case [ h | WithHint h <- properties cinfo ] of 
                    hint:_ -> hint
                    _      -> NoHint

   getInfoSource = info
   setNewTypeError typeError = addProperty (WithTypeError typeError)
   setNewHint hint = addProperty (WithHint hint)
   getPosition cinfo = case [ i | PositionInTreeWalk i <- properties cinfo ] of 
                         [ i ] -> Just i
                         _     -> Nothing
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
   
addProperty :: Property -> HeliumConstraintInfo -> HeliumConstraintInfo
addProperty property info = let old = properties info
                            in info { properties = property : old }

setPosition :: Int -> Constraint HeliumConstraintInfo -> Constraint HeliumConstraintInfo
setPosition i c = case c of
                    Equiv        a t1    t2 -> Equiv (f a) t1 t2
                    ImplInstance a t1 ms t2 -> ImplInstance (f' a) t1 ms t2
                    ExplInstance a t1    t2 -> ExplInstance (f' a) t1 t2
   where f info = addProperty (PositionInTreeWalk i) info
         f' a = \(t1,t2) -> f (a (t1,t2))
