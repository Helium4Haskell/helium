-----------------------------------------------------------------------------
-- The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- The information that is stored with each type constraint that is constructed
-- during type inference.
--
-----------------------------------------------------------------------------

module ConstraintInfo where

import Top.Types
import Top.ComposedSolvers.Tree
import UHA_Syntax
import UHA_Source
import UHA_Range (showFullRange)
import OneLiner
import TypeErrors
import Messages
import HeliumMessages -- for instance Show
import DoublyLinkedTree
import TypeConstraints
import HighLightArea
import Utils (internalError)
import Data.Maybe
import Data.Char
import Data.FiniteMap

data ConstraintInfo =
   CInfo { location      :: String
         , sources       :: (UHA_Source, Maybe UHA_Source{- term -})
         , typepair      :: (Tp,Tp)        
         , localInfo     :: InfoTree
         , properties    :: Properties          
         }
     
instance Show ConstraintInfo where
   show = location

-----------------------------------------------------------------
-- Smart constructors

childConstraint :: Int -> String -> InfoTree -> Properties -> (Tp, Tp) -> ConstraintInfo
childConstraint childNr theLocation infoTree theProperties tppair =
  CInfo { location   = theLocation
        , sources    = ( (self . attribute) infoTree
                       , Just $ (self . attribute . selectChild childNr) infoTree
                       )
        , typepair   = tppair
        , localInfo  = infoTree        
        , properties = theProperties
        }

specialConstraint :: String -> InfoTree -> (UHA_Source, Maybe UHA_Source) -> Properties -> (Tp, Tp) -> ConstraintInfo
specialConstraint theLocation infoTree theSources theProperties tppair =
  CInfo { location   = theLocation
        , sources    = theSources
        , typepair   = tppair
        , localInfo  = infoTree        
        , properties = theProperties
        }
        
orphanConstraint :: Int -> String -> InfoTree -> Properties -> (Tp, Tp) -> ConstraintInfo
orphanConstraint childNr theLocation infoTree theProperties tppair =
  CInfo { location   = theLocation
        , sources    = ( (self . attribute . selectChild childNr) infoTree
                       , Nothing
                       )
        , typepair   = tppair
        , localInfo  = infoTree        
        , properties = theProperties
        }        
        
resultConstraint :: String -> InfoTree -> Properties -> (Tp, Tp) -> ConstraintInfo
resultConstraint theLocation infoTree theProperties tppair =
  CInfo { location   = theLocation
        , sources    = ( (self . attribute) infoTree 
                       , Nothing
                       )
        , typepair   = tppair
        , localInfo  = infoTree    
        , properties = theProperties
        }        

variableConstraint :: String -> UHA_Source -> Properties -> (Tp, Tp) -> ConstraintInfo
variableConstraint theLocation theSource theProperties tppair =
  CInfo { location   = theLocation
        , sources    = (theSource, Nothing)
        , typepair   = tppair
        , localInfo  = root (LocalInfo { self = theSource, assignedType = Just (snd tppair) }) []
        , properties = theProperties
        }               
        
cinfoBindingGroupExplicitTypedBinding :: Name -> (Tp,Tp) -> ConstraintInfo
cinfoSameBindingGroup                 :: Name -> (Tp,Tp) -> ConstraintInfo
cinfoBindingGroupImplicit             :: Name -> (Tp,Tp) -> ConstraintInfo
cinfoBindingGroupExplicit             :: Name -> (Tp,Tp) -> ConstraintInfo

cinfoBindingGroupExplicitTypedBinding name = 
   variableConstraint "explicitly typed binding" (nameToUHA_Expr name) [ FromBindingGroup, ExplicitTypedBinding, HasTrustFactor 10.0 ]
cinfoSameBindingGroup name = 
   variableConstraint "variable" (nameToUHA_Expr name) [ FromBindingGroup, FolkloreConstraint ]
cinfoBindingGroupImplicit name = 
   variableConstraint "variable" (nameToUHA_Expr name) [ FromBindingGroup, FolkloreConstraint, HasTrustFactor 10.0 ]
cinfoBindingGroupExplicit name = 
   variableConstraint "variable" (nameToUHA_Expr name) [ FromBindingGroup, FolkloreConstraint ] 

type InfoTrees = [InfoTree]
type InfoTree = DoublyLinkedTree LocalInfo
                            
data LocalInfo = 
     LocalInfo { self           :: UHA_Source  
               , assignedType   :: Maybe Tp
               , monos          :: Tps
               }
            
type ConstraintSet  = Tree  (TypeConstraint ConstraintInfo)
type ConstraintSets = Trees (TypeConstraint ConstraintInfo)
	    
type Properties = [Property]
data Property   = FolkloreConstraint
                | ConstraintPhaseNumber Int
                | HasTrustFactor Float
                | FuntionBindingEdge Int{-number of patterns-}
                | OriginalTypeScheme TpScheme
                | IsUserConstraint Int{-user-constraint-group unique number-} Int{-constraint number within group-}
                | WithTypeError TypeError
                | WithHint TypeErrorHint
		| HighlightAreas (Area, Area) 
                | ReductionErrorInfo Predicate
                | FromBindingGroup 
		| IsImported Name 
                | ApplicationEdge Bool{-is binary-} [LocalInfo]{-info about terms-}
                | ExplicitTypedBinding
		| Unifier Int{-type variable-} (String{-location-}, LocalInfo, String{-description-})
                | OriginalTypePair (Tp, Tp)
		
instance SetReduction ConstraintInfo where
  setReduction p = addProperty (ReductionErrorInfo p)

instance OriginalTypeScheme ConstraintInfo where
   setTypeScheme = addProperty . OriginalTypeScheme

maybeReductionErrorPredicate :: ConstraintInfo -> Maybe Predicate
maybeReductionErrorPredicate cinfo = 
   case [ p | ReductionErrorInfo p <- properties cinfo ] of
      [x] -> Just x
      _   -> Nothing

maybeHighlightAreas :: ConstraintInfo -> Maybe (Area, Area)
maybeHighlightAreas cinfo =
   case [ tuple | HighlightAreas tuple <- properties cinfo ] of
      [t] -> Just t
      _   -> Nothing
      
isFolkloreConstraint :: ConstraintInfo -> Bool
isFolkloreConstraint cinfo = 
   or [ True | FolkloreConstraint <- properties cinfo ]

addProperty :: Property -> ConstraintInfo -> ConstraintInfo
addProperty property cinfo = 
   cinfo { properties = property : properties cinfo }

maybeOriginalTypeScheme :: ConstraintInfo -> Maybe (Bool,TpScheme)
maybeOriginalTypeScheme cinfo = 
   let flipped = case (self . attribute . localInfo) cinfo of
                    UHA_Expr (Expression_Typed _ _ _) -> False
                    _                                 -> True
   in case [ s | OriginalTypeScheme s <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just (flipped, t)

maybeUserConstraint :: ConstraintInfo -> Maybe (Int, Int)
maybeUserConstraint info =
   case [ (x, y) | IsUserConstraint x y <- properties info ] of
      tuple:_ -> Just tuple
      _       -> Nothing
      
phaseOfConstraint :: ConstraintInfo -> Int
phaseOfConstraint info =
   case [ i | ConstraintPhaseNumber i <- properties info ] of  
      []  -> 5 -- default phase number
      i:_ -> i

setTypePair :: (Tp, Tp) -> ConstraintInfo -> ConstraintInfo
setTypePair pair info =
   let p (OriginalTypePair _) = False
       p _                    = True
   in info { typepair   = pair 
           , properties = OriginalTypePair (typepair info) : filter p (properties info)
           }
      
originalTypePair :: ConstraintInfo -> (Tp, Tp)
originalTypePair info = 
   case [ pair | OriginalTypePair pair <- properties info ] of
      [p] -> p
      _   -> typepair info
      
setTypeError :: TypeError -> ConstraintInfo -> ConstraintInfo
setTypeError typeError cinfo =
   let p (WithTypeError _) = False
       p _                 = True
   in cinfo { properties = WithTypeError typeError : filter p (properties cinfo) } 

makeTypeErrors :: Substitution sub => OrderedTypeSynonyms -> sub -> [ConstraintInfo] -> TypeErrors
makeTypeErrors synonyms sub = 
   map (sub |->) . catMaybes . map (makeTypeError synonyms sub)

makeTypeError :: Substitution sub => OrderedTypeSynonyms -> sub -> ConstraintInfo -> Maybe TypeError 
makeTypeError synonyms sub cinfo = 
   case maybeReductionErrorPredicate cinfo of
   
      -- a reduction error
      Just predicate -> 
         let source = fst (sources cinfo) 
	     tp     = snd (typepair cinfo)
	     scheme = case maybeOriginalTypeScheme cinfo of
	                 Just (_, ts) -> ts
		  	 Nothing      -> internalError "ConstraintInfo" "makeTypeError'" "could not find the original type scheme"
	 in Just (makeReductionError source (scheme, tp) standardClasses predicate)
      
      -- an unification error: first test if the two types can really not be unified
      Nothing -> 
         let (t1, t2) = typepair cinfo
	 in case mguWithTypeSynonyms synonyms (sub |-> t1) (sub |-> t2) of
               Left (InfiniteType _) -> 
	          let hint = ("because", MessageString "unification would give infinite type")
                  in Just (unificationTypeError (addProperty (WithHint hint) cinfo))
               Left _  -> 
	          Just (unificationTypeError cinfo)
               Right _ -> Nothing

unificationTypeError :: ConstraintInfo -> TypeError
unificationTypeError cinfo =
   let (source, term) = sources cinfo
       range    = maybe (rangeOfSource source) rangeOfSource term
       oneliner = MessageOneLiner (MessageString ("Type error in " ++ location cinfo))
       (t1, t2) = typepair cinfo 
       (msgtp1, msgtp2) = 
          case maybeOriginalTypeScheme cinfo of
             Nothing     -> (toTpScheme t1, toTpScheme t2)
             Just (flipped, ts)
                | flipped   -> (ts, toTpScheme t2)
                | otherwise -> (toTpScheme t2, ts)
       reason | isFolkloreConstraint cinfo = "expected type"
              | otherwise                  = "does not match"
       table = [ (s, MessageOneLineTree (oneLinerSource source)) | (s, source) <- convertSources (sources cinfo)] 
               ++
               [ ("type", MessageType msgtp1)
               , (reason, MessageType msgtp2)
               ]
       hints      = [ hint | WithHint hint <- properties cinfo ]
       highlights = 
          case maybeHighlightAreas cinfo of
             Nothing -> []
             Just (area1, area2) ->
	        [ ("highlight 1", MessageString $ show area1)
	       , ("highlight 2", MessageString $ show area2)
	       ]
  in case [t | WithTypeError t <- properties cinfo] of
	[] -> TypeError [range] [oneliner] table (hints++highlights)   
	TypeError ranges oneliners table hints : _ -> 
	   TypeError ranges oneliners table (hints++highlights)
	   
	       
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