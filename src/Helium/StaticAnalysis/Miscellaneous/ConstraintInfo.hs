{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{-| Module      :  ConstraintInfo
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    The information that is stored with each type constraint that is constructed
	during type inference.
-}

module Helium.StaticAnalysis.Miscellaneous.ConstraintInfo where

import Helium.Main.Args (Option(..))
import Top.Types
import Top.Ordering.Tree
import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.Syntax.UHA_Range
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.StaticAnalysis.Miscellaneous.TypeConstraints

import Data.Typeable
import Data.Data

import Top.Constraint.Information
import Top.Implementation.Overloading
import Top.Interface.Basic (ErrorLabel)
import Top.Interface.Substitution (unificationErrorLabel)
import Top.Interface.TypeInference
import Helium.Utils.Utils (internalError)
import Data.Maybe
import Data.Function
import Data.List
import Control.Applicative

data ConstraintInfo =
   CInfo_ { location      :: String
          , sources       :: (UHA_Source, Maybe UHA_Source{- term -})
          , localInfo     :: InfoTree
          , properties    :: Properties
          , errorMessage  :: Maybe TypeError
          }
     
instance Show ConstraintInfo where
   show x = location x ++ show (properties x)

-------------------------------------------------------------------------
-- Properties

type Properties = [Property]
data Property   
   = FolkloreConstraint
   | ConstraintPhaseNumber Int
   | HasTrustFactor Float
   | FuntionBindingEdge Int{-number of patterns-}
   | InstantiatedTypeScheme TpScheme
   | SkolemizedTypeScheme (Tps, TpScheme)
   | IsUserConstraint Int{-user-constraint-group unique number-} Int{-constraint number within group-}
   | WithHint (String, MessageBlock)
   | ReductionErrorInfo Predicate
   | FromBindingGroup 
   | IsImported Name 
   | ApplicationEdge Bool{-is binary-} [LocalInfo]{-info about terms-}
   | ExplicitTypedBinding -- superfluous?
   | ExplicitTypedDefinition Tps{- monos-} Name{- function name -}
   | Unifier Int{-type variable-} (String{-location-}, LocalInfo, String{-description-})
   | EscapedSkolems [Int]
   | PredicateArisingFrom (Predicate, ConstraintInfo)
   | TypeSignatureLocation Range
   | TypePair (Tp, Tp)
   | CustomError String
   | NeverDirectiveProperty (Predicate, ConstraintInfo)
   | CloseDirectiveProperty (String, ConstraintInfo)
   | DisjointDirectiveProperty (String, ConstraintInfo) (String, ConstraintInfo)

instance Show Property where
   show FolkloreConstraint = "FolkloreConstraint"
   show (ConstraintPhaseNumber _) = "ConstraintPhaseNumber"
   show (HasTrustFactor _) = "HasTrustFactor"
   show (FuntionBindingEdge _) = "FuntionBindingEdge"
   show (InstantiatedTypeScheme _) = "InstantiatedTypeScheme"
   show (SkolemizedTypeScheme _) = "SkolemizedTypeScheme"
   show (IsUserConstraint _ _) = "IsUserConstraint"
   show (WithHint _ ) = "WithHint"
   show (ReductionErrorInfo _) = "ReductionErrorInfo"
   show (FromBindingGroup) = "FromBindingGroup"
   show (IsImported _) = "IsImported"
   show (ApplicationEdge _ lc) = "ApplicationEdge" ++ show (map assignedType lc)
   show ExplicitTypedBinding = "ExplicitTypedBinding"
   show (ExplicitTypedDefinition _ _) = "ExplicitTypedDefinition"
   show (Unifier _ _) = "Unifier"
   show (EscapedSkolems _) = "EscapedSkolems"
   show (PredicateArisingFrom _) = "PredicateArisingFrom"
   show (TypeSignatureLocation _) = "TypeSignatureLocation"
   show (TypePair (t1, t2)) = "TypePair (" ++ show t1 ++ ", " ++ show t2 ++ ")" 


class HasProperties a where
   getProperties :: a -> Properties
   addProperty   :: Property   -> a -> a
   addProperties :: Properties -> a -> a 

   -- default definitions
   addProperty    = addProperties . (:[])
   addProperties  = flip (foldr addProperty)

instance HasProperties Properties where
   getProperties = id
   addProperty   = (:)
   addProperties = (++)

instance HasProperties ConstraintInfo where
   getProperties = properties
   addProperties ps info = 
      info { properties = ps ++ properties info }

-------------------------------------------------------------------------
-- Property functions

maybeHead :: [a] -> Maybe a
maybeHead []    = Nothing
maybeHead (a:_) = Just a

headWithDefault :: a -> [a] -> a
headWithDefault a = fromMaybe a . maybeHead

maybeNeverDirectivePredicate :: HasProperties a => a -> Maybe (Predicate, ConstraintInfo)
maybeNeverDirectivePredicate a = 
   maybeHead [ (p, info) | NeverDirectiveProperty (p, info) <- getProperties a ]

maybeCloseDirective :: HasProperties a => a -> Maybe (String, ConstraintInfo)
maybeCloseDirective a = maybeHead [ (n, info) | CloseDirectiveProperty (n, info) <- getProperties a]

maybeDisjointDirective :: HasProperties a => a -> Maybe ((String, ConstraintInfo), (String, ConstraintInfo))
maybeDisjointDirective a = maybeHead [((n1, info1),(n2, info2)) | DisjointDirectiveProperty (n1, info1) (n2, info2) <- getProperties a]

maybeReductionErrorPredicate :: HasProperties a => a -> Maybe Predicate
maybeReductionErrorPredicate a = 
    maybeHead [ p | ReductionErrorInfo p <- getProperties a ]

isFolkloreConstraint :: HasProperties a => a -> Bool
isFolkloreConstraint a = 
   not $ null [ () | FolkloreConstraint <- getProperties a ]

-- |Returns only type schemes with at least one quantifier
maybeInstantiatedTypeScheme :: HasProperties a => a -> Maybe TpScheme
maybeInstantiatedTypeScheme a =
   maybeHead [ s | InstantiatedTypeScheme s <- getProperties a, not (withoutQuantors s) ]
   
maybeSkolemizedTypeScheme :: HasProperties a => a -> Maybe (Tps, TpScheme)
maybeSkolemizedTypeScheme info =
   maybeHead [ s | SkolemizedTypeScheme s <- getProperties info ]

maybeCustomError :: HasProperties a => a -> Maybe String
maybeCustomError info = maybeHead [ s | CustomError s <- getProperties info ]

maybeUserConstraint :: HasProperties a => a -> Maybe (Int, Int)
maybeUserConstraint a =
   maybeHead [ (x, y) | IsUserConstraint x y <- getProperties a ]
      
phaseOfConstraint :: HasProperties a => a -> Int
phaseOfConstraint a =
   headWithDefault 5 [ i | ConstraintPhaseNumber i <- getProperties a ]

isExplicitTypedBinding :: HasProperties a => a -> Bool
isExplicitTypedBinding a =
   not $ null [ () | ExplicitTypedBinding <- getProperties a ]

maybeExplicitTypedDefinition :: HasProperties a => a -> Maybe (Tps, Name)
maybeExplicitTypedDefinition a =
   maybeHead [ (ms, n) | ExplicitTypedDefinition ms n <- getProperties a ]

maybeTypeSignatureLocation :: HasProperties a => a -> Maybe Range
maybeTypeSignatureLocation a =
   maybeHead [ r | TypeSignatureLocation r <- getProperties a ]

maybePredicateArisingFrom :: HasProperties a => a -> Maybe (Predicate, ConstraintInfo)
maybePredicateArisingFrom a =
   maybeHead [ t | PredicateArisingFrom t <- getProperties a ]
      
getEscapedSkolems :: HasProperties a => a -> [Int]
getEscapedSkolems a =
   concat [ is | EscapedSkolems is <- getProperties a ]
         
-----------------------------------------------------------------
-- Smart constructors

childConstraint :: Int -> String -> InfoTree -> Properties -> ConstraintInfo
childConstraint childNr theLocation infoTree theProperties =
  CInfo_ { location   = theLocation
         , sources    = ( (self . attribute) infoTree
                        , Just $ (self . attribute . selectChild childNr) infoTree
                        )
         , localInfo  = infoTree        
         , properties = theProperties
         , errorMessage = Nothing
         }

specialConstraint :: String -> InfoTree -> (UHA_Source, Maybe UHA_Source) -> Properties -> ConstraintInfo
specialConstraint theLocation infoTree theSources theProperties =
  CInfo_ { location   = theLocation
         , sources    = theSources
         , localInfo  = infoTree        
         , properties = theProperties
         , errorMessage = Nothing
         }
        
orphanConstraint :: Int -> String -> InfoTree -> Properties -> ConstraintInfo
orphanConstraint childNr theLocation infoTree theProperties =
  CInfo_ { location   = theLocation
         , sources    = ( (self . attribute . selectChild childNr) infoTree
                        , Nothing
                        )
         , localInfo  = infoTree        
         , properties = theProperties
         , errorMessage = Nothing
         }        
        
resultConstraint :: String -> InfoTree -> Properties -> ConstraintInfo
resultConstraint theLocation infoTree theProperties =
  CInfo_ { location   = theLocation
         , sources    = ( (self . attribute) infoTree 
                        , Nothing
                        )
         , localInfo  = infoTree    
         , properties = theProperties
         , errorMessage = Nothing
         }        

variableConstraint :: String -> UHA_Source -> Properties -> ConstraintInfo
variableConstraint theLocation theSource theProperties =
  CInfo_ { location   = theLocation
         , sources    = (theSource, Nothing)
         , localInfo  = root LocalInfo { self = theSource, assignedType = Nothing {- ?? -}, monos = [] } []
         , properties = theProperties
         , errorMessage = Nothing
         }               
        
cinfoBindingGroupExplicitTypedBinding :: Tps -> Name -> Name ->  ConstraintInfo
cinfoSameBindingGroup                 :: Name ->                 ConstraintInfo
cinfoBindingGroupImplicit             :: Name ->                 ConstraintInfo
cinfoBindingGroupExplicit             :: Tps -> Names -> Name -> ConstraintInfo
cinfoGeneralize                       :: Name ->                 ConstraintInfo

cinfoBindingGroupExplicitTypedBinding ms name nameTS = 
   let props = [ FromBindingGroup, ExplicitTypedBinding, ExplicitTypedDefinition ms name, 
                 HasTrustFactor 10.0, TypeSignatureLocation (getNameRange nameTS) ]
   in variableConstraint "explicitly typed binding" (nameToUHA_Def name) props
cinfoSameBindingGroup name = 
   let props = [ FromBindingGroup, FolkloreConstraint ]
   in variableConstraint "variable" (nameToUHA_Expr name) props
cinfoBindingGroupImplicit name = 
   let props = [ FromBindingGroup, FolkloreConstraint, HasTrustFactor 10.0 ]
   in variableConstraint "variable" (nameToUHA_Expr name) props
cinfoBindingGroupExplicit ms defNames name = 
   let props1 = [ FromBindingGroup, FolkloreConstraint ]
       props2 = case filter (name==) defNames of
                   [defName] -> [ExplicitTypedDefinition ms defName]
                   _         -> []
   in variableConstraint "variable" (nameToUHA_Expr name) (props1 ++ props2)
cinfoGeneralize name =
   variableConstraint ("Generalize " ++ show name) (nameToUHA_Expr name) []

type InfoTrees = [InfoTree]
type InfoTree = DoublyLinkedTree LocalInfo
                            
data LocalInfo = 
     LocalInfo { self           :: UHA_Source  
               , assignedType   :: Maybe Tp
               , monos          :: Tps
               }

-- For Proxima
typeSchemesInInfoTree :: FixpointSubstitution -> Predicates -> InfoTree -> [(Range, TpScheme)]
typeSchemesInInfoTree subst ps infoTree =
   let local = attribute infoTree
       rest  = concatMap (typeSchemesInInfoTree subst ps) (children infoTree)
   in case assignedType local of 
         Just tp -> let is     = ftv tp 
                        ps'    = filter (any (`elem` is) . ftv) ps
                        scheme = generalizeAll (subst |-> (ps' .=>. tp))
                    in (rangeOfSource (self local), scheme) : rest
         Nothing -> rest

type ConstraintSet  = Tree  (TypeConstraint ConstraintInfo)
type ConstraintSets = Trees (TypeConstraint ConstraintInfo)
   
instance TypeConstraintInfo ConstraintInfo where
   unresolvedPredicate  = addProperty . ReductionErrorInfo
   ambiguousPredicate   = addProperty . ReductionErrorInfo
   escapedSkolems       = addProperty . EscapedSkolems
   predicateArisingFrom = addProperty . PredicateArisingFrom
   equalityTypePair     = setTypePair
   neverDirective       = addProperty . NeverDirectiveProperty
   closeDirective       = addProperty . CloseDirectiveProperty
   disjointDirective    = (addProperty .) . DisjointDirectiveProperty
   

instance PolyTypeConstraintInfo ConstraintInfo where
   instantiatedTypeScheme = addProperty . InstantiatedTypeScheme
   skolemizedTypeScheme   = addProperty . SkolemizedTypeScheme
   

      
highlyTrustedFactor :: Float
highlyTrustedFactor = 10000.0

highlyTrusted :: Property
highlyTrusted = HasTrustFactor highlyTrustedFactor

isHighlyTrusted :: ConstraintInfo -> Bool
isHighlyTrusted info = 
   product [ i | HasTrustFactor i <- properties info ] >= highlyTrustedFactor

setTypePair :: (Tp, Tp) -> ConstraintInfo -> ConstraintInfo
setTypePair pair ci = addProperty (TypePair pair) ci

typepair :: ConstraintInfo -> (Tp, Tp)
typepair info = fromJust (maybeHead [ pair | TypePair pair <- getProperties info ])

isExprTyped :: ConstraintInfo -> Bool
isExprTyped info = 
   case fst (sources info) of
      UHA_Expr (Expression_Typed _ _ _) -> True
      _                                 -> False     
    
tooGeneralLabels :: [ErrorLabel]
tooGeneralLabels = [skolemVersusConstantLabel, skolemVersusSkolemLabel, escapingSkolemLabel]

-- TODO: get rid of the TypeError and TypeErrorHint data types, and move the following two functions
-- to the module TypeErrors
    
makeTypeErrors :: Substitution sub => [Option] -> ClassEnvironment -> OrderedTypeSynonyms -> sub -> [(ConstraintInfo, ErrorLabel)] -> TypeErrors
makeTypeErrors options classEnv synonyms sub errors =
   let --comp l1 l2
       --   | l1 `elem` tooGeneralLabels && l2 `elem` tooGeneralLabels = EQ
       --   | otherwise = l1 `compare` l2
   
       list  = groupBy ((==) `on` snd) 
             $ sortBy  (compare `on` snd)
             $ (if NoOverloadingTypeCheck `elem` options 
                then filter ((/= ambiguousLabel) . snd) 
                else id)
               errors
       final = groupBy ((==) `on` fst) 
             $ sortBy  (compare `on` fst) 
             $ filter (not . null . snd)
               [ make label (info : map fst rest) | (info, label):rest <- list ]
   in case final of
         []   -> []
         hd:_ -> concatMap snd hd

 where
   special :: ConstraintInfo -> TypeError -> TypeError
   special info defaultMessage =
      maybe defaultMessage (sub |->) (maybeSpecialTypeError info)
 
   make :: ErrorLabel -> [ConstraintInfo] -> (Int, TypeErrors)
   make label infos
      
      -- an unification error: first test if the two types can really not be unified
      | label == unificationErrorLabel =
           let f info = 
                  case mguWithTypeSynonyms synonyms (sub |-> fst (typepair info)) (sub |-> snd (typepair info)) of
                     Left (InfiniteType _) -> 
                        let hint = ("because", MessageString "unification would give infinite type")
                        in [ sub |-> special info (makeUnificationTypeError (addProperty (WithHint hint) info)) ]
                     Left _  -> 
                        [ sub |-> special info (makeUnificationTypeError info) ]
                     Right _ -> []
           in (1, concatMap f infos)
      
      -- missing class predicate in declared type (hence, declared type is too general)
      | label == missingInSignatureLabel =
           let f info =
                  let (p, infoArising) = fromMaybe err (maybePredicateArisingFrom info)
                      range   = fromMaybe err (maybeTypeSignatureLocation info)
                      mSource = if isExprTyped info then Nothing else Just (fst $ sources info)
                      scheme  = maybe err snd (maybeSkolemizedTypeScheme info)
                      t1      = freezeVariablesInType (unqualify (unquantify scheme))
                      t2      = sub |-> fst (typepair info)
                      tuple   = case mguWithTypeSynonyms synonyms t1 t2 of
                                   Left _ -> (False, p)
                                   Right (_, sub1) ->
                                      let Predicate className tp = sub1 |-> p
                                          sub' = listToSubstitution [ (i, TCon s) | (i, s) <- getQuantorMap scheme ]
                                      in (True, Predicate className (sub' |-> unfreezeVariablesInType tp))
                      err    = internalError "ConstraintInfo" "makeTypeErrors" "unknown class predicate"
                  in special info (makeMissingConstraintTypeError range mSource scheme tuple (fst $ sources infoArising))
           in (2, map f infos)
      
      -- declared type is too general
      | label `elem` tooGeneralLabels =
           let f info = 
                  let monoset = sub |-> ms
                      range   = fromMaybe err (maybeTypeSignatureLocation info)
                      scheme1 = generalize monoset ([] .=>. sub |->  snd (typepair info))
                      (ms, scheme2) = fromMaybe err (maybeSkolemizedTypeScheme info)
                      source  = uncurry fromMaybe (sources info)
                      err     = internalError "ConstraintInfo" "makeTypeErrors" "unknown original type scheme"
                  in special info (makeNotGeneralEnoughTypeError (isExprTyped info) range source scheme1 scheme2)
           in (if label == escapingSkolemLabel then 3 else 2, map f infos)

      -- a reduction error
      | label == unresolvedLabel =
           let f info = 
                  let 
                      maybeNever = maybeNeverDirectivePredicate info
                      maybeClose = maybeCloseDirective info
                      customMessage = maybe Nothing (maybeCustomError) (snd <$> maybeNever <|> snd <$> maybeClose)
                      source = fst (sources info)
                      extra  = case maybeInstantiatedTypeScheme info of
                                  Just scheme -> -- overloaded function
                                     Left (scheme, snd $ typepair info)
                                  Nothing -> --overloaded language construct
                                     Right (location info, sub |-> assignedType (attribute (localInfo info)))
                      pred' = let err = internalError "ConstraintInfo" "makeTypeErrors" 
                                                       "unknown predicate which resulted in a reduction error"
                               in maybe (fromMaybe err $ maybeReductionErrorPredicate info) fst maybeNever
                  in maybe (special info (sub |-> makeReductionError source extra classEnv pred'))
                        (\m -> TypeError [rangeOfSource source] ([MessageOneLiner $ MessageString m]) [] []) customMessage
           in (4, map f infos)     
  
      -- ambiguous class predicates
      | label == ambiguousLabel =
           let f info = 
                  let scheme1   = fromMaybe err (maybeInstantiatedTypeScheme info)
                      scheme2   = generalizeAll ([] .=>. sub |->  fst (typepair info))
                      className = maybe err (\(Predicate x _) -> x) (maybeReductionErrorPredicate info)
                      err       = internalError "ConstraintInfo" "makeTypeErrors" "unknown original type scheme"
                  in special info (makeUnresolvedOverloadingError (fst $ sources info) className (scheme1, scheme2))
           in (5, map f infos)
      | label == disjointLabel = 
            let f info = let 
                        source1 = fst $ sources i1
                        source2 = fst $ sources i2
                        msg = fromMaybe err $ maybeCustomError info
                        err = internalError "ConstraintInfo" "makeTypeErrors" "Unknown disjoint directive in directive error" 
                        tab =  [ "predicate" <:> MessageString n1
                                , "disjoint from" <:> MessageString n2
                                ]
                        ((n1, i1),(n2, i2)) = fromMaybe err (maybeDisjointDirective info)
                    in TypeError [rangeOfSource source1, rangeOfSource source2] [MessageOneLiner $ MessageString msg] tab []
            in (6, map f infos)
      | otherwise = 
           internalError "ConstraintInfo" "makeTypeErrors" ("unknown label "++show label)

makeUnificationTypeError :: ConstraintInfo -> TypeError
makeUnificationTypeError info =
   let (source, term) = sources info
       range    = maybe (rangeOfSource source) rangeOfSource term
       oneliner = MessageOneLiner (MessageString ("Type error in " ++ location info))
       (t1, t2) = typepair info 
       msgtp1   = fromMaybe (toTpScheme t1) (maybeInstantiatedTypeScheme info)
       msgtp2   = maybe (toTpScheme t2) snd (maybeSkolemizedTypeScheme info)
       (reason1, reason2)   
          | isJust (maybeSkolemizedTypeScheme info) = ("inferred type", "declared type")
          | isFolkloreConstraint info               = ("type"         , "expected type")
          | otherwise                                = ("type"         , "does not match")
       table = [ s <:> MessageOneLineTree (oneLinerSource source') | (s, source') <- convertSources (sources info)] 
               ++
               [ reason1 >:> MessageType msgtp1
               , reason2 >:> MessageType msgtp2
               ]
       hints      = [ hint | WithHint hint <- properties info ]
  in TypeError [range] [oneliner] table hints
  
-------------------------------------
-- from the type inference directives

emptyConstraintInfo :: ConstraintInfo
emptyConstraintInfo =
   CInfo_ { location   = "Typing Strategy"
          , sources    = (UHA_Decls [], Nothing)
          , localInfo  = root (LocalInfo (UHA_Decls []) Nothing []) []
          , properties = []
          , errorMessage = Nothing
          }
         
defaultConstraintInfo :: (UHA_Source, Maybe UHA_Source) -> ConstraintInfo
defaultConstraintInfo sourceTuple@(s1, s2) =
   CInfo_ { location   = descriptionOfSource theSource -- not very precise: expression, pattern, etc.
          , sources    = sourceTuple
          , localInfo  = root myLocal []
          , properties = []
          , errorMessage = Nothing
          }
 where myLocal   = LocalInfo {self = theSource, assignedType = Nothing, monos = []}
       theSource = fromMaybe s1 s2

standardConstraintInfo :: ConstraintInfo
standardConstraintInfo =
   CInfo_ { location   = "Typing Strategy"
          , sources    = (UHA_Decls [], Nothing)
          , localInfo  = root myLocal []
          , properties = [ ]
          , errorMessage = Nothing
          }
 where myLocal = LocalInfo {self = UHA_Decls [], assignedType = Nothing, monos = []}
 
maybeSpecialTypeError :: ConstraintInfo -> Maybe TypeError
maybeSpecialTypeError = errorMessage 

setTypeError :: TypeError -> ConstraintInfo -> ConstraintInfo
setTypeError typeError info = 
   info { errorMessage = Just typeError }
