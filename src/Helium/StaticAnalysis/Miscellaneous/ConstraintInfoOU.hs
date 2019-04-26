{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{-| Module      :  ConstraintInfo
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    The information that is stored with each type constraint that is constructed
	during type inference.
-}

module Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU where

import Helium.Main.Args (Option(..))

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.Syntax.UHA_Range
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Messages.HeliumMessages
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.StaticAnalysis.Miscellaneous.TypeConstraints
import Helium.Utils.Utils (internalError)
import Helium.Utils.OneLiner
import Helium.ModuleSystem.ImportEnvironment 

import Rhodium.Core
import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.Graph
import Rhodium.Blamer.HeuristicProperties
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes

import Data.Typeable
import Data.Data
import Data.Maybe
import Data.Function
import Data.List
import qualified Data.Map as M

import Control.Applicative

import Unbound.LocallyNameless hiding (Name)
import Unbound.LocallyNameless.Fresh

import Debug.Trace
 
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

maybeReductionErrorPredicate :: HasProperties a => a -> Maybe Constraint
maybeReductionErrorPredicate a = 
    maybeHead [ p | ReductionErrorInfo p <- getProperties a ]

isFolkloreConstraint :: HasProperties a => a -> Bool
isFolkloreConstraint a = 
   not $ null [ () | FolkloreConstraint <- getProperties a ]

-- |Returns only type schemes with at least one quantifier
maybeInstantiatedTypeScheme :: HasProperties a => a -> Maybe PolyType
maybeInstantiatedTypeScheme a =
   maybeHead [ s | InstantiatedTypeScheme s <- getProperties a, undefined ] -- not (withoutQuantors s) ]
   
maybeSkolemizedTypeScheme :: HasProperties a => a -> Maybe ([MonoType], PolyType)
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

maybeExplicitTypedDefinition :: HasProperties a => a -> Maybe ([MonoType], Name)
maybeExplicitTypedDefinition a =
   maybeHead [ (ms, n) | ExplicitTypedDefinition ms n <- getProperties a ]

maybeTypeSignatureLocation :: HasProperties a => a -> Maybe Range
maybeTypeSignatureLocation a =
   maybeHead [ r | TypeSignatureLocation r <- getProperties a ]

maybePredicateArisingFrom :: HasProperties a => a -> Maybe (Constraint, ConstraintInfo)
maybePredicateArisingFrom a =
   maybeHead [ t | PredicateArisingFrom t <- getProperties a ]
      
getEscapedSkolems :: HasProperties a => a -> [Int]
getEscapedSkolems a =
   concat [ is | EscapedSkolems is <- getProperties a ]
         

maybeMissingConcreteInstance :: HasProperties a => a -> Maybe (String, MonoType)
maybeMissingConcreteInstance a = 
   maybeHead [ (s, m) | MissingConcreteInstance s m <- getProperties a]

maybeAddConstraintToTypeSignature :: HasProperties a => a -> Maybe (Maybe (Constraint, EdgeId, ConstraintInfo), Constraint)
maybeAddConstraintToTypeSignature a = 
   maybeHead [ (m, cs) | AddConstraintToTypeSignature m cs <- getProperties a]

maybeClassUsages :: HasProperties a => a -> Maybe [(Constraint, EdgeId, ConstraintInfo)]
maybeClassUsages a = 
   maybeHead [ m | ClassUsages m <- getProperties a]

maybeRelevantFunctionBinding :: HasProperties a => a -> Maybe Constraint
maybeRelevantFunctionBinding a = 
   maybeHead [ m | RelevantFunctionBinding m <- getProperties a]

maybeAmbigiousClass :: HasProperties a => a -> Maybe Constraint
maybeAmbigiousClass a = 
   maybeHead [ c | AmbigiousClass c <- getProperties a]

isFromGadt :: HasProperties a => a -> Bool
isFromGadt a = not $ null [ () | FromGADT <- getProperties a ] 

isGADTPatternApplication :: HasProperties a => a -> Bool
isGADTPatternApplication a = not $ null [ () | GADTPatternApplication <- getProperties a ] 

maybeUnreachablePattern :: HasProperties a => a -> Maybe (MonoType, MonoType)
maybeUnreachablePattern a =
   maybeHead [ (m1, m2) | UnreachablePattern m1 m2 <- getProperties a ]

maybePatternMatch :: HasProperties a => a -> Maybe (TyVar, Int, Maybe Constraint)
maybePatternMatch a =
   maybeHead [ (v, i, mc) | PatternMatch v i mc <- getProperties a]

isPatternMatch :: Property -> Bool
isPatternMatch (PatternMatch _ _ _) = True
isPatternMatch _ = False

maybePossibleTypeSignature :: HasProperties a => a -> Maybe PolyType
maybePossibleTypeSignature a =
   maybeHead [ pt | PossibleTypeSignature pt <- getProperties a]
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
         , localInfo  = root LocalInfo { self = theSource, assignedType = Nothing} []
         , properties = theProperties
         , errorMessage = Nothing
         }               
        
cinfoBindingGroupExplicitTypedBinding :: [MonoType] -> Name -> Name ->  ImportEnvironment -> ConstraintInfo
cinfoSameBindingGroup                 :: Name ->                 ConstraintInfo
cinfoBindingGroupImplicit             :: Name ->                 ConstraintInfo
cinfoBindingGroupExplicit             :: [MonoType] -> Names -> Name -> ImportEnvironment -> ConstraintInfo
cinfoGeneralize                       :: Name ->                 ConstraintInfo

cinfoBindingGroupExplicitTypedBinding ms name nameTS importEnv = 
   let props = [ FromBindingGroup, ExplicitTypedBinding, ExplicitTypedDefinition ms name, 
                 HasTrustFactor 10.0, TypeSignatureLocation (getNameRange nameTS) ] ++
            [IsImported name | let ns = M.keys (valueConstructors importEnv) ++ M.keys (typeEnvironment importEnv), name `elem` ns]
   in variableConstraint "explicitly typed binding" (nameToUHA_Def name) props
cinfoSameBindingGroup name = 
   let props = [ FromBindingGroup, FolkloreConstraint ]
   in variableConstraint "variable" (nameToUHA_Expr name) props
cinfoBindingGroupImplicit name = 
   let props = [ FromBindingGroup, FolkloreConstraint, HasTrustFactor 10.0 ]
   in variableConstraint "variable" (nameToUHA_Expr name) props
cinfoBindingGroupExplicit ms defNames name importEnv = 
   let props1 = [ FromBindingGroup, FolkloreConstraint ]
       props2 = case filter (name==) defNames of
                   [defName] -> [ExplicitTypedDefinition ms defName]
                   _         -> []
   in variableConstraint "variable" (nameToUHA_Expr name) (props1 ++ props2 ++ 
      [IsImported name | let ns = M.keys (valueConstructors importEnv) ++ M.keys (typeEnvironment importEnv), name `elem` ns]
   )
cinfoGeneralize name =
   variableConstraint ("Generalize " ++ show name) (nameToUHA_Expr name) []

     
highlyTrustedFactor :: Float
highlyTrustedFactor = 10000.0

highlyTrusted :: Property
highlyTrusted = HasTrustFactor highlyTrustedFactor

isHighlyTrusted :: ConstraintInfo -> Bool
isHighlyTrusted info = 
   product [ i | HasTrustFactor i <- properties info ] >= highlyTrustedFactor

setTypePair :: (MonoType, MonoType) -> ConstraintInfo -> ConstraintInfo
setTypePair pair = addProperty (TypePair pair)

typepair :: ConstraintInfo -> (MonoType, MonoType)
typepair info = fromJust (maybeHead [ pair | TypePair pair <- getProperties info ])

isExprTyped :: ConstraintInfo -> Bool
isExprTyped info = 
   case fst (sources info) of
      UHA_Expr (Expression_Typed _ _ _) -> True
      _                                 -> False     
  
-------------------------------------
-- from the type inference directives

emptyConstraintInfo :: ConstraintInfo
emptyConstraintInfo =
   CInfo_ { location   = "Typing Strategy"
          , sources    = (UHA_Decls [], Nothing)
          , localInfo  = root (LocalInfo (UHA_Decls []) Nothing) []
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
 where myLocal   = LocalInfo {self = theSource, assignedType = Nothing}
       theSource = fromMaybe s1 s2

standardConstraintInfo :: ConstraintInfo
standardConstraintInfo =
   CInfo_ { location   = "Typing Strategy"
          , sources    = (UHA_Decls [], Nothing)
          , localInfo  = root myLocal []
          , properties = [ ]
          , errorMessage = Nothing
          }
 where myLocal = LocalInfo {self = UHA_Decls [], assignedType = Nothing}
 
maybeSpecialTypeError :: ConstraintInfo -> Maybe TypeError
maybeSpecialTypeError = errorMessage 

setTypeError :: TypeError -> ConstraintInfo -> ConstraintInfo
setTypeError typeError info = 
   info { errorMessage = Just typeError }

functionSpineP :: Fresh m => PolyType -> m ([MonoType], MonoType)
functionSpineP (PolyType_Bind _ b) = unbind b >>= functionSpineP . snd
functionSpineP (PolyType_Mono _ m) = return (functionSpine m)

-- |Returns the right spine of a function type. For instance,
-- if type @t@ is @Int -> (Bool -> String)@, then @functionSpine t@
-- is @([Int,Bool],String)@.
functionSpine :: MonoType -> ([MonoType],MonoType)
functionSpine = rec' [] where
   rec' tps (MonoType_App (MonoType_App (MonoType_Con "->") t1) t2) = rec' (t1:tps) t2
   rec' tps tp                              = (reverse tps,tp)


arityOfMonoType :: MonoType -> Int
arityOfMonoType = length . fst . functionSpine

arityOfPolyType :: Fresh m => PolyType -> m Int
arityOfPolyType x = length . fst <$> functionSpineP x

-- |Returns the right spine of a function type of a maximal length.
functionSpineOfLength :: Int -> MonoType -> ([MonoType], MonoType)
functionSpineOfLength i tp = 
   let (as, a ) = functionSpine tp
       (bs, cs) = splitAt i as
   in (bs, foldr (:-->:) a cs)

modCi :: (ConstraintInfo -> ConstraintInfo) -> Constraint -> Constraint
modCi f (Constraint_Unify m1 m2 ci) = (Constraint_Unify m1 m2 (f <$> ci))
modCi f (Constraint_Inst m1 m2 ci) = (Constraint_Inst m1 m2 (f <$> ci))

  
isTupleConstructor :: String -> Bool
isTupleConstructor ('(':[]) = False
isTupleConstructor ('(':cs) = all (','==) (init cs) && last cs == ')'
isTupleConstructor _        = False



leftSpine :: MonoType -> (MonoType,[MonoType])
leftSpine = rec' [] 
   where
      rec' tps (MonoType_App t1 t2) = rec' (t2:tps) t1
      rec' tps tp           = (tp,tps)

class IsFunctionBinding a where
   isExplicitlyTyped    :: a -> Bool
   maybeFunctionBinding :: a -> Maybe Int

instance IsFunctionBinding ConstraintInfo where
   isExplicitlyTyped cinfo = 
      or [ True | ExplicitTypedBinding <- properties cinfo ]
      
   maybeFunctionBinding cinfo = 
      case [ t | FuntionBindingEdge t <- properties cinfo ] of
         []  -> Nothing
         t:_ -> Just t    

