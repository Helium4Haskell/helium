-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
------------------------------------------------------------------------------

module TypeGraphConstraintInfo where

import UHA_Syntax
import Types
import ConstraintInfo
import OneLiner
import TypeErrors
import Messages
import Utils         (internalError)

class (Show constraintinfo,ConstraintInfo constraintinfo) => 
         TypeGraphConstraintInfo constraintinfo where
          
   getPosition                  :: constraintinfo -> Maybe Int
   getTrustFactor               :: constraintinfo -> Float 
   getConstraintPhaseNumber     :: constraintinfo -> Maybe Int 
   isFolkloreConstraint         :: constraintinfo -> Bool
   isExplicitTypedBinding       :: constraintinfo -> Bool
   isTupleEdge                  :: constraintinfo -> Bool
   maybeApplicationEdge         :: constraintinfo -> Maybe (Bool, [(OneLineTree, Tp, Range)]) 
   maybeImportedFunction        :: constraintinfo -> Maybe Name
   getTwoTypes                  :: constraintinfo -> (Tp,Tp)
   maybeLiteral                 :: constraintinfo -> Maybe Literal
   maybeNegation                :: constraintinfo -> Maybe Bool
   isNegationResult             :: constraintinfo -> Bool
   maybeFunctionBinding         :: constraintinfo -> Maybe Int
   maybeUserConstraint          :: constraintinfo -> Maybe (Int, Int)
   maybeUnifier                 :: constraintinfo -> Maybe Int
   setFolkloreConstraint        :: constraintinfo -> constraintinfo
   setNewTypeError              :: TypeError -> constraintinfo -> constraintinfo
   setNewHint                   :: TypeErrorInfo -> constraintinfo -> constraintinfo
   makeTypeError                :: constraintinfo -> TypeError
   isPattern                    :: constraintinfo -> Bool
   isEmptyInfixApplication      :: constraintinfo -> Bool
   isReductionErrorInfo         :: constraintinfo -> Bool
   maybeReductionErrorPredicate :: constraintinfo -> Maybe Predicate
   isExprVariable               :: constraintinfo -> Bool
   
-- not a nice solution!
makeTypeErrorForTerm :: TypeGraphConstraintInfo constraintinfo => (Bool,Bool) -> Int -> OneLineTree -> (Tp,Tp) -> Range -> constraintinfo -> TypeError
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
             functionType = either (\tp -> MessageType ([] :=> tp)) MessageTypeScheme ftype
             subterm
                | isInfixApplication = if argumentNumber == 0 then "left operand" else "right operand"
                | otherwise          = ordinal False (argumentNumber + 1) ++ " argument"
         in TypeError range oneliner (UnificationErrorTable newSources (Left t1) (Left t2)) infos

      typeError -> typeError