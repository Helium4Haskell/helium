-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeGraphConstraintInfo.hs : !!! CLEAN UP THIS CODE !!!!
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
             
   getInfoSource           :: constraintinfo -> InfoSource
   getPosition             :: constraintinfo -> Maybe Int
   getTrustFactor          :: constraintinfo -> Maybe Int
   getConstraintPhaseNumber :: constraintinfo -> Maybe Int 
   isFolkloreConstraint    :: constraintinfo -> Bool
   isExplicitTypedBinding  :: constraintinfo -> Bool
   isTupleEdge             :: constraintinfo -> Bool
   maybeApplicationEdge    :: constraintinfo -> Maybe (Bool, [(Tree, Tp, Range)])
   maybeImportedFunction   :: constraintinfo -> Maybe Name
   getTwoTypes             :: constraintinfo -> (Tp,Tp)
   maybeLiteral            :: constraintinfo -> Maybe Literal
   maybeNegation           :: constraintinfo -> Maybe Bool
   isNegationResult        :: constraintinfo -> Bool
   maybeFunctionBinding    :: constraintinfo -> Maybe Int
   maybeOriginalTypeScheme :: constraintinfo -> Maybe (Bool,TpScheme)
   maybeUserConstraint     :: constraintinfo -> Maybe (Int, Int)
   maybeUnifier            :: constraintinfo -> Maybe Int
   setFolkloreConstraint   :: constraintinfo -> constraintinfo
   setNewTypeError         :: TypeError -> constraintinfo -> constraintinfo
   setNewHint              :: TypeErrorInfo -> constraintinfo -> constraintinfo
   makeTypeError           :: constraintinfo -> TypeError
   getErrorRange           :: constraintinfo -> Range

   isPattern               :: constraintinfo -> Bool
   isPattern cinfo = let (nt, _, _, _) = getInfoSource cinfo 
                     in nt == NTPattern

-- not a nice solution!
makeTypeErrorForTerm :: TypeGraphConstraintInfo constraintinfo => (Bool,Bool) -> Int -> Tree -> (Tp,Tp) -> Range -> constraintinfo -> TypeError
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
             functionType = either MessageType MessageTypeScheme ftype
             subterm
                | isInfixApplication = if argumentNumber == 0 then "left operand" else "right operand"
                | otherwise          = ordinal False (argumentNumber + 1) ++ " argument"
         in TypeError range oneliner (UnificationErrorTable newSources (Left t1) (Left t2)) infos

      typeError -> typeError

-- Info source
type InfoSource = (InfoNT, InfoAlt, Int, String)
           
data InfoNT = NTBody              | NTDeclaration  | NTFunctionBinding | NTExpression 
            | NTGuardedExpression | NTPattern      | NTAlternative     | NTStatement
            | NTQualifier         | NTBindingGroup
   deriving (Show,Eq)
   
data InfoAlt = AltBody             | AltFunctionBindings | AltPatternBinding    | AltFunctionBinding
             | AltLiteral          | AltConstructor      | AltLet               | AltCase
             | AltLambda           | AltInfixApplication | AltDo                | AltIf 
             | AltEnum             | AltNegate           | AltTyped             | AltList 
             | AltComprehension    | AltTuple            | AltNormalApplication | AltGuardedExpression 
             | AltInfixConstructor | AltAs               | AltAlternative       | AltExpression             
             | AltGenerator        | AltGuard            | AltBindingGroup      | AltNegateFloat
   deriving (Show,Eq)
