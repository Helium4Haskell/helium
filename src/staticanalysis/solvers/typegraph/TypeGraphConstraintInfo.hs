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

type InfoSource = (InfoNT,InfoAlt,String) 
           
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
   


class (Show constraintinfo,ConstraintInfo constraintinfo) => 
         TypeGraphConstraintInfo constraintinfo where 
             
   getInfoSource           :: constraintinfo -> InfoSource
   getPosition             :: constraintinfo -> Maybe Int
   getTrustFactor          :: constraintinfo -> Maybe Int 
   getConstraintPhaseNumber :: constraintinfo -> Maybe Int 
   isFolkloreConstraint    :: constraintinfo -> Bool
   isExplicitTypedBinding  :: constraintinfo -> Bool
   isTupleEdge             :: constraintinfo -> Bool
   maybeApplicationEdge    :: constraintinfo -> Maybe (Bool,[(Tree,Tp)])
   maybeImportedFunction   :: constraintinfo -> Maybe Name
   getTwoTypes             :: constraintinfo -> (Tp,Tp)
   maybeLiteral            :: constraintinfo -> Maybe Literal
   maybeNegation           :: constraintinfo -> Maybe Int
   getSize                 :: constraintinfo -> Maybe Int
   isNegationResult        :: constraintinfo -> Bool
   maybeFunctionBinding    :: constraintinfo -> Maybe Int   
   maybeOriginalTypeScheme :: constraintinfo -> Maybe (Bool,TpScheme)
   setFolkloreConstraint   :: constraintinfo -> constraintinfo 
   setNewTypeError         :: TypeError -> constraintinfo -> constraintinfo
   setNewHint              :: TypeErrorInfo -> constraintinfo -> constraintinfo
   makeTypeError           :: constraintinfo -> TypeError
  
-- not a nice solution!  
makeTypeErrorForTerm :: TypeGraphConstraintInfo constraintinfo => Tree -> (Tp,Tp) -> constraintinfo -> TypeError
makeTypeErrorForTerm termOneLiner (t1, t2) cinfo = 
   case makeTypeError cinfo of
   
      TypeError range oneliner (UnificationErrorTable sources _ _) infos -> 
         let newSources = filter onlyExpression sources ++ [("Term", termOneLiner)]
             onlyExpression = ("Expression"==) . fst
         in TypeError range oneliner (UnificationErrorTable newSources (Left t1) (Left t2)) infos 
         
      typeError -> typeError
