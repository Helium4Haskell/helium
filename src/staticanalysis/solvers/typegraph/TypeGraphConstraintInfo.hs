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
   isFolkloreConstraint    :: constraintinfo -> Bool
   isTupleEdge             :: constraintinfo -> Bool
   maybeApplicationEdge    :: constraintinfo -> Maybe (Bool,[(Tree,Tp)])
   maybeImportedFunction   :: constraintinfo -> Maybe Name
   getTwoTypes             :: constraintinfo -> (Tp,Tp)
   maybeLiteral            :: constraintinfo -> Maybe Literal
   maybeNegation           :: constraintinfo -> Maybe Int
   getSize                 :: constraintinfo -> Maybe Int
   isExplicitTypedBinding  :: constraintinfo -> Bool
   isNegationResult        :: constraintinfo -> Bool
   maybeFunctionBinding    :: constraintinfo -> Maybe Int   
   maybeOriginalTypeScheme :: constraintinfo -> Maybe (Bool,TpScheme)
   setFolkloreConstraint   :: constraintinfo -> constraintinfo 
   setNewTypeError         :: TypeError -> constraintinfo -> constraintinfo
   setNewHint              :: Hint -> constraintinfo -> constraintinfo
   makeTypeError           :: constraintinfo -> TypeError
  
makeTypeErrorForTerm :: TypeGraphConstraintInfo constraintinfo => Tree -> (Tp,Tp) -> constraintinfo -> TypeError
makeTypeErrorForTerm oneLiner (t1,t2) cinfo = 
   let newsources = concatMap (\sd -> case sd of SD_Term _ -> [] ; _ -> [sd]) oldsources ++ [SD_Term oneLiner]
       TypeError fc lc ra oldsources oldpair h = makeTypeError cinfo
   in TypeError fc lc ra newsources (Nothing,t1,t2) h  
