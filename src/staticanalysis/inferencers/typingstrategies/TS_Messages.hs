module TS_Messages where

import Messages
import HeliumConstraintInfo
import Types
import UHA_Syntax

type TS_Errors = [TS_Error]
data TS_Error 
      = InconsistentConstraint String {- rule name -} HeliumConstraintInfo
      | UndefinedTS String {- rule name -} Name {- variable/constructor -} Entity
      | UnusedMetaVariable String {- rule name -} String {- metavariable -}
      | TypeErrorTS String TypeError      
      | Soundness String {- rule name -} TpScheme {- inferredTpScheme -} TpScheme {- constraintsTpScheme -}
             
type TS_Warnings = [TS_Warning]
data TS_Warning

instance IsMessage TS_Error where
   getRanges _ = []
   
   display (InconsistentConstraint rule hci) =
      let (t1,t2) = typepair hci
      in "Error in type strategy rule "++show rule++": "++
         "the given constraint set was inconsistent while solving the constraint "++
         show t1++" == "++show t2

   display (UndefinedTS rule name entity) =
      "Undefined "++show entity++" "++show name++" in type strategy rule "++show rule

   display (UnusedMetaVariable rule metavariable) =
      "Unused meta-variable "++show metavariable++" in type strategy rule "++show rule

   display (TypeErrorTS rule typeError) =
      "Type error in type strategy rule "++show rule++" while inferring the type of the conclusion:\n" ++
      display typeError

   display (Soundness rule inferred strategy) =
      "The Strategy rule "++show rule++" is not sound:\n" ++
      "*** strategy rule   : "++show strategy++"\n" ++
      "*** type inferencer : "++show inferred++"\n"
      
   display _   = "<TS_Error>"
   
instance IsMessage TS_Warning where
   getRanges _ = []
   display _   = "<TS_Warning>"
