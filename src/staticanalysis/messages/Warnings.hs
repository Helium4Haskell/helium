-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Warnings.hs : ...
-- 
-------------------------------------------------------------------------------

module Warnings where

import UHA_Syntax
import Types
import Messages
import UHA_Utils    (getNameRange)
import Utils        (internalError)

-------------------------------------------------------------
-- (Static) Warnings

type Warnings = [Warning]
data Warning  = NoTypeDef Name TpScheme Bool
              | Shadow Name Name
              | Unused Entity Name {- toplevel or not -} Bool
              | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}

instance HasMessage Warning where
   getMessage x = [MessageOneLiner (showWarning x)]
   getRanges warning = case warning of
      NoTypeDef name _ _            -> [getNameRange name]
      Shadow _ name                 -> [getNameRange name]
      Unused _ name _               -> [getNameRange name]
      SimilarFunctionBindings n1 n2 -> [getNameRange n1, getNameRange n2]
      _                             -> internalError "Messages.hs" 
                                                      "instance IsMessage Warning" 
                                                      "unknown type of Warning"

showWarning :: Warning -> MessageBlock
showWarning warning = case warning of

   NoTypeDef name tpscheme topLevel ->
      MessageString ("Missing type signature: " ++ show name ++ " :: "++show tpscheme)

   Shadow shadowee shadower ->
      MessageString ("Variable " ++ show (show shadower) ++
                     " shadows the one at " ++
                     showPosition (getNameRange shadowee))

   Unused entity name toplevel ->
      MessageString (capitalize (show entity) ++ " " ++ show (show name) ++ " is not used")
    
   SimilarFunctionBindings suspect witness ->
      let [n1, n2] = sortNamesByRange [suspect, witness] 
      in MessageString ("Suspicious adjacent functions "++ show (show n1) ++ " and " ++ show (show n2))
   
   _ -> internalError "Messages" "showWarning" "unknown type of Warning"
   

makeUnused :: Entity -> Names -> Bool -> [Warning]
makeUnused entity names toplevel = [ Unused entity name toplevel | name <- names ]   
