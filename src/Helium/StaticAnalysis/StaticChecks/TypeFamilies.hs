module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Syntax (Declaration(Declaration_TypeFam))
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Debug.Trace

declNoIndenticalVars :: Declaration -> Errors
declNoIndenticalVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) _ _) = let

  createPairs :: Show a => [a] -> [(a, a)]
  createPairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

  tails [] = []
  tails (x:xs) = (x:xs) : tails xs
  

  in [Duplicated Variable [n1, n2] | (n1, n2) <- createPairs  tv, n1 == n2]
declNoIndenticalVars _ = []

declInjectivityVars :: Declaration -> Errors 
declInjectivityVars (Declaration_TypeFam _ _ MaybeInjectivity_Nothing  _)   = []
declInjectivityVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) (MaybeInjectivity_Just inj) _) = let
  (Injectivity_Injectivity declres res injargs) = inj

  in [Undefined Variable res [declres] ["The result variable in the injectivity annotation is not defined!"] | res /= declres] ++
     [Undefined Variable x tv [] | x <- injargs, x `notElem` tv] 
declInjectivityVars _ = []
