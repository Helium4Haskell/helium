module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Syntax (Declaration(Declaration_TypeFam))
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Debug.Trace

--------------------------------------
-- Declaration static checks
type DeclInfo = [(Name, Bool, Names, Names)]
type InstanceInfo = [(Name, Types, Type)]

-- Checks if a declaration does not have variables with identical names.
declNoIndenticalVars :: Declaration -> Errors
declNoIndenticalVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) _ _) = let

  createPairs :: Show a => [a] -> [(a, a)]
  createPairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

  tails [] = []
  tails (x:xs) = (x:xs) : tails xs
  

  in [Duplicated Variable [n1, n2] | (n1, n2) <- createPairs  tv, n1 == n2]
declNoIndenticalVars _ = []

-- Check the injectivity variables (both result var and injectively defined vars)
declInjectivityVars :: Declaration -> Errors 
declInjectivityVars (Declaration_TypeFam _ _ MaybeInjectivity_Nothing  _)   = []
declInjectivityVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) (MaybeInjectivity_Just inj) _) = let
  (Injectivity_Injectivity declres res injargs) = inj

  in [Undefined Variable res [declres] ["The result variable in the injectivity annotation is not defined!"] | res /= declres] ++
     [Undefined Variable x tv [] | x <- injargs, x `notElem` tv] 
declInjectivityVars _ = []

-- Check whether duplicate type families exist.
declCheckDuplicates :: DeclInfo -> Errors 
declCheckDuplicates tfs = let

  createNamePairs xs = [(n1, n2) | ((n1, _, _, _):ys) <- tails xs, (n2, _, _, _) <- ys]

  tails [] = []
  tails (x:xs) = (x:xs) : tails xs

  in [DuplicateTypeFamily (n1, n2) | (n1, n2) <- createNamePairs tfs, n1 == n2]
--------------------------------------
-- Associated Typesynonym check (variable alignment)
atsCheckVarAlignment :: DeclInfo -> Errors 
atsCheckVarAlignment = undefined

--------------------------------------
-- Instance checks

instCheckDeclExists :: DeclInfo -> InstanceInfo -> Errors
instCheckDeclExists ds is = let

  getUndefinedNames = [n1 | (n1, _, _) <- is, all (\(n2, _, _, _) -> n1 /= n2 ) ds]
  ns = map (\(n, _, _, _) -> n) ds
  
  in [UndefinedTypeFamily n ns | n <- getUndefinedNames]