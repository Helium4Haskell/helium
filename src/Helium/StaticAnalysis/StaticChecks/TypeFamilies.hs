module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Debug.Trace


type DeclInfo = [(Name, Bool, Names, Names)]
type InstanceInfo = [(Name, Types, Type)]

type ATSDeclInfo = [(Name, Name, [(Int, Int)])]
type ATSInstanceInfo = [(Name, Name, Types, Types)]
--------------------------------------
-- Declaration static checks

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
atsCheckVarAlignment :: ATSDeclInfo -> ATSInstanceInfo -> Errors 
atsCheckVarAlignment decls insts = let
  
  convertedInsts = [(instn, itfn, map (typeToMonoType []) its, map (typeToMonoType []) tfts) | (instn, itfn, its, tfts) <- insts]

  violations = [(itfn, instn, thrd (its !! ci), thrd (tfts !! tfi)) | 
                (_, tfdn, idxs) <- decls, -- Get a decl
                (ci, tfi) <- idxs, -- obtain alignment info
                (instn, itfn,  its, tfts) <- convertedInsts, -- Get an inst
                tfdn == itfn, -- instance and decl names must be equal 
                thrd (its !! ci) /= thrd (tfts !! tfi)] -- Then types at indices must be equal.
  
  thrd (_, _, z) = z

  in [WronglyAlignedATS n1 n2 t1 t2 | (n1, n2, t1, t2) <- violations]

--------------------------------------
-- Instance checks

instCheckDeclExists :: DeclInfo -> InstanceInfo -> Errors
instCheckDeclExists ds is = let

  getUndefinedNames = [n1 | (n1, _, _) <- is, all (\(n2, _, _, _) -> n1 /= n2 ) ds]
  ns = map (\(n, _, _, _) -> n) ds
  
  in [UndefinedTypeFamily n ns | n <- getUndefinedNames]

instSaturationCheck :: DeclInfo -> InstanceInfo -> Errors
instSaturationCheck ds is = let

  violations = [(n2, length ns, length ts) | (n1, _, ns, _) <- ds, (n2, ts, _) <- is, n1 == n2, length ns /= length ts]

  in [WronglySaturatedTypeFamily n dl tl | (n, dl, tl) <- violations]

-- CHECKS TODO!!!!!:
-- Occurscheck of variables
--
-- Definition smaller check (For non-injective)
-- - Injective type fams
--    - Definition no type family or bare variable check
--    - Pre-unification
--    - Basically, the injectivity check from paper.