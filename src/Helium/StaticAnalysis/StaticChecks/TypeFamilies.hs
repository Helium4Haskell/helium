module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Debug.Trace
import GHC.Conc (disableAllocationLimit)


type TFDeclInfos = [TFDeclInfo]
data TFDeclInfo
  = DOpen Name Names (Maybe Names)
  | DClosed Name Names (Maybe Names)
  | DAssoc Name Names (Maybe Names) [(Int, Int)]

type TFInstanceInfos = [TFInstanceInfo]
data TFInstanceInfo
  = IOpen Name Types Type
  | IClosed Name Types Type
  | IAssoc Name Types Type Types Name

obtainDeclNames :: TFDeclInfo -> Name
obtainDeclNames (DOpen n _ _)    = n
obtainDeclNames (DClosed n _ _)  = n
obtainDeclNames (DAssoc n _ _ _) = n

obtainInstanceNames :: TFInstanceInfo -> Name
obtainInstanceNames (IOpen n _ _)      = n
obtainInstanceNames (IClosed n _ _)    = n
obtainInstanceNames (IAssoc n _ _ _ _) = n
--------------------------------------
-- Declaration static checks, SEPARATE CHECKS

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

------------------------------------------------------------------
checkTypeFamStaticErrors :: TFDeclInfos -> TFInstanceInfos -> Errors
checkTypeFamStaticErrors dis iis =
     declCheckDuplicates dis
  ++ atsCheckVarAlignment dis iis
  ++ instCheckDeclExists dis iis
  ++ instSaturationCheck dis iis

-- Check whether duplicate type families exist.
declCheckDuplicates :: TFDeclInfos -> Errors
declCheckDuplicates tfs = let

  obtainNames :: TFDeclInfo -> Name
  obtainNames (DOpen n _ _) = n
  obtainNames (DClosed n _ _) = n
  obtainNames (DAssoc n _ _ _) = n

  createNamePairs xs = [(n1, n2) | (n1:ys) <- tails (map obtainNames xs), n2 <- ys]

  tails [] = []
  tails (x:xs) = (x:xs) : tails xs

  in [DuplicateTypeFamily (n1, n2) | (n1, n2) <- createNamePairs tfs, n1 == n2]

--------------------------------------
-- Associated Typesynonym check (variable alignment)
atsCheckVarAlignment :: TFDeclInfos -> TFInstanceInfos -> Errors
atsCheckVarAlignment decls insts = let

  convertedInsts = [(instn, itfn, map (typeToMonoType []) its, map (typeToMonoType []) tfts) | (IAssoc itfn tfts _ its instn) <- insts]

  violations = [(itfn, instn, thrd (its !! ci), thrd (tfts !! tfi)) |
                (DAssoc tfdn _ _ idxs) <- decls, -- Get a decl
                (ci, tfi) <- idxs, -- obtain alignment info
                (instn, itfn,  its, tfts) <- convertedInsts, -- Get an inst
                tfdn == itfn, -- instance and decl names must be equal 
                thrd (its !! ci) /= thrd (tfts !! tfi)] -- Then types at indices must be equal.

  thrd (_, _, z) = z

  in [WronglyAlignedATS n1 n2 t1 t2 | (n1, n2, t1, t2) <- violations]

--------------------------------------
-- Instance checks

instCheckDeclExists :: TFDeclInfos -> TFInstanceInfos -> Errors
instCheckDeclExists ds is = let

  getUndefinedNames = [n1 | n1 <- map obtainInstanceNames is, notElem n1 $ map obtainDeclNames ds]
  ns = map obtainDeclNames ds

  in [UndefinedTypeFamily n ns | n <- getUndefinedNames]

instSaturationCheck :: TFDeclInfos -> TFInstanceInfos -> Errors
instSaturationCheck ds is = let

  getNameArgs :: TFDeclInfo -> (Name, Names)
  getNameArgs (DOpen n ns _)     = (n, ns)
  getNameArgs (DClosed n ns _)   = (n, ns)
  getNameArgs (DAssoc n ns _ _ ) = (n, ns)

  getNameTypes :: TFInstanceInfo -> (Name, Types)
  getNameTypes (IOpen n ts _)    = (n, ts)
  getNameTypes (IClosed n ts _ ) = (n, ts)
  getNameTypes (IAssoc n ts _ _ _) = (n, ts)

  violations = [(n2, length ns, length ts) | (n1, ns) <- map getNameArgs ds, (n2, ts) <- map getNameTypes is, n1 == n2, length ns /= length ts]

  in [WronglySaturatedTypeFamily n dl tl | (n, dl, tl) <- violations]

-- CHECKS TODO!!!!!:
-- Occurscheck of variables
--
-- Definition smaller check (For non-injective)
-- - Injective type fams
--    - Definition no type family or bare variable check
--    - Pre-unification
--    - Basically, the injectivity check from paper.