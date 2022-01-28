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
  | DAssoc Name Names (Maybe Names) [(Int, Int)] Name

type TFInstanceInfos = [TFInstanceInfo]
data TFInstanceInfo
  = IOpen Name Types Type
  | IClosed Name Types Type
  | IAssoc Name Types Type Types Name

obtainDeclNames :: TFDeclInfo -> Name
obtainDeclNames (DOpen n _ _)      = n
obtainDeclNames (DClosed n _ _)    = n
obtainDeclNames (DAssoc n _ _ _ _) = n

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
-- STATIC CHECKS OVER ALL KNOWN DECLARATIONS AND INSTANCES
checkTypeFamStaticErrors :: TFDeclInfos -> TFInstanceInfos -> Errors
checkTypeFamStaticErrors dis iis = let
     
  phase1 = declCheckDuplicates dis
           ++ atsCheckVarAlignment dis iis
           ++ instCheckInstanceValidity dis iis
           ++ instSaturationCheck dis iis
  
  phase2 = []
  in if not (null phase1)
        then phase1
        else phase2

-- Check whether duplicate type families exist.
declCheckDuplicates :: TFDeclInfos -> Errors
declCheckDuplicates tfs = let

  obtainNames :: TFDeclInfo -> Name
  obtainNames (DOpen n _ _)      = n
  obtainNames (DClosed n _ _)    = n
  obtainNames (DAssoc n _ _ _ _) = n

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
                (DAssoc tfdn _ _ idxs _) <- decls, -- Get a decl
                (ci, tfi) <- idxs, -- obtain alignment info
                (instn, itfn,  its, tfts) <- convertedInsts, -- Get an inst
                tfdn == itfn, -- instance and decl names must be equal 
                thrd (its !! ci) /= thrd (tfts !! tfi)] -- Then types at indices must be equal.

  thrd (_, _, z) = z

  in [WronglyAlignedATS n1 n2 t1 t2 | (n1, n2, t1, t2) <- violations]

--------------------------------------
-- Instance checks

instCheckInstanceValidity :: TFDeclInfos -> TFInstanceInfos -> Errors
instCheckInstanceValidity ds is = let

  getUndefinedNames = [n1 | n1 <- map obtainInstanceNames is, notElem n1 $ map obtainDeclNames ds]
  ns = map obtainDeclNames ds
  
  obtainOpenClosed (IOpen n _ _:ts)   = n : obtainOpenClosed ts
  obtainOpenClosed (IClosed n _ _:ts) = n : obtainOpenClosed ts
  obtainOpenClosed (_:ts)             = obtainOpenClosed ts
  obtainOpenClosed []                 = []

  obtainOpenAssoc (IOpen n _ _:ts)   = n : obtainOpenAssoc ts
  obtainOpenAssoc (IAssoc n _ _ _ _:ts) = n : obtainOpenAssoc ts
  obtainOpenAssoc (_:ts)                = obtainOpenAssoc ts
  obtainOpenAssoc []                    = []

  hasAssocTypeSyn cn n = case [ n1 | (DAssoc n1 _ _ _ cn1) <- ds, cn1 == cn, n == n1] of
                            [] -> False
                            _  -> True 

  -- Associated type synonym instance validities
  assocNotInClassInstance = [(n2, cn) | (DAssoc n1 _ _ _ cn) <- ds, n2 <- obtainOpenClosed is, n1 == n2]
  assocInstanceNotPartOfClass = [(n, cn) | (IAssoc n _ _ _ cn) <- is, not $ hasAssocTypeSyn cn n]
  assocNotLinkedToRightClass = [(n2, cn2, cn1) | (DAssoc n1 _ _ _ cn1) <- ds, (IAssoc n2 _ _ _ cn2) <- is, n1 == n2, cn1 /= cn2]

  -- Closed type synonym instance validities.
  openInstancesForClosed = [n2 | (DClosed n1 _ _) <- ds, n2 <- obtainOpenAssoc is, n1 == n2]

  in [UndefinedTypeFamily n ns | n <- getUndefinedNames] ++
     [ATSNotInInstance n cn | (n, cn) <- assocNotInClassInstance] ++
     [ATSWrongClassInstance n cn1 cn2 | (n, cn1, cn2) <- assocNotLinkedToRightClass] ++
     [ATSNotPartOfClass n1 n2 | (n1, n2) <- assocInstanceNotPartOfClass] ++
     [OpenInstanceForClosed n | n <- openInstancesForClosed]

instSaturationCheck :: TFDeclInfos -> TFInstanceInfos -> Errors
instSaturationCheck ds is = let

  getNameArgs :: TFDeclInfo -> (Name, Names)
  getNameArgs (DOpen n ns _)      = (n, ns)
  getNameArgs (DClosed n ns _)    = (n, ns)
  getNameArgs (DAssoc n ns _ _ _) = (n, ns)

  getNameTypes :: TFInstanceInfo -> (Name, Types)
  getNameTypes (IOpen n ts _)      = (n, ts)
  getNameTypes (IClosed n ts _ )   = (n, ts)
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