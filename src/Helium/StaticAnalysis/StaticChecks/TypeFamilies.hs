module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
import Debug.Trace
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
    ( isFamilyFree, MonoType (MonoType_Fam, MonoType_Var) )
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
    ( namesInType, namesInTypes )


type TFDeclInfos = [TFDeclInfo]
data TFDeclInfo
  = DOpen Name Names (Maybe Names)
  | DClosed Name Names (Maybe Names)
  | DAssoc Name Names (Maybe Names) [(Int, Int)] Name
  deriving Show

type TFInstanceInfos = [TFInstanceInfo]
data TFInstanceInfo
  = IOpen Name Types Type
  | IClosed Name Types Type Int --Int resembles the priority that the instance has in the closed type family
  | IAssoc Name Types Type Types Name
  deriving Show

-------------------------------------
-- UTILS

obtainDeclName :: TFDeclInfo -> Name
obtainDeclName (DOpen n _ _)      = n
obtainDeclName (DClosed n _ _)    = n
obtainDeclName (DAssoc n _ _ _ _) = n

obtainInstanceName :: TFInstanceInfo -> Name
obtainInstanceName (IOpen n _ _)      = n
obtainInstanceName (IClosed n _ _ _)  = n
obtainInstanceName (IAssoc n _ _ _ _) = n

thrd :: (a, b, c) -> c
thrd (_, _, z) = z

obtainTyFams :: TFDeclInfos -> [(String, Int)]
obtainTyFams (DAssoc n ns _ _ _:ts) = (show n, length ns) : obtainTyFams ts
obtainTyFams (DClosed n ns _:ts)    = (show n, length ns) : obtainTyFams ts
obtainTyFams (DOpen n ns _:ts)      = (show n, length ns) : obtainTyFams ts
obtainTyFams []                     = []

obtainArguments :: TFInstanceInfo -> Types
obtainArguments (IAssoc _ ts _ _ _) = ts
obtainArguments (IClosed _ ts _ _)  = ts
obtainArguments (IOpen _ ts _)      = ts

obtainDefinition :: TFInstanceInfo -> Type
obtainDefinition (IAssoc _ _ t _ _) = t
obtainDefinition (IClosed _ _ t _)  = t
obtainDefinition (IOpen _ _ t)      = t

isTFApplication :: MonoType -> Bool 
isTFApplication (MonoType_Fam _ _) = True 
isTFApplication _                  = False

isBareVariable :: MonoType -> Bool
isBareVariable (MonoType_Var _ _) = True
isBareVariable _                  = False

--------------------------------------
-- Declaration static checks, SEPARATE CHECKS

-- Checks if a declaration does not have variables with identical names.
declNoIndenticalVars :: Declaration -> Errors
declNoIndenticalVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) _ _) = let

  createPairs :: Show a => [a] -> [(a, a)]
  createPairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

  tails [] = []
  tails (x:xs) = (x:xs) : tails xs


  in [Duplicated Variable [n1, n2] | (n1, n2) <- createPairs tv, n1 == n2]
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
  
  phase2 = instNoTFInArgument dis iis
           ++ instVarOccursCheck iis
           ++ instInjDefChecks dis iis
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

  in [WronglyAlignedATS n1 n2 t1 t2 | (n1, n2, t1, t2) <- violations]

--------------------------------------
-- Instance checks

instCheckInstanceValidity :: TFDeclInfos -> TFInstanceInfos -> Errors
instCheckInstanceValidity ds is = let

  getUndefinedNames = [n1 | n1 <- map obtainInstanceName is, notElem n1 $ map obtainDeclName ds]
  ns = map obtainDeclName ds
  
  obtainOpenClosed :: TFInstanceInfos -> Names
  obtainOpenClosed (IOpen n _ _:ts)     = n : obtainOpenClosed ts
  obtainOpenClosed (IClosed n _ _ _:ts) = n : obtainOpenClosed ts
  obtainOpenClosed (_:ts)               = obtainOpenClosed ts
  obtainOpenClosed []                   = []

  obtainOpenAssoc :: TFInstanceInfos -> Names
  obtainOpenAssoc (IOpen n _ _:ts)      = n : obtainOpenAssoc ts
  obtainOpenAssoc (IAssoc n _ _ _ _:ts) = n : obtainOpenAssoc ts
  obtainOpenAssoc (_:ts)                = obtainOpenAssoc ts
  obtainOpenAssoc []                    = []

  hasAssocTypeSyn :: Name -> Name -> Bool
  hasAssocTypeSyn cn n = case [ n1 | (DAssoc n1 _ _ _ cn1) <- ds, cn1 == cn, n == n1] of
                            [] -> False
                            _  -> True 

  -- Associated type synonym instance validities
  assocNotInClassInstance = [(n2, cn) | (DAssoc n1 _ _ _ cn) <- ds, n2 <- obtainOpenClosed is, n1 == n2]
  assocInstanceNotPartOfClass = [(n, cn) | (IAssoc n _ _ _ cn) <- is, not $ hasAssocTypeSyn cn n, n `notElem` getUndefinedNames]
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
  getNameTypes (IClosed n ts _ _)   = (n, ts)
  getNameTypes (IAssoc n ts _ _ _) = (n, ts)

  violations = [(n2, length ns, length ts) | (n1, ns) <- map getNameArgs ds, (n2, ts) <- map getNameTypes is, n1 == n2, length ns /= length ts]

  in [WronglySaturatedTypeFamily n dl tl | (n, dl, tl) <- violations]

instNoTFInArgument :: TFDeclInfos -> TFInstanceInfos -> Errors
instNoTFInArgument dis tis = let

  violations = [ (obtainInstanceName inst, arg, thrd $ typeToMonoType (obtainTyFams dis) arg) |
                 inst <- tis
               , arg <- obtainArguments inst
               , not $ isFamilyFree $ thrd $ typeToMonoType (obtainTyFams dis) arg
               ]
  in [TFInArgument n t mt | (n, t, mt) <- violations] 

instVarOccursCheck :: TFInstanceInfos -> Errors
instVarOccursCheck tis = let

  getViolations :: TFInstanceInfo -> Names
  getViolations tfi = let
    argVars = namesInTypes $ obtainArguments tfi
    defVars = namesInType $ obtainDefinition tfi

    undefNames = [n | n <- defVars, n `notElem` argVars]
    in undefNames
    
  in [Undefined Variable n [] ["Variable " ++ show (show n) ++ " does not occur in any instance argument"] | n <- concatMap getViolations tis]

instSmallerChecks :: TFInstanceInfos -> Errors
instSmallerChecks tis = let
  x = 2
  in []

instInjDefChecks :: TFDeclInfos -> TFInstanceInfos -> Errors
instInjDefChecks dis tis = let

  isInjective :: TFDeclInfo -> TFInstanceInfo -> Bool
  isInjective (DAssoc n1 _ (Just _) _ _) (IAssoc n2 _ _ _ _) = n1 == n2
  isInjective (DClosed n1 _ (Just _))    (IClosed n2 _ _ _)  = n1 == n2
  isInjective (DOpen n1 _ (Just _))      (IOpen n2 _ _)      = n1 == n2
  isInjective _                          _                   = False

  tyFams = obtainTyFams dis

  injInsts = [inst | inst <- tis, decl <- dis, isInjective decl inst]
  tyFamDef = [ obtainInstanceName inst | 
               inst <- injInsts
             , isTFApplication (thrd $ typeToMonoType tyFams (obtainDefinition inst))]
  bareVars = [ (obtainInstanceName inst, filter (not . isBareVariable) (map (thrd . typeToMonoType tyFams) (obtainArguments inst))) |
               inst <- injInsts
             , isBareVariable (thrd $ typeToMonoType tyFams (obtainDefinition inst))
             , not $ all (isBareVariable . thrd . typeToMonoType tyFams) (obtainArguments inst)]
  in [InjTFInDefinition n | n <- tyFamDef] ++
     [InjBareVarInDefinition n ns | (n, ns) <- bareVars]
-- CHECKS TODO!!!!!:
-- Type is smaller Checks!
--
-- Definition smaller check (For non-injective)
-- - Injective type fams
--    - Definition no type family or bare variable check
--    - Pre-unification
--    - Basically, the injectivity check from paper.