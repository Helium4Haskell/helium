{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Helium.StaticAnalysis.StaticChecks.TypeFamilies where

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Miscellaneous.Unify
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
    ( typeToMonoType, tpToMonoType, importEnvironmentToTypeFamilies, TypeFamilies, tfInstanceInfoToAxiom, tfInstanceInfoToMonoTypes, typeSynonymsToTypeFamilies )
import Debug.Trace
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
    ( isFamilyFree, MonoType (MonoType_Fam, MonoType_Var, MonoType_Con, MonoType_App), MonoTypes, Axiom (Axiom_Unify), TyVar )
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
    ( namesInType, namesInTypes )
import Data.List (nub, elemIndex)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust, mapMaybe)
import Helium.Utils.Utils (internalError)
import Unbound.Generics.LocallyNameless (runFreshM)
import Top.Types (unquantify, split)
import Helium.ModuleSystem.ImportEnvironment ( TypeSynonymEnvironment )
import Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Fresh (FreshM)

-- Checks if a MonoType is as a whole a type family application
isTFApplication :: MonoType -> Bool 
isTFApplication (MonoType_Fam _ _) = True 
isTFApplication _                  = False

-- Checks if the MonoType is a bare variable
isBareVariable :: MonoType -> Bool
isBareVariable (MonoType_Var _ _) = True
isBareVariable _                  = False

-- Builds Injective environment.
buildInjectiveEnv :: TFDeclInfos -> InjectiveEnv
buildInjectiveEnv (DAssoc n ns ins _ _:dis) = M.insert (show n) (getInjIndices ns ins) $ buildInjectiveEnv dis
buildInjectiveEnv (DClosed n ns ins:dis)    = M.insert (show n) (getInjIndices ns ins) $ buildInjectiveEnv dis
buildInjectiveEnv (DOpen n ns ins:dis)      = M.insert (show n) (getInjIndices ns ins) $ buildInjectiveEnv dis
buildInjectiveEnv []                        = M.empty

getInjIndices :: Names -> Maybe Names -> [Int]
getInjIndices _  Nothing = []
getInjIndices ns (Just ins) = map (fromJust . flip elemIndex ins) ns

--------------------------------------
-- Declaration static checks, SEPARATE CHECKS

-- Checks if a declaration does not have variables with identical names.
declNoIndenticalVars :: Declaration -> Errors
declNoIndenticalVars (Declaration_TypeFam _ (SimpleType_SimpleType _ _ tv) _ _) 
  = [Duplicated Variable [n1, n2] | (n1, n2) <- createPairs tv, n1 == n2]
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
checkTypeFamStaticErrors :: TypeSynonymEnvironment -> TFDeclInfos -> TFInstanceInfos -> Errors
checkTypeFamStaticErrors env dis iis = let
  
  tyfams = typeSynonymsToTypeFamilies env ++ obtainTyFams dis

  phase1 = declCheckDuplicates dis
           ++ atsCheckVarAlignment dis iis
           ++ instCheckInstanceValidity dis iis
           ++ instSaturationCheck dis iis
  
  phase2 = instNoTFInArgument tyfams iis
           ++ instVarOccursCheck iis
           ++ instInjDefChecks tyfams dis iis
           ++ instSmallerChecks tyfams iis
           ++ compatibilityCheck tyfams iis
           ++ pairwiseInjChecks tyfams dis iis
  in if not (null phase1)
        then phase1
        else phase2

checkTypeFamWarnings :: TypeSynonymEnvironment -> TFDeclInfos -> TFInstanceInfos -> Warnings
checkTypeFamWarnings env dis tis = let
  tyfams = typeSynonymsToTypeFamilies env ++ obtainTyFams dis

  in closedOverlapWarning tyfams tis

-- Check whether duplicate type families exist.
declCheckDuplicates :: TFDeclInfos -> Errors
declCheckDuplicates tfs = let

  -- Creates all unique pairs of declaration names
  createNamePairs xs = [(n1, n2) | (n1:ys) <- tails (map obtainDeclName xs), n2 <- ys]

  in [DuplicateTypeFamily (n1, n2) | (n1, n2) <- createNamePairs tfs, n1 == n2]

--------------------------------------
-- Associated Typesynonym check (variable alignment)
atsCheckVarAlignment :: TFDeclInfos -> TFInstanceInfos -> Errors
atsCheckVarAlignment decls insts = let

  -- Converts all instances to a tuple containing (class instance name, tf instance name, monotypes of instance args, monotypes of tf instance args)
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

  
  ns = map obtainDeclName ds
  
  -- Obtains open and closed instances
  obtainOpenClosed :: TFInstanceInfos -> Names
  obtainOpenClosed (IOpen n _ _:ts)     = n : obtainOpenClosed ts
  obtainOpenClosed (IClosed n _ _ _:ts) = n : obtainOpenClosed ts
  obtainOpenClosed (_:ts)               = obtainOpenClosed ts
  obtainOpenClosed []                   = []

  --Obtains assoc and open instances
  obtainOpenAssoc :: TFInstanceInfos -> Names
  obtainOpenAssoc (IOpen n _ _:ts)      = n : obtainOpenAssoc ts
  obtainOpenAssoc (IAssoc n _ _ _ _:ts) = n : obtainOpenAssoc ts
  obtainOpenAssoc (_:ts)                = obtainOpenAssoc ts
  obtainOpenAssoc []                    = []

  hasAssocTypeSyn :: Name -> Name -> Bool
  hasAssocTypeSyn cn n = case [ n1 | (DAssoc n1 _ _ _ cn1) <- ds, cn1 == cn, n == n1] of
                            [] -> False
                            _  -> True 

  -- Obtains instance names of undefined type families
  getUndefinedNames = [n1 | n1 <- map obtainInstanceName is, n1 `notElem` ns]

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

instNoTFInArgument :: TypeFamilies -> TFInstanceInfos -> Errors
instNoTFInArgument fams tis = let

  violations = [ (obtainInstanceName inst, arg, thrd $ typeToMonoType fams arg) |
                 inst <- tis
               , arg <- obtainArguments inst
               , not $ isFamilyFree $ thrd $ typeToMonoType fams arg
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

--TODO: DO OTHER SMALLER CHECKS FROM PROPOSAL!
instSmallerChecks :: TypeFamilies -> TFInstanceInfos -> Errors
instSmallerChecks tyFams tis = let

  obtainDefTyFam :: MonoType -> MonoTypes
  obtainDefTyFam t@(MonoType_Fam _ mts) = t : concatMap obtainDefTyFam mts
  obtainDefTyFam (MonoType_App mt1 mt2) = obtainDefTyFam mt1 ++ obtainDefTyFam mt2
  obtainDefTyFam _                      = []
  
  obtainNameArgsDef :: TFInstanceInfo -> (Name, Types, Type)
  obtainNameArgsDef (IAssoc n ts t _ _) = (n, ts, t)
  obtainNameArgsDef (IClosed n ts t _)  = (n, ts, t)
  obtainNameArgsDef (IOpen n ts t)      = (n, ts, t)

  obtainVars :: MonoType -> [String]
  obtainVars (MonoType_Var (Just s) _) = [s]
  obtainVars (MonoType_Con _)          = []
  obtainVars (MonoType_Fam _ mts)      = nub $ concatMap obtainVars mts
  obtainVars (MonoType_App mt1 mt2)    = nub $ obtainVars mt1 ++ obtainVars mt2

  countSymbols :: MonoType -> Int
  countSymbols (MonoType_Var _ _)     = 1
  countSymbols (MonoType_Con _)       = 1
  countSymbols (MonoType_Fam _ mts)   = sum $ map countSymbols mts
  countSymbols (MonoType_App mt1 mt2) = countSymbols mt1 + countSymbols mt2

  countOccVar :: String -> MonoType -> Int
  countOccVar v (MonoType_Var (Just s) _) | v == s = 1
                                          | otherwise = 0
  countOccVar v (MonoType_Fam _ mts)      = sum $ map (countOccVar v) mts
  countOccVar v (MonoType_App mt1 mt2)    = countOccVar v mt1 + countOccVar v mt2
  countOccVar _ _                         = 0

  checkInstance :: (Name, Types, Type) -> Errors
  checkInstance (n, ts, t) = let
    argMts = map (thrd . typeToMonoType tyFams) ts
    defMt = thrd $ typeToMonoType tyFams t 

    defTFs = obtainDefTyFam defMt
    -- First smaller check
    notTFFree = case filter (\(MonoType_Fam _ mts) -> not $ all isFamilyFree mts) defTFs of
                  [] -> []
                  xs -> [TFFamInDefNotFamFree n xs]

    -- Second smaller check
    symbolsNotSmaller = [ TFDefNotSmallerSymbols n tf | tf <- defTFs, sum (map countSymbols argMts) <= countSymbols tf ]

    varOccurenceCheck = [ TFDefVarCountNotSmaller n argVar | 
                          argVar <- concatMap obtainVars argMts
                        , defTF <- defTFs
                        , sum (map (countOccVar argVar) argMts) <= countOccVar argVar defTF]
    in notTFFree ++ symbolsNotSmaller ++ varOccurenceCheck

  in concatMap (checkInstance . obtainNameArgsDef) tis

instInjDefChecks :: TypeFamilies -> TFDeclInfos -> TFInstanceInfos -> Errors
instInjDefChecks tyFams dis tis = let

  isInjective :: TFDeclInfo -> TFInstanceInfo -> Bool
  isInjective (DAssoc n1 _ (Just _) _ _) (IAssoc n2 _ _ _ _) = n1 == n2
  isInjective (DClosed n1 _ (Just _))    (IClosed n2 _ _ _)  = n1 == n2
  isInjective (DOpen n1 _ (Just _))      (IOpen n2 _ _)      = n1 == n2
  isInjective _                          _                   = False

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

-------------------------------
-- COMPATIBILITY CHECK
compatibilityCheck :: TypeFamilies -> TFInstanceInfos -> Errors
compatibilityCheck tfams tis = let
  
  -- Obtain all open tf instances
  openTFs = obtainOpenTFInstances tis
  
  -- create to be checked pairs
  instancePairs = [(inst1, inst2) | 
                  inst1:ys <- tails openTFs, inst2 <- ys
                  , obtainInstanceName inst1 == obtainInstanceName inst2]

  -- In compat
  in mapMaybe (compat tfams) instancePairs

closedOverlapWarning :: TypeFamilies -> TFInstanceInfos -> Warnings
closedOverlapWarning tfams tis = let

  closedTFs = obtainClosedTFInstances tis
  instancePairs = [(inst1, inst2) | 
                  inst1:ys <- tails closedTFs, inst2 <- ys
                  , obtainInstanceName inst1 == obtainInstanceName inst2]

  in mapMaybe (compatWarn tfams) instancePairs

compat :: TypeFamilies -> (TFInstanceInfo, TFInstanceInfo) -> Maybe Error
compat tfams (inst1, inst2) = let

  axiom1 = tfInstanceInfoToAxiom tfams inst1
  axiom2 = tfInstanceInfoToAxiom tfams inst2

  ((lhs1, rhs1), (lhs2, rhs2)) = runFreshM $ unbindAx axiom1 axiom2

  in case unifyTy M.empty lhs1 lhs2 of
            SurelyApart -> Nothing
            Unifiable subst -> 
              if applySubst subst rhs1 == applySubst subst rhs2
                then Nothing
                else Just $ OpenTFOverlapping (obtainInstanceName inst1) (obtainInstanceName inst2) lhs1 lhs2 rhs1 rhs2

compatWarn :: TypeFamilies -> (TFInstanceInfo, TFInstanceInfo) -> Maybe Warning
compatWarn tfams (inst1, inst2) = let
  
  axiom1 = tfInstanceInfoToAxiom tfams inst1
  axiom2 = tfInstanceInfoToAxiom tfams inst2

  ((lhs1, rhs1), (lhs2, rhs2)) = runFreshM $ unbindAx axiom1 axiom2
  in case unifyTy M.empty lhs1 lhs2 of
            SurelyApart -> Nothing
            Unifiable subst -> 
              if M.null subst
                then Just $ EqualClosedTypeFamilyInstances (obtainInstanceName inst1) (obtainInstanceName inst2) lhs1 lhs2 rhs1 rhs2
                else Nothing 

pairwiseInjChecks :: TypeFamilies -> TFDeclInfos -> TFInstanceInfos -> Errors
pairwiseInjChecks fams dis tis = let

  injTFs = obtainInjectiveTFInstances dis tis
  instancePairs = [(inst1, inst2) 
                  | inst1:ys <- tails injTFs, inst2 <- ys
                  , obtainInstanceName inst1 == obtainInstanceName inst2]
                  ++ [(inst, inst) | inst <- injTFs] -- Adding pairwise checks with itself (NEEDED)!
  ienv = buildInjectiveEnv dis
  in mapMaybe (pairwiseInjCheck fams ienv) instancePairs 

pairwiseInjCheck :: TypeFamilies -- Type fams to build axioms
                 -> InjectiveEnv -- Map containing indices of injective type families.
                 -> (TFInstanceInfo, TFInstanceInfo) -- The two instances to be pairwise checked
                 -> Maybe Error -- Result is a maybe error
pairwiseInjCheck fams ienv (inst1, inst2) = let

  axiom1 = tfInstanceInfoToAxiom fams inst1
  axiom2 = tfInstanceInfoToAxiom fams inst2
  
  ((clhs1@(MonoType_Fam _ lhs1), rhs1), (clhs2@(MonoType_Fam _ lhs2), rhs2)) = runFreshM $ unbindAx axiom1 axiom2

  in case preUnify ienv rhs1 rhs2 of 
            SurelyApart -> Nothing
            Unifiable subst
              | all (\i -> checkInjArg subst (lhs1 !! i) (lhs2 !! i)) injIndices
                  -> Nothing 
              | isClosed inst1 && applySubst subst clhs1 /= applySubst subst clhs2
                  -> Nothing
              | otherwise
                  -> Just $ InjPreUnifyFailed (obtainInstanceName inst1) (obtainInstanceName inst2) clhs1 clhs2 rhs1 rhs2  -- ERROR!
  where
    injIndices = ienv M.! show (obtainInstanceName inst1)

    checkInjArg :: SubstitutionEnv -> MonoType -> MonoType -> Bool
    checkInjArg subst mt1 mt2 = applySubst subst mt1 == applySubst subst mt2

-- Running this in the FreshM monad makes sure that the unbind functions generate fresh vars in the lhs and rhs's.
unbindAx :: Axiom ConstraintInfo -> Axiom ConstraintInfo -> FreshM ((MonoType, MonoType), (MonoType, MonoType))
unbindAx (Axiom_Unify b1) (Axiom_Unify b2) = do
  (_, (lhs1, rhs1)) <- unbind b1
  (_, (lhs2, rhs2)) <- unbind b2
  return ((lhs1, rhs1), (lhs2, rhs2))
-- CHECKS TODO!!!!!:
--
-- Definition smaller check (For non-injective)
-- - Injective type fams
--    - Pre-unification
--    - Basically, the injectivity check from paper.