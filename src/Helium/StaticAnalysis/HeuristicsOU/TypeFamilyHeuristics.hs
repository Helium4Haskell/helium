{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics where
import Unbound.Generics.LocallyNameless ( Fresh, unbind, Subst (substs))
import Rhodium.Blamer.Path
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (Axiom (Axiom_ClosedGroup, Axiom_Unify, Axiom_Injective), TyVar, RType (MType), Constraint (Constraint_Inst, Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con, MonoType_Var), PolyType (PolyType_Mono, PolyType_Bind), fvToList, MonoTypes, isFamilyFree)
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Rhodium.Blamer.Heuristics (VotingHeuristic (SingleVoting))
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules (ErrorLabel (ErrorLabel))

import Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils (buildReductionTrace, getFullTrace, getLastTypeInTrace, getFirstTypeInTrace, squashTrace)
import Data.Maybe (isJust, catMaybes, fromMaybe, mapMaybe)
import Debug.Trace (trace)
import Data.List (permutations, nub, intercalate, sort)
import qualified Data.Map as M
import Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo
import Helium.StaticAnalysis.Messages.HeliumMessages (freshenRepresentation)
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances (reactClosedTypeFam, convertSubstitution, axsToInjectiveEnv)
import Rhodium.Core (unifyTypes, runTG)
import Control.Monad (filterM)
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion (polytypeToMonoType)
import Helium.StaticAnalysis.Miscellaneous.TypeConversion (Freshen(freshenWithMapping))
import Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos (TFInstanceInfo(tfiName, varNameMap), tails, splitBy)
import Helium.StaticAnalysis.StaticChecks.TypeFamilies (performPairwiseInjCheck, performWronglyUsedVarInInjCheck)
import Helium.Syntax.UHA_Syntax (Name)
import Helium.StaticAnalysis.Miscellaneous.Diagnostics (Diagnostic)
import Data.Either (isLeft, fromLeft, fromRight)
import Data.Bifunctor (bimap)

typeErrorThroughReduction :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic
typeErrorThroughReduction path = SingleVoting "Type error through type family reduction" f
  where
    f (constr, eid, ci, gm) = do
      graph <- getGraph
      let edge = getEdgeFromId graph eid
      case constr of
        Constraint_Inst _ pt _ -> do
          -- Getting edge of erroneous constraint (pconstraint)
          let pmt = case pt of
                pb@(PolyType_Bind _ _) -> (fst . fst . snd) $ polytypeToMonoType [] 0 pb
                PolyType_Mono _ mt -> mt
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of
            -- PConstraint could not be reduced further
            (Constraint_Unify mf@MonoType_Fam{} t _, ErrorLabel "Residual constraint") -> do
              [MType freshOg] <- freshenRepresentation . (:[]) <$> getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              -- Get potential trace.
              theTrace <- squashTrace <$> buildReductionTrace False cedge freshOg
              -- Builds hint in nested sense, when type family contains other families that were not reducable (or wronly reduced, perhaps)
              mTheHint <- buildNestedHints cedge mf t
              -- Unpack hint
              let theHint = case mTheHint of
                    Nothing -> id
                    Just ([],[]) -> id
                    Just (causes, fixes) -> let
                      causeHint = if null causes
                        then id
                        else addHint ("probable cause" ++ if length causes > 1 then "s" else "") (intercalate "\n" causes)
                      fixHint = if null fixes
                        then id
                        else addHint ("possible fix" ++ if length fixes > 1 then "es" else "") (intercalate "\n" fixes)
                      in causeHint . fixHint
              case theTrace of
                -- No trace but still reduction error
                [] -> if typeIsInType mf pmt
                        then return $ Just (5, "Type family could not be reduced, no trace", constr, eid, addProperty (TypeFamilyReduction Nothing t freshOg freshOg False) $ theHint ci, gm)
                        else return Nothing
                -- Now with trace, checking if the trace belongs to the type signature
                trc -> do
                  let Just lastType = getLastTypeInTrace trc
                  let Just firstType = getFirstTypeInTrace trc
                  if typeIsInType lastType pmt
                    then return $ Just (5, "Type family could not be reduced further, trace", constr, eid, addProperty (TypeFamilyReduction (Just theTrace) t lastType firstType False) $ theHint ci, gm)
                    else return Nothing
            -- Reduced to simple type but resulted in type error
            (Constraint_Unify t1 t2 _, _) -> do
              -- Substitute both types
              (MType t1') <- getSubstTypeFull (getGroupFromEdge edge) (MType t1)
              (MType t2') <- getSubstTypeFull (getGroupFromEdge edge) (MType t2)
              -- Generate traces
              t1Trace <- squashTrace <$> buildReductionTrace True edge t1'
              t2Trace <- squashTrace <$> buildReductionTrace True edge t2'
              -- Get the type reduced from a type family (only one side is).
              case getFullTrace t1Trace t2Trace of
                Nothing -> return Nothing
                Just (ti, theTrace) -> do
                  -- Get the inferred type
                  let inferredT = if ti == 0 then t2 else t1
                  let inferredTStr = makeCharString inferredT
                  -- Get last type in trace and first type, obtain potential permutation hint.
                  let Just lastType = getLastTypeInTrace theTrace
                  mhint <- buildPermutationHint lastType inferredT
                  let hint = maybe id (addHint "possible fix") mhint
                  let Just firstType = getFirstTypeInTrace theTrace
                  if typeIsInType lastType pmt
                    then return $ Just (4, "Type family reduction type error", constr, eid, addProperty (TypeFamilyReduction (Just theTrace) inferredTStr lastType firstType True) $ hint ci, gm)
                    else return Nothing
            _ -> return Nothing
        _                     -> return Nothing
        where
          -- Builds permutation hint.
          buildPermutationHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo)) 
                                => MonoType -> MonoType -> m (Maybe String)
          buildPermutationHint ogmf@(MonoType_Fam fn mts _) infMt = do
            -- Build permutations of the arguments of the type family.
            let permsMt = filter (mts /=) $ permutations mts
            -- loop over the permutations.
            loopPerms permsMt
            
            where
              -- Tries a permutation.
              loopPerms (p:perms) = do
                axs <- getAxioms
                -- building new type family.
                let nft = MonoType_Fam fn p Nothing
                -- obtain touchable vars for unification.
                tchs <- filterM (fmap isJust . isVertexTouchable) (nub $ fvToList nft ++ fvToList infMt :: [TyVar])
                -- unify new type family application with the inferred type passed with it.
                ures <- runTG $ unifyTypes axs [] [Constraint_Unify nft infMt Nothing] tchs
                case ures of
                  -- No substitution, we try the next.
                  Nothing -> loopPerms perms
                  -- There is a substitution and thus we may provide a possible fix.
                  Just _ -> do
                    let hint = Just ("Changing " 
                                  ++ (show . show) ogmf ++ " to " ++ (show . show) nft ++ " helps to remove this type error")
                    return hint 
              loopPerms [] = return Nothing
          buildPermutationHint _ _ = return Nothing

          -- Builds a hint that shows when a type was not apart during closed type family matching.
          buildApartnessHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo)) 
                             => MonoType -> m (Maybe String)
          buildApartnessHint mt@(MonoType_Fam fn _ _) = do
            axs <- getAxioms
            
            -- get the closed axioms belonging to the family (or not)
            let mClosedAxs = getMaybeClosedAxs axs fn         

            mApartErr <- case mClosedAxs of
              -- No closed family, no hint.
              Nothing -> return Nothing
              -- We perform the reaction again, with different arguments to obtain the possibly non apart axiom.
              Just caxs -> snd <$> reactClosedTypeFam False False (Constraint_Unify mt (MonoType_Con "Char" Nothing) Nothing) caxs
            -- Build hint accordingly.
            let [MType mt'] = freshenRepresentation [MType mt :: RType ConstraintInfo]
            case mApartErr of
              Just (amt, r) -> do
                let hint = "type " ++ (show . show) mt' ++ " is not apart from instance " ++ (show . show) amt ++ " at " ++ show r
                return $ Just hint
              Nothing -> return $ Just $ (show . show) mt' ++ " is not reducable. No matching instance was found"
          buildApartnessHint _ = return Nothing

          -- Builds hints in a nested way, considers arguments of the non-reducable type family too.
          buildNestedHints :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo)) 
                           => TGEdge (Constraint ConstraintInfo) ->  MonoType -> MonoType -> m (Maybe ([String], [String]))
          buildNestedHints cedge mf@(MonoType_Fam fn _ _) t = do
            axs <- getAxioms
            -- We need to know what arguments are expected to be (based on inferred body type "t")
            wantedArgs <- filterOnAxsRHS fn axs axs t
            case wantedArgs of
              -- Nothing is returned when no wanted args could be obtained (injective problems, multiple possibilities...)
              Nothing -> return Nothing
              -- Else, we nest again and build hints for this level.
              Just args -> do
                -- Substitute the family to get complete type.
                (MType mf'@(MonoType_Fam _ mts' _)) <- getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
                -- Considerables are the family arguments and the wanted family arguments zipped.
                let considerables = zip mts' args
                -- Recurse
                nestedRes <- foldl (\(pcs,pfs) (pcs', pfs') -> (pcs++pcs', pfs++pfs')) ([],[]) . catMaybes <$> mapM (uncurry (buildNestedHints cedge)) considerables
                
                -- Build hints for this level.
                apartHint <- buildApartnessHint mf'
                permHint <- buildPermutationHint mf' t
                -- If deeper levels have hints, we return those, else we use this level's hints.
                -- Not the prettiest of pattern matches
                return (case (nestedRes, apartHint, permHint) of
                  (r@(_:_, _:_), _, _) -> Just r
                  (r@(_:_, []), _, _) -> Just r
                  (r@([], _:_), _, _) -> Just r
                  (_, Just a, Just p) -> Just ([a], [p])
                  (_, Just a, Nothing) -> Just ([a], [])
                  (_, Nothing, Just p) -> Just ([], [p])
                  (_, _, _) -> Nothing)
          -- In case a type with trace is found, we check if we can build a hint with the last type in it.         
          buildNestedHints cedge mt t = do
            theTrace <- buildReductionTrace True cedge mt
            case theTrace of
              [] -> return Nothing
              xs -> do
                let Just lastType = getLastTypeInTrace xs
                permHint <- buildPermutationHint lastType t
                return $ case permHint of
                  Just p -> Just ([],[p])
                  Nothing -> Nothing

          getMaybeClosedAxs :: [Axiom ConstraintInfo] -> String -> Maybe [Axiom ConstraintInfo]
          getMaybeClosedAxs (Axiom_ClosedGroup fn1 cgaxs: _) fn2
            | fn1 == fn2 = Just cgaxs
          getMaybeClosedAxs (_:axs) fn = getMaybeClosedAxs axs fn
          getMaybeClosedAxs [] _     = Nothing

typeIsInType :: MonoType -> MonoType -> Bool
typeIsInType t1 mf@(MonoType_Fam _ mts _) = let
  (mf', t1') = freshenTypes t1 mf
  in mf' == t1' || any (typeIsInType t1) mts
typeIsInType t1 ma@(MonoType_App m1 m2 _) = let
  (ma', t1') = freshenTypes t1 ma
  in ma' == t1' || typeIsInType t1 m1 || typeIsInType t1 m2
typeIsInType t1 mc@(MonoType_Con _ _)     = t1 == mc
typeIsInType t1 mv@MonoType_Var{}         = let 
  (mv', t1') = freshenTypes t1 mv
  in t1' == mv'

freshenTypes :: MonoType -> MonoType -> (MonoType, MonoType)
freshenTypes m1 m2 = let
  (_, (m1', _)) = freshenWithMapping [] (0 :: Integer) m1
  (_, (m2', _)) = freshenWithMapping [] (0 :: Integer) m2
  in (m1', m2')

replaceIfEqual :: MonoType -> MonoType -> MonoType -> MonoType
replaceIfEqual t1 t2 mf@(MonoType_Fam f mts rt) = if t2 == mf then t1 else MonoType_Fam f (map (replaceIfEqual t1 t2) mts) rt
replaceIfEqual t1 t2 ma@(MonoType_App m1 m2 rt) = if t2 == ma then t1 else MonoType_App (replaceIfEqual t1 t2 m1) (replaceIfEqual t1 t2 m2) rt
replaceIfEqual t1 t2 mc@(MonoType_Con _ _)      = if t2 == mc then t1 else mc
replaceIfEqual t1 t2 mv@MonoType_Var{}          = if t2 == mv then t1 else mv

makeCharString :: MonoType -> MonoType
makeCharString (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) rt) = MonoType_Fam "String" [] rt
makeCharString (MonoType_App m1 m2 rt) = MonoType_App (makeCharString m1) (makeCharString m2) rt
makeCharString (MonoType_Fam f mts rt) = MonoType_Fam f (map makeCharString mts) rt
makeCharString mt = mt

injectUntouchableHeuristic :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                           => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic
injectUntouchableHeuristic path = SingleVoting "Type error through injection of untouchable variable" f
  where 
    f (constr, eid, ci, gm) = do
      graph <- getGraph
      case constr of
        Constraint_Inst _ pt _ -> do
          let pmt = case pt of
                pb@(PolyType_Bind _ _) -> (fst . fst . snd) $ polytypeToMonoType [] 0 pb
                PolyType_Mono _ mt -> mt
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid 
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of 
            (cn@(Constraint_Unify mv@MonoType_Var{} mt (Just cinfo)), ErrorLabel "Residual constraint") ->
              case isResultOfInjectivity cinfo of
                Nothing -> return Nothing
                Just (cl, cr, c) -> if typeIsInType cl pmt
                  then let
                    because_hint = addHint "because" ("could not assign " ++ (show . show) mt ++ " to " ++ (show . show) mv ++ ". " ++ 
                                                     (show . show) mv ++ " is quantified with a (implicit) forall and cannot be assigned any specific type")
                    reductionHint = addHint "full reduction" (
                      "1. From\t: " ++ show c ++
                      "\n   Got\t: " ++ show cn ++
                      "\n   Reason\t: injectivity" ++
                      "\n   Amount\t: 1 time" 
                      )
                    in return $ Just (5, "Tried to inject untouchable", constr, eid, addProperty (InjectUntouchable (cl, cr)) $ because_hint $ reductionHint ci, gm)
                  else return Nothing
            _ -> return Nothing
        _ -> return Nothing

-- Works on typefamilies where a right to left improvement should have been performed but isn't because it was not specified to be injective.
shouldBeInjectiveHeuristic :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic
shouldBeInjectiveHeuristic path = SingleVoting "Not injective enough" f
  where
    f (constr, eid, ci, gm) = do
      graph <- getGraph
      case constr of
        Constraint_Inst _ pt _ -> do
          let pmt = case pt of
                pb@(PolyType_Bind _ _) -> (fst . fst . snd) $ polytypeToMonoType [] 0 pb
                PolyType_Mono _ mt -> mt
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of 
            (Constraint_Unify mf@(MonoType_Fam fn _ _) mt _, ErrorLabel "Residual constraint") -> do
              -- Get hint about possible injectivity annotations
              injHint <- buildNestedInjHint cedge mf mt
              (MType mf') <- getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              case injHint of
                Nothing -> return Nothing
                Just iHint -> do 
                  theTrace <- buildReductionTrace False cedge mf
                  case theTrace of 
                    [] -> if typeFamInType fn pmt
                      then return $ Just (7, "Should be injective, with trace", constr, eid, addProperty (TypeFamilyReduction Nothing mt mf' mf' False) $ iHint ci, gm)
                      else return Nothing
                    trc -> do
                      let Just lastT = getLastTypeInTrace trc
                      let Just firstT = getFirstTypeInTrace trc
                      if typeIsInType lastT pmt
                        then return $ Just (7, "Should be injective, without trace", constr, eid, addProperty (TypeFamilyReduction (Just trc) mt lastT firstT False) $ iHint ci, gm)
                        else return Nothing
            _ -> return Nothing
        _ -> return Nothing

        where

          buildNestedInjHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                             => TGEdge (Constraint ConstraintInfo) -> MonoType -> MonoType -> m (Maybe (ConstraintInfo -> ConstraintInfo))
          buildNestedInjHint cedge mf@(MonoType_Fam fn mts _) mt = do
            axs <- getAxioms
            -- Make sure that both types are substituted
            (MType mf'@(MonoType_Fam fn' mts' _)) <- getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
            (MType mt') <- getSubstTypeFull (getGroupFromEdge cedge) (MType mt)
            -- get the touchables from the family arguments
            tchsMts <- getTchMtsFromArgs mts'
            -- Check if the rhs is unifiable with an axs it belongs to.
            rhsUnifiable <- isRhsUnifiable fn' mt' axs
            case (tchsMts, rhsUnifiable) of
              -- If not unifiable, we are not able to do anything
              (_, False) -> return Nothing
              (tchs, True) -> do
                -- For nesting we need to know what the wanted args are.
                wantedArgs <- filterOnAxsRHS fn axs axs mt'
                case wantedArgs of
                  -- Only toplevel
                  Nothing -> buildInjHint (map fst tchs) mf' mt'
                  -- Recurse as well
                  Just wargs -> do
                    -- Recurse with wanted args
                    let considerables = zip mts wargs
                    nestedRes <- catMaybes <$> mapM (uncurry (buildNestedInjHint cedge)) considerables
                    
                    -- Build hint on this level
                    hint <- buildInjHint (map fst tchs) mf' mt'
                    case (nestedRes, hint) of
                      ([], Just h) -> return $ Just h
                      ([], Nothing) -> return Nothing
                      (xs, _) -> return $ Just $ foldl1 (.) xs
          buildNestedInjHint _ _ _ = return Nothing

          buildInjHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                       => [Int] -> MonoType -> MonoType -> m (Maybe (ConstraintInfo -> ConstraintInfo))
          buildInjHint tchs mf@(MonoType_Fam fn mts _) mt = if all isFamilyFree mts
            then do
              axs <- getAxioms
              -- Obtain currently injective arguments
              let injLocs = obtainInjInfoFromAxs fn axs
              -- the touchables not in injLocs are 'erroneous'
              let errTchs = filter (`notElem` injLocs) tchs
              if null errTchs
                -- No erroneous touchables -> we have nothing to do.
                then return Nothing
                else do
                  -- pSet contains all possible inj variables that we may add to the axiom
                  let pSet = filter (not . null) $ powerset errTchs
                  -- vNM maps the injIndices to their names
                  let vNM = buildVarNameMap fn axs
                  -- Computes for every combination of vars if it is possible to add.
                  possibleInjCombs <- mapM (checkNewInjectivity fn axs mf mt) (trace ("PSET: " ++ show pSet) pSet)
                  --Split Lefts and Rights of the result
                  let splittedRes = bimap (map $ fromLeft []) (map $ fromRight []) $ splitBy isLeft possibleInjCombs
                  case splittedRes of
                    (xs, []) -> let
                      -- Check what indices are the culprit (the ones present in all) 
                      wrongIndices = filter (\et -> all (et `elem`) xs) errTchs
                      -- build string of errTchs
                      nonInjString = buildNonInjString errTchs vNM
                      -- build string of wrongIndices
                      wrongInjString = buildNonInjString wrongIndices vNM
                      in return $ Just $ addHint "probable cause" ("usage of type family " ++ show fn ++ " requires argument " ++ if length nonInjString > 1 then "s" else "" ++ "\"" ++ nonInjString
                                                                  ++ "\" to be injective, but \"" ++ wrongInjString ++ "\" currently can't be")
                    -- We have some possible annotations, we provide them as hint. 
                    (_, ys) -> return $ Just $ addHint "possible fix" ((if null injLocs 
                                                                          then "Add one of the following injectivity annotations to " ++ show fn ++ ":\n"
                                                                          else "Replace the injectivity annotation of " ++ show fn ++ " with one of the following:\n")
                                                                      ++ buildInjSuggestionsString (zip ys (repeat vNM)))
            else return Nothing
          buildInjHint _ _ _ = return Nothing

          checkNewInjectivity :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                              => String -> [Axiom ConstraintInfo] -> MonoType -> MonoType -> [Int] -> m (Either [Int] [Int])
          checkNewInjectivity fn axs fam mt newTchs = do
            -- Update the injective axiom with new injective annotation (based on newTchs)
            let (axs', is) = swapInjAxiom fn newTchs axs
            let unifyAxs = filterAxiomsOnName fn axs' -- only unify axioms of type fam 'fn'
            ienv <- axsToInjectiveEnv axs'
            let unifyCombs = [(x, y) | (x:ys) <- tails unifyAxs, y <- ys]
            -- pairwise injectivity check and wrongly used vars check from static checks
            let pairwiseRes = mapMaybe (uncurry (performPairwiseInjCheck ienv)) unifyCombs
            let wronglyUsedVarRes = mapMaybe (performWronglyUsedVarInInjCheck ienv) unifyAxs
            -- if there are errors, we cannot use the new injetivity notation
            case pairwiseRes ++ wronglyUsedVarRes of
              [] -> do
                -- Check if the constraint is solved
                tchs <- filterM (fmap isJust . isVertexTouchable) (nub $ fvToList fam ++ fvToList mt :: [TyVar])
                res <- runTG $ unifyTypes axs' [] [Constraint_Unify fam mt Nothing] tchs
                case res of
                  -- if not: we return "Left newTchs" which means these are erroneous
                  Nothing -> return $ Left newTchs
                  -- Else, we return the new complete annotation (in is)
                  Just _ -> return $ Right is
              _  -> return $ Left newTchs

          swapInjAxiom :: String -> [Int] -> [Axiom ConstraintInfo] -> ([Axiom ConstraintInfo], [Int])
          swapInjAxiom fn is axs = let

            isInjective (Axiom_Injective fn' _) = fn == fn'
            isInjective _ = False

            oldInj = maybeHead $ filter isInjective axs
            remainingAxs = filter (not . isInjective) axs
            in case oldInj of
              Nothing -> (Axiom_Injective fn is : axs, is)
              Just (Axiom_Injective _ is') -> (Axiom_Injective fn (nub $ is ++ is') : remainingAxs, is ++ is')
              _ -> error "Should not happen!"
          
          getTchMtsFromArgs :: (IsTouchable m TyVar, Fresh m) => MonoTypes -> m [(Int, MonoType)]
          getTchMtsFromArgs mts = do
            let vars = [(i, x) | (i, x) <- zip [0..] mts, isVar x]
            filterM (\(_, MonoType_Var _ v _) -> isJust <$> isVertexTouchable v) vars

            where
              isVar MonoType_Var{} = True
              isVar _              = False
          
          isRhsUnifiable :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                         => String -> MonoType -> [Axiom ConstraintInfo] -> m Bool
          isRhsUnifiable fn mt (Axiom_Unify b _:axs) = do
            (_, (MonoType_Fam fn' _ _, rhs)) <- unbind b
            if fn == fn'
              then do
                allAxs <- getAxioms
                tchs <- filterM (fmap isJust . isVertexTouchable) (nub $ fvToList rhs ++ fvToList mt :: [TyVar])
                res <- runTG $ unifyTypes allAxs [] [Constraint_Unify mt rhs Nothing] tchs
                case res of
                  Nothing -> return False
                  Just _ -> return True
              else isRhsUnifiable fn mt axs
          isRhsUnifiable fn mt (Axiom_ClosedGroup fn' axs': axs) = if fn == fn'
            then isRhsUnifiable fn mt axs'
            else isRhsUnifiable fn mt axs
          isRhsUnifiable fn mt (_:axs) = isRhsUnifiable fn mt axs
          isRhsUnifiable _ _ [] = return False

          obtainInjInfoFromAxs :: String -> [Axiom ConstraintInfo] -> [Int]
          obtainInjInfoFromAxs fn (Axiom_Injective afn idx:axs) = if fn == afn then idx else obtainInjInfoFromAxs fn axs
          obtainInjInfoFromAxs fn (_:axs) = obtainInjInfoFromAxs fn axs
          obtainInjInfoFromAxs _  [] = []

          buildVarNameMap :: String -> [Axiom ConstraintInfo] -> M.Map Int Name
          buildVarNameMap fn axs = let
            fnAxs = filterAxiomsOnName fn axs
            in fromMaybe M.empty (varNameMap (let (Axiom_Unify _ (Just tfi)) = head fnAxs in tfi))

          buildInjSuggestionsString :: [([Int], M.Map Int Name)] -> String
          buildInjSuggestionsString posIdx = intercalate "\n" $ zipWith
            (curry
              (\ (i, (is, varMap))
                  -> let names = map (varMap M.!) (sort is)
                    in show i ++ ": r -> " ++ unwords (map show names)))
            [(1 :: Integer)..] posIdx

          buildNonInjString :: [Int] -> M.Map Int Name -> String
          buildNonInjString idx vNM = let 
            names = map (vNM M.!) (sort idx)
            in intercalate ", " (map show names)

-- Filter function for axioms.
filterOnAxsRHS :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo))
                => String -> [Axiom ConstraintInfo] -> [Axiom ConstraintInfo] -> MonoType -> m (Maybe [MonoType])
filterOnAxsRHS fn axs axs' mt = do
  filterRes <- catMaybes <$> mapM (filterAxOnRHS axs' fn mt) axs
  case filterRes of
    [] -> return $ Just []
    [x] -> return $ Just x
    _ : _ -> return Nothing

-- Checks one axiom at a time.
filterAxOnRHS :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo)) 
              => [Axiom ConstraintInfo] -> String -> MonoType -> Axiom ConstraintInfo -> m (Maybe [MonoType])
filterAxOnRHS axs fn mt (Axiom_Unify b _) = do
  (aes, (lhs@(MonoType_Fam fn' _ _), rhs)) <- unbind b
  if fn /= fn'
    then return Nothing
    else do
      tchs <- filterM (fmap isJust . isVertexTouchable) (fvToList mt :: [TyVar])
      -- We check if the right hand side unifies with the type from the constraint.
      res <- runTG $ unifyTypes axs [] [Constraint_Unify rhs mt Nothing] (nub $ tchs ++ aes)
      case res of
        -- If so, apply the substitution and return the argument types.
        Just s -> do
          let (MonoType_Fam _ mts _) = substs (convertSubstitution s) lhs
          return $ Just mts
        Nothing -> return Nothing
-- If closed group, loop over the group.
filterAxOnRHS axs' fn mt (Axiom_ClosedGroup fn' axs) =
  if fn == fn'
    then filterOnAxsRHS fn axs axs' mt
    else return Nothing
filterAxOnRHS _ _ _ _ = return Nothing

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [r | ps <- powerset xs, r <- [x:ps,ps]]

filterAxiomsOnName :: String -> [Axiom ConstraintInfo] -> [Axiom ConstraintInfo]
filterAxiomsOnName fn (ax@(Axiom_Unify _ (Just tfi)):axs) = if show (tfiName tfi) == fn then ax : filterAxiomsOnName fn axs else filterAxiomsOnName fn axs
filterAxiomsOnName fn (Axiom_ClosedGroup fn' axs:axs') = if fn == fn' then axs else filterAxiomsOnName fn axs'
filterAxiomsOnName fn (_:axs) = filterAxiomsOnName fn axs
filterAxiomsOnName _ _ = []

typeFamInType :: String -> MonoType -> Bool
typeFamInType s (MonoType_Fam fn mts _) = let
  --mf' = freshenWithMapping [] (0 :: Integer) mf
  in fn == s || any (typeFamInType s) mts
typeFamInType s (MonoType_App m1 m2 _) = typeFamInType s m1 || typeFamInType s m2
typeFamInType _ (MonoType_Con _ _)     = False
typeFamInType _ MonoType_Var{}         = False