{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE TupleSections #-}
module Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics where
import Unbound.Generics.LocallyNameless ( Fresh, unbind, Subst (substs), bind)
import Rhodium.Blamer.Path
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (Axiom (Axiom_ClosedGroup, Axiom_Unify, Axiom_Injective), TyVar, RType (MType), Constraint (Constraint_Inst, Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con, MonoType_Var), PolyType (PolyType_Mono, PolyType_Bind), fvToList, MonoTypes, isFamilyFree)
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Rhodium.Blamer.Heuristics (VotingHeuristic (SingleVoting))
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules (ErrorLabel (ErrorLabel))

import Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils (buildReductionTrace, getLastTypeInTrace, getFirstTypeInTrace, squashTrace)
import Data.Maybe (isJust, catMaybes, fromMaybe, mapMaybe)
import Data.List (permutations, nub, intercalate, sort)
import qualified Data.Map as M
import Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo
import Helium.StaticAnalysis.Messages.HeliumMessages (freshenRepresentation)
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances (reactClosedTypeFam, convertSubstitution, axsToInjectiveEnv, isBetaFree)
import Rhodium.Core (unifyTypes, runTG)
import Control.Monad (filterM)
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion (polytypeToMonoType, contFreshMRes)
import Helium.StaticAnalysis.Miscellaneous.TypeConversion (Freshen(freshenWithMapping))
import Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos (TFInstanceInfo(tfiName, varNameMap), tails, splitBy)
import Helium.StaticAnalysis.StaticChecks.TypeFamilies (performPairwiseInjCheck, performWronglyUsedVarInInjCheck)
import Helium.Syntax.UHA_Syntax (Name)
import Helium.StaticAnalysis.Miscellaneous.Diagnostics (Diagnostic)
import Data.Either (isLeft, fromLeft, fromRight)
import Data.Bifunctor (bimap)
import Rhodium.TypeGraphs.GraphReset (removeEdge)

typeErrorThroughReduction :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic
typeErrorThroughReduction path = SingleVoting "Type error through type family reduction" f
  where
    f (constr, eid, ci, _) = do
      graph <- getGraph
      let edge = getEdgeFromId graph eid
          constr' = fromMaybe constr (maybeHasOriginalTypeSignature ci)
      case constr' of
        Constraint_Inst _ pt _ -> do
          -- Getting edge of erroneous constraint (pconstraint)
          let pmt = case pt of
                pb@(PolyType_Bind _ _) -> (fst . fst . snd) $ polytypeToMonoType [] 0 pb
                PolyType_Mono _ mt -> mt
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of
            (Constraint_Unify mf1@MonoType_Fam{} mf2@MonoType_Fam{} _, ErrorLabel "Residual constraint") -> do
              (MType mf1') <- if isBetaFree mf1 then return (MType mf1) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf1)
              (MType mf2') <- if isBetaFree mf2 then return (MType mf2) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf2)

              mf1Trace <- squashTrace <$> buildReductionTrace cedge mf1'
              mf2Trace <- squashTrace <$> buildReductionTrace cedge mf2'

              let redHint = addReduction (Just mf1Trace) . addReduction (Just mf2Trace)
              
              mf1Hints <- buildNestedApartnessHint mf1
              mf2Hints <- buildNestedApartnessHint mf2
              let hints  = case catMaybes (mf1Hints ++ mf2Hints) of
                            [] -> id
                            causes -> addHint ("probable cause" ++ if length causes > 1 then "s" else "") (intercalate "\n" causes)
              let lastMf1 = getLastTypeInTrace mf1Trace
                  lastMf2 = getLastTypeInTrace mf2Trace

              if maybe (mf1' `typeIsInType` pmt) (`typeIsInType` pmt) lastMf1 || maybe (mf2' `typeIsInType` pmt) (`typeIsInType` pmt) lastMf2
                then return $ Just (5, "Type families could not be reduced, potential trace", constr', eid, addProperties [TypeFamilyReduction lastMf1 mf1' lastMf2 mf2' False, HasOriginalTypeSignature constr'] $ redHint $ hints ci, replaceTypeFamModifiers [(lastMf1, mf1'), (lastMf2, mf2')] constr)
                else return Nothing              
            -- PConstraint could not be reduced further
            (Constraint_Unify mf@MonoType_Fam{} t _, ErrorLabel "Residual constraint") -> do
              -- Make sure that we only substitute beta variables (others are okay)
              (MType mf') <- if isBetaFree mf then return (MType mf) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              let [MType freshOg] = freshenRepresentation . (:[]) $ (MType mf' :: RType ConstraintInfo)
              -- Get potential trace.
              theTrace <- squashTrace <$> buildReductionTrace cedge mf'
              let redHint = addReduction (Just theTrace)
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
                [] -> if typeIsInType mf' pmt
                        then return $ Just (5, "Type family could not be reduced, no trace", constr', eid, addProperties [TypeFamilyReduction Nothing freshOg Nothing t False, HasOriginalTypeSignature constr'] $ redHint $ theHint ci, replaceTypeFamModifiers [(Just mf', t)] constr)
                        else return Nothing
                -- Now with trace, checking if the trace belongs to the type signature
                trc -> do
                  let Just lastType = getLastTypeInTrace trc
                  let Just firstType = getFirstTypeInTrace trc
                  if typeIsInType lastType pmt
                    then return $ Just (5, "Type family could not be reduced further, trace", constr', eid, addProperties [TypeFamilyReduction (Just lastType) firstType Nothing t False, HasOriginalTypeSignature constr'] $ redHint $ theHint ci, replaceTypeFamModifiers [(Just lastType, t)] constr)
                    else return Nothing
            -- Reduced to simple type but resulted in type error
            (Constraint_Unify t1 t2 _, _) -> do
              -- Substitute both types
              (MType t1') <- getSubstTypeFull (getGroupFromEdge edge) (MType t1)
              (MType t2') <- getSubstTypeFull (getGroupFromEdge edge) (MType t2)
              -- Generate traces
              t1Trace <- squashTrace <$> buildReductionTrace edge t1'
              t2Trace <- squashTrace <$> buildReductionTrace edge t2'
              let t1RedHint = addReduction (Just t1Trace)
              let t2RedHint = addReduction (Just t2Trace)
              let lastType1 = getLastTypeInTrace t1Trace
              let lastType2 = getLastTypeInTrace t2Trace
              mhint1 <- maybe (return Nothing) (`buildPermutationHint` t2) lastType1
              mhint2 <- maybe (return Nothing) (`buildPermutationHint` t1) lastType2
              let hint = maybe id (addHint "possible fix") mhint1 . maybe id (addHint "possible fix") mhint2
              if maybe False (`typeIsInType` pmt) lastType1 || maybe False (`typeIsInType` pmt) lastType2
                then return $ Just (4, "Type family reduction type error", constr' , eid, addProperties [TypeFamilyReduction lastType1 t1 lastType2 t2 True] $ t1RedHint $ t2RedHint $ hint ci, replaceTypeFamModifiers [(lastType1, t1), (lastType2, t2)] constr)
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

          buildNestedApartnessHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic, CompareTypes m (RType ConstraintInfo))
                                   => MonoType -> m [Maybe String]
          buildNestedApartnessHint mt@(MonoType_Fam _ mts _) = do
            nestedHints <- mapM buildNestedApartnessHint mts
            
            curHint <- buildApartnessHint mt
            
            case curHint of
              Just _ -> return [curHint]
              Nothing -> return $ concat nestedHints
          buildNestedApartnessHint _ = return [Nothing]

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
                (MType mf'@(MonoType_Fam _ mts' _)) <- if isBetaFree mf then return (MType mf) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
                -- Considerables are the family arguments and the wanted family arguments zipped.
                let considerables = zip mts' args
                -- Recurse
                nestedRes <- foldl (\(pcs,pfs) (pcs', pfs') -> (pcs++pcs', pfs++pfs')) ([],[]) . catMaybes <$> mapM (uncurry (buildNestedHints cedge)) considerables
                
                -- Build hints for this level.
                apartHint <- buildApartnessHint mf'
                permHint <- buildPermutationHint mf' t

                let basicHints = foldl (\c m -> if isFam m then ((show . show) m ++ " is not reducable. No matching instance was found") : c else c) [] mts' 
                -- If deeper levels have hints, we return those, else we use this level's hints.
                -- Not the prettiest of pattern matches
                return (case (nestedRes, apartHint, permHint) of
                  (r@(_:_, _:_), _, _) -> Just r
                  (r@(_:_, []), _, _) -> Just r
                  (r@([], _:_), _, _) -> Just r
                  (_, Just a, Just p) -> Just (if null basicHints then [a] else basicHints, [p])
                  (_, Just a, Nothing) -> Just (if null basicHints then [a] else basicHints, [])
                  (_, Nothing, Just p) -> Just (basicHints, [p])
                  (_, _, _) -> Nothing)
          -- In case a type with trace is found, we check if we can build a hint with the last type in it.         
          buildNestedHints cedge mt t = do
            theTrace <- buildReductionTrace cedge mt
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
                Just (cl, cr, c) -> do
                  trc <- squashTrace <$> buildReductionTrace cedge cl
                  let redHint = addReduction (Just trc)
                  let lastT = getLastTypeInTrace trc
                  if typeIsInType (fromMaybe cl lastT) pmt
                    then let
                      because_hint = addHint "because" ("could not assign " ++ (show . show) mt ++ " to " ++ (show . show) mv ++ ". " ++ 
                                                      (show . show) mv ++ " is quantified with a (implicit) forall and cannot be assigned any specific type")
                      reductionHint = addHint "injectivity info" (
                        "From\t: " ++ show c ++
                        "\nGot\t: " ++ show cn 
                        )
                      in return $ Just (5, "Tried to inject untouchable", constr, eid, addProperty (InjectUntouchable (lastT, cl) cr) $ because_hint $ reductionHint $ redHint ci, gm)
                    else return Nothing
            _ -> return Nothing
        _ -> return Nothing

-- Works on typefamilies where a right to left improvement should have been performed but isn't because it was not specified to be injective.
shouldBeInjectiveHeuristic :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic
shouldBeInjectiveHeuristic path = SingleVoting "Not injective enough" f
  where
    f (constr, eid, ci, _) = do
      graph <- getGraph
      let constr' = fromMaybe constr (maybeHasOriginalTypeSignature ci)
      case constr' of
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
              (MType mf') <- if isBetaFree mf then return (MType mf) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              case injHint of
                Nothing -> return Nothing
                Just iHint -> do 
                  theTrace <- buildReductionTrace cedge mf'
                  let redHint = addReduction (Just theTrace)
                  case theTrace of 
                    [] -> if typeFamInType fn pmt
                      then return $ Just (7, "Should be injective, without trace", constr', eid, addProperty (TypeFamilyReduction Nothing mf' Nothing mt False) $ iHint ci, replaceTypeFamModifiers [(Just mf, mt)] constr')
                      else return Nothing
                    trc -> do
                      let Just lastT = getLastTypeInTrace trc
                      let Just firstT = getFirstTypeInTrace trc
                      if typeIsInType lastT pmt
                        then return $ Just (7, "Should be injective, with trace", constr', eid, addProperty (TypeFamilyReduction (Just lastT) firstT Nothing mt False) $ redHint $ iHint ci, replaceTypeFamModifiers [(Just lastT, mt)] constr')
                        else return Nothing
            _ -> return Nothing
        _ -> return Nothing

        where

          buildNestedInjHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                             => TGEdge (Constraint ConstraintInfo) -> MonoType -> MonoType -> m (Maybe (ConstraintInfo -> ConstraintInfo))
          buildNestedInjHint cedge mf@(MonoType_Fam fn mts _) mt = do
            axs <- getAxioms
            -- Make sure that both types are substituted
            (MType mf'@(MonoType_Fam fn' mts' _)) <- if all isBetaFree mts then return (MType mf) else getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
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
                  possibleInjCombs <- mapM (checkNewInjectivity fn axs mf mt) pSet
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

          -- Updates the axiom to adapt its injectivity (so we can check if the new injectivity fixes stuff)
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
          
          -- Gets the touchable variables and their index from the argument monotypes of (for example) a type family
          getTchMtsFromArgs :: (IsTouchable m TyVar, Fresh m) => MonoTypes -> m [(Int, MonoType)]
          getTchMtsFromArgs mts = do
            let vars = [(i, x) | (i, x) <- zip [0..] mts, isVar x]
            filterM (\(_, MonoType_Var _ v _) -> isJust <$> isVertexTouchable v) vars

            where
              isVar MonoType_Var{} = True
              isVar _              = False
          
          -- Checks if the right hand side of the constraint, is unifiable with an axiom. If so, an injectivity fix may be presented.
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

          -- Gets injectivity info for the family (the String) from the axioms we have.
          -- Returns the injective indices (if any).
          obtainInjInfoFromAxs :: String -> [Axiom ConstraintInfo] -> [Int]
          obtainInjInfoFromAxs fn (Axiom_Injective afn idx:axs) = if fn == afn then idx else obtainInjInfoFromAxs fn axs
          obtainInjInfoFromAxs fn (_:axs) = obtainInjInfoFromAxs fn axs
          obtainInjInfoFromAxs _  [] = []

          -- Builds a map from index to Name (the original Name in the code)
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

isFam :: MonoType -> Bool
isFam MonoType_Fam{} = True
isFam _              = False

filterAxiomsOnName :: String -> [Axiom ConstraintInfo] -> [Axiom ConstraintInfo]
filterAxiomsOnName fn (ax@(Axiom_Unify _ (Just tfi)):axs) = if show (tfiName tfi) == fn then ax : filterAxiomsOnName fn axs else filterAxiomsOnName fn axs
filterAxiomsOnName fn (Axiom_ClosedGroup fn' axs:axs') = if fn == fn' then axs else filterAxiomsOnName fn axs'
filterAxiomsOnName fn (_:axs) = filterAxiomsOnName fn axs
filterAxiomsOnName _ _ = []

-- Check if type fam occurs in type
typeFamInType :: String -> MonoType -> Bool
typeFamInType s (MonoType_Fam fn mts _) = let
  in fn == s || any (typeFamInType s) mts
typeFamInType s (MonoType_App m1 m2 _) = typeFamInType s m1 || typeFamInType s m2
typeFamInType _ (MonoType_Con _ _)     = False
typeFamInType _ MonoType_Var{}         = False

-- Replace a MonoType (1) with a MonoType (2) in a MonoType (3) and return the new MonoType (4)
repTypeInMonoType :: MonoType -> MonoType -> MonoType -> MonoType
repTypeInMonoType lmt rmt mt@(MonoType_App ma1 ma2 rs) = let
  (lmt', mt') = freshenTypes lmt mt
  in if lmt' == mt'
    then rmt
    else MonoType_App (repTypeInMonoType lmt rmt ma1) (repTypeInMonoType lmt rmt ma2) rs
repTypeInMonoType lmt rmt mt@(MonoType_Fam f mts rs) = let
  (lmt', mt') = freshenTypes lmt mt
  in if lmt' == mt'
    then rmt
    else MonoType_Fam f (map (repTypeInMonoType lmt rmt) mts) rs
repTypeInMonoType lmt rmt mt@MonoType_Var{} = let
  (lmt', mt') = freshenTypes lmt mt
  in if lmt' == mt'
    then rmt
    else mt
repTypeInMonoType lmt rmt mt@MonoType_Con{} = if lmt == mt
  then rmt
  else mt

-- Replace a MonoType (1) with a MonoType (2) in a PolyType (3) and return the new PolyType (4)
repTypeInPolyType :: MonoType -> MonoType -> PolyType ConstraintInfo -> PolyType ConstraintInfo
repTypeInPolyType lmt rmt (PolyType_Bind s b) = let
  ((tv, pt), _) = contFreshMRes (unbind b) 0
  in PolyType_Bind s $ bind tv (repTypeInPolyType lmt rmt pt)
repTypeInPolyType lmt rmt (PolyType_Mono cs mt) = PolyType_Mono cs (repTypeInMonoType lmt rmt mt)

-- GraphModifier that substitutes the Family in it (MonoType 1, lmt) with what the type inference expected (MonoType 2, rmt)
-- in the constraint that was considered in the heuristic.
replaceTypeFamModifiers :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic)
                        => [(Maybe MonoType, MonoType)] -> Constraint ConstraintInfo -> GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
replaceTypeFamModifiers mts oldConstr (eid, _, ci) graph' = do
  let cedge = getEdgeFromId graph' eid
      constr = getConstraintFromEdge cedge
  case constr of
    -- Get the instantiation constraint (the one that was considered in the heuristic)
    Constraint_Inst imt pt rs -> do
      let newPmt = foldl (\ pt' (lmt, rmt) -> maybe pt' (\lmt' -> repTypeInPolyType lmt' rmt pt') lmt) pt mts
          newConstr = Constraint_Inst imt newPmt (Just $ addProperty (HasOriginalTypeSignature oldConstr) (fromMaybe emptyConstraintInfo rs))
          isG = isEdgeGiven cedge
          isOriginal = isEdgeOriginal cedge
        -- Update the graph with the new constraint.
      gNewConstr <- convertConstraint [] isOriginal isG (getGroupFromEdge cedge) (getPriorityFromEdge cedge) newConstr
      remGraph <- removeEdge eid  graph'
      return $ (, ci) $ mergeGraphs remGraph [gNewConstr]
    _ -> return (graph', ci)