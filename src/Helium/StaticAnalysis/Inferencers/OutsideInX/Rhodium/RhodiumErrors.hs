{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumErrors where

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Fresh

import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Graph
import Rhodium.Blamer.HeuristicProperties
import Rhodium.Solver.Rules

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper
import Helium.StaticAnalysis.Messages.TypeErrors hiding (makeNotGeneralEnoughTypeError, makeReductionError, makeMissingConstraintTypeError, makeUnresolvedOverloadingError)
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumGenerics
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.Syntax.UHA_Utils
import Helium.StaticAnalysis.Messages.HeliumMessages


import Helium.Syntax.UHA_Range
import Helium.Syntax.UHA_Syntax

import Data.Maybe
import Data.List

import Debug.Trace
import Data.Graph (Edge)


instance HasConstraintInfo (Constraint ConstraintInfo) ConstraintInfo where
    getConstraintInfo (Constraint_Unify _ _ ci) = ci
    getConstraintInfo (Constraint_Inst _ _ ci) = ci
    getConstraintInfo (Constraint_Exists _ ci) = ci
    getConstraintInfo (Constraint_Class _ _ ci) = ci
    getConstraintInfo c = error ("No constraint info for " ++ show c)
    setConstraintInfo ci (Constraint_Unify m1 m2 _) = Constraint_Unify m1 m2 (Just ci)


instance (MonadFail m, CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => TypeErrorInfo m (Constraint ConstraintInfo) ConstraintInfo where
    createTypeError edge li constraint ci = maybe nError (return . const ci) (errorMessage ci)
        where
            nError
                | li == labelIncorrectConstructors && isJust (maybeUnreachablePattern ci) =
                    do
                        let Just (expected, function) = maybeUnreachablePattern ci
                        let Just tsLoc = maybeTypeSignatureLocation ci
                        return ci{
                            errorMessage = Just $ makeUnreachablePatternError (fst $ sources ci) tsLoc expected function (maybePossibleTypeSignature ci)
                        }
                        --error $ show (expected, function)
                | li == labelIncorrectConstructors || li == labelInfiniteType || isTypeError ci || isTooManyFBArgs ci =
                    do
                        te <- makeUnificationTypeError edge constraint ci
                        return ci{
                            errorMessage = Just te
                        }
                | li == labelResidual && isJust (maybeMissingConcreteInstance ci) =
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                axioms <- getAxioms
                                let mmtype = MType m1
                                MType m1' <- getSubstTypeFull (getGroupFromEdge edge) mmtype
                                let Just (cn, m) = maybeMissingConcreteInstance ci
                                let [MType m1'', PType p2', MType m'] = freshenRepresentation [MType m1', PType p2, MType m]

                                    source = fst (sources ci)
                                    extra  = (m1'', Just p2')
                                return ci{
                                            errorMessage = Just $ makeReductionError source Nothing extra axioms (cn, m)
                                        }
                | li == labelResidual && isJust (maybeAmbigiousClass ci) =
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                let Just cc = maybeAmbigiousClass ci
                                PType scheme1 <- getSubstTypeFull (getGroupFromEdge edge) (PType p2)
                                MType scheme2 <- getSubstTypeFull (getGroupFromEdge edge) (MType m1)
                                let [PType scheme1', MType scheme2'] = freshenRepresentation [PType scheme1, MType scheme2]
                                let Just classConstraint = maybeAmbigiousClass ci
                                return ci{
                                    errorMessage = Just $ makeUnresolvedOverloadingError (fst $ sources ci) classConstraint (scheme1', scheme2')
                                }
                | li == labelResidual && isJust (maybeAddConstraintToTypeSignature ci) =
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                let Just (m, cc) = maybeAddConstraintToTypeSignature ci
                                case m of
                                    Nothing -> do
                                        axioms <- getAxioms
                                        let fbType = fromMaybe (error "No relevant function binding present") (maybeRelevantFunctionBinding ci)
                                        let Just fbci = getConstraintInfo fbType
                                        let fb = firstConstraintElement fbType
                                        --let Constraint_Unify fb _ (Just fbci) = error $ show fbType
                                        let source = fst (sources fbci)
                                        fb' <- getSubstTypeFull (getGroupFromEdge edge) $ MType fb
                                        let Constraint_Class nc [mt] _ = cc
                                        MType mt' <- getSubstTypeFull (getGroupFromEdge edge) (MType mt)
                                        let [MType fb'', MType mt''] = freshenRepresentation [fb', MType mt']
                                        let extra = (fb'', Nothing)
                                        return ci{
                                            errorMessage = Just $ makeReductionError source (Just $ fst (sources ci)) extra axioms (nc, mt'')
                                        }
                                    Just (cts, eid, cits) -> do
                                        let range   = fromMaybe (rangeOfSource $ fst $ sources ci) (maybeTypeSignatureLocation ci)
                                        let mSource = if isExprTyped ci then Nothing else Just (fst $ sources ci)
                                        -- MType m1' <- getSubstTypeFull (getGroupFromEdge edge) (MType m1)
                                        PType p2' <- getSubstTypeFull (getGroupFromEdge edge) (PType p2)
                                        let Just usages = maybeClassUsages ci
                                        let mGadtTs = if isGADTTypeSignature ci then maybeTypeSignatureLocation cits else Nothing
                                        return ci{
                                            errorMessage = Just $ makeMissingConstraintTypeError ci range mSource p2' (True, cc) (map (fst . sources . (\(_, _, c) -> c)) usages) mGadtTs
                                        }
                | li == labelResidual && isJust (maybeMissingGADTTypeSignature ci) = do
                        let Just (pt, function, branches) = maybeMissingGADTTypeSignature ci
                        return ci{
                            errorMessage = Just $ makeMissingTypeSignature function branches pt
                        }
                | li == labelResidual && isJust (maybeEscapingExistentital ci) = do
                        let Just (mmt, cons) = maybeEscapingExistentital ci
                        mmt' <- either (return . Left) (\mt -> (\m -> Right (mt, fromMType m)) <$> getSubstTypeFull (getGroupFromEdge edge) (MType mt)) mmt

                        let source = fst $ sources ci
                        let Constraint_Unify m1 _ _ = constraint
                        MType m1' <- getSubstTypeFull (getGroupFromEdge edge) $ MType m1
                        err <- makeEscapingVariable source cons mmt' m1'

                        return ci{
                            errorMessage = Just err
                        }
                | li == labelResidual =
                        case constraint of
                            Constraint_Inst m1 m2 _ -> do
                                MType scheme1 <- getSubstTypeFull (getGroupFromEdge edge) (MType m1) >>= getSubstTypeFull (getGroupFromEdge edge)
                                --PType scheme2 <- getSubstType (PType m2)
                                let [MType scheme1', PType m2'] = freshenRepresentation [MType scheme1, PType m2]
                                let
                                    range   = fromMaybe err (maybeTypeSignatureLocation ci)
                                    source  = uncurry fromMaybe (sources ci)
                                    err     = noRange -- error "unknown original type scheme"

                                    te = makeNotGeneralEnoughTypeError (isExprTyped ci) range source scheme1' m2'
                                return ci{
                                    errorMessage = Just te
                                }
                            c -> return ci{
                                    errorMessage = Just $ TypeError [] [MessageOneLiner (MessageString ("Unknown residual constraint: " ++ show c))] [] []
                                }
                | "Touchable touched:" `isPrefixOf` show li   =
                    return ci{
                            errorMessage = Just $ TypeError [] [MessageOneLiner (MessageString ("Unknown residual constraint: " ++ show constraint))] [] []
                            }
                | otherwise = error ("Unknown error label: " ++ show li)

makeEscapingVariable :: Monad m => UHA_Source -> Constraint ConstraintInfo -> Either MonoType (MonoType, MonoType) -> MonoType -> m TypeError
makeEscapingVariable source patternConstraint mt unif = do

        let
            range = rangeOfSource source
            oneliner = MessageOneLiner (MessageString ("Cannot unify variable in " ++ descriptionOfSource source))
            (constructor, constructorCi) = case patternConstraint of
                Constraint_Inst _ p pci -> (p, pci)
                Constraint_Unify _ m1 mci -> (PolyType_Mono [] m1, mci)
            constructorTs = fromMaybe noRange (constructorCi >>= maybeTypeSignatureLocation)
        let
            table = (descriptionOfSource source <:> MessageOneLineTree (oneLinerSource source)) :
                case mt of
                    Left m -> let
                            [MType m', PType constructor'] = freshenRepresentation [MType m, PType constructor]

                        in [
                            "type"  >:> MessageMonoType m'
                        ,   "constructor" >:> MessagePolyType constructor'
                        ,   "defined at" >:> MessageRange constructorTs
                        , "hint" <:> MessageString ("The type in the constructor represents an existential type, which cannot be used as a universal type in the expression")
                        ]
                    Right (me, mt) -> let
                            [MType me', MType mt', PType constructor'] = freshenRepresentation [MType me, MType unif, PType constructor]
                        in [
                            "existential type"  >:> MessageMonoType me'
                        ,   "cannot be unified with" >:> MessageMonoType mt'
                        ,   "constructor" >:> MessagePolyType constructor'
                        ,   "defined at" >:> MessageRange constructorTs
                        ]
        return $ TypeError [range] [oneliner] table []

makeUnreachablePatternError :: UHA_Source -> Range -> MonoType -> MonoType -> Maybe (PolyType ConstraintInfo) -> TypeError
makeUnreachablePatternError source functionRange expected inferred possibleTS=
    let
        (expected', inferred', possibleTS') = case possibleTS of
            Nothing -> let [MType e', MType i'] = freshenRepresentation [MType expected, MType inferred :: RType ConstraintInfo] in (e', i', Nothing)
            Just ts -> let [MType e', MType i', PType ts'] = freshenRepresentation [MType expected, MType inferred, PType ts] in (e', i', Just ts')
        range = rangeOfSource source
        oneliner = MessageOneLiner (MessageString "Pattern is not accessible")
        table = [
                    "Pattern" <:> MessageOneLineTree (oneLinerSource source)
                ,   "constructor type" >:> MessageMonoType expected'
                ,   "defined at" >:> MessageRange functionRange
                ,   "inferred type of pattern" >:> MessageMonoType inferred'
            ]
        hints = ("hint", MessageString "change the type signature, remove the branch or change the branch")
                :
                [
                    ("possible type signature", MessageString (show ps)) | Just ps <- [possibleTS']
                ]
    in TypeError [range] [oneliner] table hints

makeNotGeneralEnoughTypeError :: Bool -> Range -> UHA_Source -> MonoType -> PolyType ConstraintInfo -> TypeError
makeNotGeneralEnoughTypeError isAnnotation range source tpscheme1 tpscheme2 =
    let
        ts1      = tpscheme1
        ts2      = tpscheme2
        special  = if isAnnotation then "Type annotation" else "Type signature"
        oneliner = MessageOneLiner (MessageString (special ++ " is too general"))
        descr    = if isAnnotation then "expression" else "function"
        table    = [ descr           <:> MessageOneLineTree (oneLinerSource source)
                    , "declared type" >:> MessagePolyType ts2
                    , "inferred type" >:> MessageMonoType ts1
                    ]
        hints    = [ ("hint", MessageString "try removing the type signature") | not (null (fvToList ts1 :: [TyVar])) ]
    in TypeError [range] [oneliner] table hints


makeUnificationTypeError :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => TGEdge (Constraint ConstraintInfo) -> Constraint ConstraintInfo -> ConstraintInfo -> m TypeError
makeUnificationTypeError edge constraint info =
    do
    let (source, term) = sources info
        range    = maybe (rangeOfSource source) rangeOfSource term
        oneliner = MessageOneLiner (MessageString ("Type error in " ++ location info))
        (t1, t2) = case constraint of
            Constraint_Unify t1 t2 _-> (MType t1, MType t2)
            Constraint_Inst t1 t2 _ -> (MType t1, PType t2)
    --let    Constraint_Unify t1 t2 _ = constraint
    let t1' = case maybeApplicationTypeSignature info of
            Nothing -> t1
            Just ps -> PType ps
    msgtp1   <- getSubstTypeFull (getGroupFromEdge edge) t1'
    msgtp2   <- getSubstTypeFull  (getGroupFromEdge edge) t2
    let [msgtp2', msgtp1'] = freshenRepresentation [msgtp2, msgtp1]
    --m2Trace <- buildReductionTrace edge msgmt2
    (m2Trace, msgmt2) <- case msgtp2' of
      PType (PolyType_Mono _ mt) -> do
          tr <- buildReductionTrace edge mt
          return (tr, mt)
      MType mt -> do
          tr <- buildReductionTrace edge mt
          return (tr, mt)
    let (reason1, reason2)
            | isTooManyFBArgs info                   = ("declared type", "inferred type")
            | isFolkloreConstraint info               = ("type"         , "expected type")
            | otherwise                                = ("type"         , "does not match")
        table = [ s <:> MessageOneLineTree (oneLinerSource source') | (s, source') <- convertSources (sources info)]
                ++
                [
                    reason1 >:> case msgtp2' of
                        MType m -> MessageMonoType m
                        PType p -> MessagePolyType p
                ,   reason2 >:> case msgtp1' of
                        MType m -> MessageMonoType m
                        PType p -> MessagePolyType p                    
                ]
        hints      = [ hint | WithHint hint <- properties info ]
                   ++ [("trace " ++ show msgmt2, traceToMessageBlock (squashTrace m2Trace)) | (not . null) m2Trace]               
    return $ TypeError [range] [oneliner] table hints

makeReductionError :: UHA_Source -> Maybe UHA_Source -> (MonoType, Maybe (PolyType ConstraintInfo)) -> [Axiom ConstraintInfo] -> (String, MonoType) -> TypeError
makeReductionError source usage extra axioms (className, predicateTp) =
    let location = "function"
        message  = [ MessageOneLiner $ MessageString $ "Type error in overloaded " ++ location ]
        (predicateTp', extra')   = case extra of
            (scheme, Just tp) ->
                let [MType scheme', PType tp', MType predicateTp'] = freshenRepresentation [MType scheme, PType tp, MType predicateTp] in
                        (predicateTp', (scheme', Just tp'))
            (scheme, Nothing) ->
                let [MType scheme', MType predicateTp'] = freshenRepresentation [MType scheme :: RType ConstraintInfo, MType predicateTp] in
                    (predicateTp', (scheme', Nothing))
        tab1     = case extra' of
                        (scheme, Just tp) -> -- overloaded function

                            [ "function" <:> MessageOneLineTree (oneLinerSource source)
                            , "type"     >:> MessagePolyType tp
                            , "used as"  >:> MessageMonoType scheme
                            ]
                        (scheme, Nothing) ->
                            [
                                    "function" <:> MessageOneLineTree (oneLinerSource source)
                                ,   "inferred type"  >:> MessageMonoType scheme

                            ] ++ maybe [] (\u -> ["arising from" >:> MessageOneLineTree (oneLinerSource u)]) usage
        tab2     =  [ "problem"  <:> MessageCompose [ MessageMonoType predicateTp'
                                                    , MessageString (" is not an instance of class "++className)
                                                    ]
                    ]
    in TypeError [rangeOfSource source] message (tab1 ++ tab2) [case snd extra' of
        Just _ -> ("hint", MessageString hint)
        Nothing -> ("hint", MessageString "add a type signature to the function")
        ]
    where
        hint :: String
        hint = case valids of
                    []  -> "there are no valid instances of "++className
                    [x] -> "valid instance of "++className++" is "++show x
                    _   -> "valid instances of "++className++" are "++prettyAndList (nub valids)

        valids :: [String]
        valids = let
                        tps              = mapMaybe (instances className) axioms
                        (tuples, others) =  let     p (MonoType_Con s _) = isTupleConstructor s
                                                    p _        = False
                                            in partition (p . fst . leftSpine) tps
                    in if length tuples > 4 -- magic number!
                        then map show others ++ ["tuples"]
                        else map show tps

        instances :: String -> Axiom ConstraintInfo -> Maybe MonoType
        instances s (Axiom_Class b) = let (vars, (cond, cn, [mt])) = runFreshM $ unbind b
                                        in  if s == cn then
                                                Just mt
                                            else
                                                Nothing
        instances s _ = Nothing

makeMissingConstraintTypeError :: ConstraintInfo -> Range -> Maybe UHA_Source -> PolyType ConstraintInfo -> (Bool, Constraint ConstraintInfo) -> [UHA_Source] -> Maybe Range -> TypeError
makeMissingConstraintTypeError ci range mSource scheme (original, Constraint_Class n [ms] _) arisingFrom gadtTypeSig =

    let special  = if isJust mSource then "signature" else "annotation"
        gadtCons = [PType m | Just (Just (Constraint_Inst _ m _,_, _), _) <- [maybeAddConstraintToTypeSignature ci]] :: [RType ConstraintInfo]

        [PType scheme', MType ms'] = take 2 $ freshenRepresentation ([PType scheme :: RType ConstraintInfo, MType ms] ++ gadtCons)
        oneliner = MessageOneLiner (MessageString ("Missing class constraint in type "++special))
        gadtHint = maybe "" (\ts -> " from the GADT constructor, defined at " ++ show ts) gadtTypeSig
        table    = maybe [] (\source -> ["function" <:> MessageOneLineTree (oneLinerSource source)]) mSource ++
                    [ (isJust mSource, MessageString "declared type", MessagePolyType scheme')
                    , "class constraint" <:> MessageString (n ++ " " ++ show ms')
                    ]
        hints    = [ ("hint", MessageString $ "add the class constraint to the type signature" ++ gadtHint) | original ]
    in TypeError [range] [oneliner] table hints

makeUnresolvedOverloadingError :: UHA_Source -> Constraint ConstraintInfo -> (PolyType ConstraintInfo, MonoType) -> TypeError
makeUnresolvedOverloadingError source (Constraint_Class description _ _) (functionType, usedAsType) =
    let message = [ MessageOneLiner (MessageString ("Don't know which instance to choose for " ++ description)) ]
        table   = [ "function" <:> MessageOneLineTree (oneLinerSource source)
                    , "type"     >:> MessagePolyType functionType
                    , "used as"  >:> MessageMonoType usedAsType
                    , "hint"     <:> MessageString ( "write an explicit type for this function" ++
                                "\n   e.g. (show :: [Int] -> String)")
                    ]
    in TypeError [rangeOfSource source] message table []

makeMissingTypeSignature :: UHA_Source -> [UHA_Source] -> Maybe (PolyType ConstraintInfo) -> TypeError
makeMissingTypeSignature source branchSources mTs = let
        mTs' = case mTs of
            Nothing -> Nothing
            Just ts -> let [PType ts'] = freshenRepresentation [PType ts] in Just ts'
        message = [ MessageOneLiner (MessageString "A type signature is necessary for this definition")]
        fname = case source of
                    UHA_Decl fb -> case nameOfDeclaration fb of
                        (name:_) -> MessageString (show name)
                        _ -> MessageOneLineTree $ oneLinerSource source
                    _ -> MessageOneLineTree $ oneLinerSource source
        table = [
                "function" <:> fname
               -- "hint" <:> MessageString ("add a valid type signature" ++ maybe "" (\pt -> " , e.g. " ++ show pt) mTs)
            ]
        hints = [("hint", MessageString $ "add a valid type signature" ++ maybe "" (\pt -> ", e.g. " ++ show pt) mTs')]
    in TypeError (map rangeOfSource branchSources) message table hints

buildReductionTrace :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                    => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildReductionTrace e mt = case getMaybeReductionStep mt of
      Nothing -> case mt of
          MonoType_Fam{} -> buildNestedSteps e mt
          _                    -> return []
      Just (Step after before mconstr rt) -> do
          (MType trAfter) <- getSubstTypeFull (getGroupFromEdge e) (MType after)
          (MType trBefore) <- getSubstTypeFull (getGroupFromEdge e) (MType before)          
          trConstr <- case mconstr of 
                Just (Constraint_Unify sm1 sm2 _) -> do
                    (MType trConstrLeft) <- getSubstTypeFull (getGroupFromEdge e) (MType sm1)
                    (MType trConstrRight) <- getSubstTypeFull (getGroupFromEdge e) (MType sm2)
                    return $ Just $ Constraint_Unify trConstrLeft trConstrRight Nothing
          ih <- buildReductionTrace e trBefore
          return $ (Step trAfter trBefore trConstr rt, 1) : ih

buildNestedSteps :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                   => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildNestedSteps = buildNestedSteps' []
    where
        buildNestedSteps' seen e' mt' = do
            (MType mt'') <- getSubstTypeFull (getGroupFromEdge e') (MType mt')
            case mt'' of
                (MonoType_Fam f (m:mts) _) -> do
                    step <- getOneStep e' m
                    case step of
                      Nothing -> buildNestedSteps' (m:seen) e' (MonoType_Fam f mts Nothing)
                      Just (Step after before mconstr rt) -> do
                            ih <- buildNestedSteps' (before:seen) e' (MonoType_Fam f mts Nothing)
                            return ((Step (MonoType_Fam f (seen++(after:mts)) Nothing) (MonoType_Fam f (seen++(before:mts)) Nothing) mconstr rt, 1) : ih)
                _ -> return []


getOneStep :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                  => TGEdge (Constraint ConstraintInfo) -> MonoType -> m (Maybe ReductionStep)
getOneStep e mt = case getMaybeReductionStep mt of
    Nothing -> return Nothing
    Just (Step after before mconstr rt) -> do
        (MType trAfter) <- getSubstTypeFull (getGroupFromEdge e) (MType after)
        (MType trBefore) <- getSubstTypeFull (getGroupFromEdge e) (MType before)
        trConstr <- case mconstr of 
                Just (Constraint_Unify sm1 sm2 _) -> do
                    (MType trConstrLeft) <- getSubstTypeFull (getGroupFromEdge e) (MType sm1)
                    (MType trConstrRight) <- getSubstTypeFull (getGroupFromEdge e) (MType sm2)
                    return $ Just $ Constraint_Unify trConstrLeft trConstrRight Nothing
        return $ Just $ Step trAfter trBefore trConstr rt

squashTrace :: ReductionTrace -> ReductionTrace 
squashTrace rts = let
    
    groupedRts = groupBy (\(Step _ _ _ rt1, _) (Step _ _ _ rt2, _) -> rt1 == rt2) rts
    in map buildNewStep groupedRts
    where
        buildNewStep [s] = s 
        buildNewStep (s@(Step after _ c rt, _):groupedRt) = let
            (Step _ before _ _, _) = last groupedRt 
            in (Step after before c rt, length (s:groupedRt))

traceToMessageBlock :: ReductionTrace -> MessageBlock
traceToMessageBlock rts = let
    in MessageCompose $ mapToBlock (1 :: Int) "" rts
    where
        mapToBlock idx pre ((Step after before _ (LeftToRight _), times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ (show . show) after ++ " <--- " ++ (show . show) before ++ ". Reason: left to right application. " ++ timesToString times ++ "\n")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock idx pre ((Step after before constr CanonReduction, times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ (show . show) after ++ " <--- " ++ (show . show) before ++ " in constraint: " ++ (show . show) constr ++ ". Reason: canon reduction" ++ timesToString times ++"\n.")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock idx pre ((Step after before _ TopLevelImprovement, times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ (show . show) after ++ " <--- " ++ (show . show) before ++ ". Reason: injective top-level improvement" ++ timesToString times ++ "\n.")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock _ _ [] = []

        timesToString t = if t == 1 then "" else "Applied " ++ show t ++ " times."
