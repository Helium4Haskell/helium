

module Helium.StaticAnalysis.HeuristicsOU.FilterHeuristics where


import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper 

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances

import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.Path
import Rhodium.Blamer.HeuristicsUtils
import Rhodium.Core
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree

import Data.List
import Data.Maybe
import qualified Data.Map as M


import Unbound.LocallyNameless
import Unbound.LocallyNameless.Fresh

import Control.Monad

import Debug.Trace

isFolklore :: ConstraintInfo -> Bool 
isFolklore cinfo = or [ True | FolkloreConstraint <- properties cinfo ]

avoidFolkloreHeuristic :: Monad m => Heuristic m axiom touchable types constraint ConstraintInfo
avoidFolkloreHeuristic = edgeFilter "Avoid folklore constraint" f
    where
        f (_, _, ci) = return (not (isFolklore ci))


--highParticipation :: (HasTypeGraph FreshM Axiom TyVar RType Constraint ConstraintInfo, HasLogInfo FreshM) => Double -> Path FreshM Axiom TyVar RType Constraint ConstraintInfo -> Heuristic FreshM Axiom TyVar RType Constraint ConstraintInfo
highParticipation ratio path =
    Filter ("Participation ratio [ratio="++show ratio++"]") selectTheBest
        where
            selectTheBest es = do
                graph <- getGraph
                let (nrOfPaths, fm)   = participationMap (getProblemEdges graph [])
                    participationList = M.filterWithKey p fm
                    p cnr _    = cnr `elem` activeCNrs
                    activeCNrs = [ cnr | (_, cnr, _) <- es ]
                    maxInList  = maximum (M.elems participationList)
                    limit     -- test if one edge can solve it completely
                        | maxInList == nrOfPaths = maxInList 
                        | otherwise              = round (fromIntegral maxInList * ratio) `max` 1
                    goodCNrs   = M.keys (M.filter (>= limit) participationList)
                    bestEdges  = filter (\(_, cnr,_) -> cnr `elem` goodCNrs) es
            
                    -- prints a nice report
                    mymsg  = unlines ("" : title : replicate 100 '-' : map f es)
                    title  = "cnr  constraint                                                                ratio   info"
                    f ((cons, cnr, info)) = 
                        take 5  (show cnr++(if cnr `elem` goodCNrs then "*" else "")++repeat ' ') ++
                        take 74 (show cons++repeat ' ') ++
                        take 8  (show (M.findWithDefault 0 cnr fm * 100 `div` nrOfPaths)++"%"++repeat ' ') ++
                        "{"++show info++"}"
                logMsg mymsg
                return $ if null bestEdges then es else bestEdges
                        
avoidForbiddenConstraints :: Monad m => Heuristic m axiom touchable types (Constraint ConstraintInfo) ConstraintInfo
avoidForbiddenConstraints = 
    edgeFilter "Avoid forbidden constraints" f
        where 
            f (_, _, info) = return (not (isHighlyTrusted info))


phaseFilter :: Monad m => Heuristic m axiom touchable types (Constraint ConstraintInfo) ConstraintInfo
phaseFilter =  let f (_, _, info) = return (phaseOfConstraint info)
               in maximalEdgeFilter "Highest phase number" f

trustFactor :: ConstraintInfo -> Float
trustFactor info = fromMaybe 0 (maybeHead [f | (HasTrustFactor f) <- properties info])

avoidTrustedConstraints :: Monad m => Heuristic m axiom touchable types (Constraint ConstraintInfo) ConstraintInfo
avoidTrustedConstraints = 
        let f (_, _, info) = return (trustFactor info)
        in minimalEdgeFilter "Trust factor of edge" f


class MaybeApplication a where
    maybeNumberOfArguments :: a -> Maybe Int
    maybeApplicationEdge   :: a -> Maybe (Bool, [(UHA_Source, MonoType)])

instance MaybeApplication ConstraintInfo where
    maybeNumberOfArguments = 
        fmap (length . snd) . maybeApplicationEdge
        
    maybeApplicationEdge cinfo = 
        let list = [ (b, zip (map self infoTrees) (map (var . fromJust) tps))
                    | ApplicationEdge b infoTrees <- properties cinfo
                    , let tps = map assignedType infoTrees
                    , all isJust tps
                    ]
        in case list of 
                []      -> Nothing
                tuple:_ -> Just tuple


avoidApplicationConstraints :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => Heuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
avoidApplicationConstraints = 
    edgeFilter "Avoid application constraints" f
    where
        f pair@(constraint, edgeId, info) = 
            case constraint of
                Constraint_Inst _ _ _ -> return True
                Constraint_Unify t1 t2 _ ->
                    case maybeNumberOfArguments info of
                        Nothing -> return True
                        Just nrArgs ->
                            doWithoutEdge edgeId $
                                do              
                                    maybeFunctionType <- getSubstType $ MType t1
                                    maybeExpectedType <- getSubstType $ MType t2
                                    
                                    case (maybeFunctionType,maybeExpectedType) of    
                                        (MType functionType, MType expectedType) -> do
                                            axioms <- getAxioms
                                            isSame <- runTG (unifyTypes axioms [] [Constraint_Unify (monotypeTuple xs) (monotypeTuple ys) Nothing] ((fv (monotypeTuple xs) :: [TyVar]) ++ fv (monotypeTuple ys)))     
                                            return (not (length xs == nrArgs && length ys == nrArgs && isJust isSame))               
                                            where 
                                                xs         = fst (functionSpineOfLength nrArgs functionType)
                                                ys         = fst (functionSpineOfLength nrArgs expectedType)  
                                        _ -> return True    


class MaybeNegation a where
    maybeNegation :: a -> Maybe Bool
    
instance MaybeNegation ConstraintInfo where
    maybeNegation cinfo = 
        case (self . attribute . localInfo) cinfo of
            UHA_Expr (Expression_Negate      _ _) -> Just True
            UHA_Expr (Expression_NegateFloat _ _) -> Just False
            _                                     -> Nothing
     

avoidNegationConstraints :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => Heuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
avoidNegationConstraints = 
    edgeFilter "Avoid negation constraints" f
    where
        f pair@(constraint, eid, info) =
            case maybeNegation info of
                Nothing -> return True
                Just isIntNegation -> case constraint of
                    Constraint_Inst t1 t2 _ ->
                        doWithoutEdge eid $  
                            do  
                                PType t2' <- getSubstType $ PType t2                  
                                axioms <- getAxioms
                                freshV <- fresh (string2Name "a")
                                let testtp = (if isIntNegation then MonoType_Con "Int" else MonoType_Con "Float") :-->: var freshV
                                unif <- runTG (unifyTypes axioms [] [Constraint_Inst testtp t2' Nothing] (freshV : (fv t2')))    
                                return (isNothing unif)
                    _ -> return True

resultsEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((constraint, EdgeId, info) -> m a) -> Heuristic m axiom touchable types constraint info
resultsEdgeFilter selector description function =
    Filter description $ \es -> 
            do 
                tupledList <-    let f tuple = 
                                        do  result <- function tuple
                                            return (result, tuple)
                                in mapM f es
                let maximumResult 
                        | null tupledList = error "resultsEdgeFilter, unexpected empty list" 
                        | otherwise       = selector (map fst tupledList)
                return (map snd (filter ((maximumResult ==) . fst) tupledList))

maximalEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, info) -> m a) -> Heuristic m axiom touchable types constraint info
maximalEdgeFilter = resultsEdgeFilter maximum

minimalEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, info) -> m a) -> Heuristic m axiom touchable types constraint info
minimalEdgeFilter = resultsEdgeFilter minimum

edgeFilter :: Monad m => String -> ((constraint, EdgeId, info) -> m Bool) -> Heuristic m axiom touchable types constraint info
edgeFilter description function = 
    Filter description $ \es -> 
        do  xs <- filterM function es
            return (if null xs then es else xs)

