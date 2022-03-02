{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
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
import Rhodium.TypeGraphs.GraphReset 
import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree

import Data.List
import Data.Maybe
import qualified Data.Map as M


import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Fresh
import Control.Monad.IO.Class (MonadIO)

import Control.Monad

import Debug.Trace

isFolklore :: ConstraintInfo -> Bool 
isFolklore cinfo = or [ True | FolkloreConstraint <- properties cinfo ]

avoidFolkloreHeuristic :: Monad m => Heuristic m axiom touchable types constraint ConstraintInfo
avoidFolkloreHeuristic = edgeFilter "Avoid folklore constraint" f
    where
        f (_, _, ci, _) = return (not (isFolklore ci))


removeEdgeAndTsModifier :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
removeEdgeAndTsModifier (eid, constraint, ci) graph = do
    let cedge = getEdgeFromId graph eid 
    case getConstraintFromEdge cedge of
        Constraint_Unify mv _ _ -> do
            let es' = filter (\e -> isConstraintEdge e && isInstConstraint (getConstraintFromEdge e)  && firstConstraintElement (getConstraintFromEdge e) == mv ) $ M.elems (edges graph) --
            (\g -> (g, foldr (\e ci -> let 
                    Constraint_Inst _ ts _ = getConstraintFromEdge e
                in addProperty (ApplicationTypeSignature ts) ci ) ci es')) <$> foldM (flip removeEdge) graph (eid : map edgeId es')
        _ -> (\g -> (g, ci)) <$> removeEdge eid graph
           


avoidForbiddenConstraints :: (Fresh m, Monad m) => Heuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
avoidForbiddenConstraints = 
    Filter "Avoid forbidden constraints" (return . mapMaybe f)
        where 
            f (eid, c, info, gm) | isHighlyTrusted info = Nothing
                                 | otherwise = Just (eid, c, info, removeEdgeAndTsModifier) 


phaseFilter :: Monad m => Heuristic m axiom touchable types (Constraint ConstraintInfo) ConstraintInfo
phaseFilter =  let f (_, _, info, gm) = return (phaseOfConstraint info)
               in maximalEdgeFilter "Highest phase number" f

trustFactor :: ConstraintInfo -> Float
trustFactor info = fromMaybe 0 (maybeHead [f | (HasTrustFactor f) <- properties info])

avoidTrustedConstraints :: Monad m => Heuristic m axiom touchable types (Constraint ConstraintInfo) ConstraintInfo
avoidTrustedConstraints = 
        let f (_, _, info, gm) = return (trustFactor info)
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


avoidApplicationConstraints :: 
    (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) 
    => Heuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
avoidApplicationConstraints = 
    edgeFilter "Avoid application constraints" f
    where
        f pair@(constraint, edgeId, info, gm) = 
            case constraint of
                Constraint_Inst{} -> return True
                Constraint_Unify t1 t2 _ ->
                    case maybeNumberOfArguments info of
                        Nothing -> return True
                        Just nrArgs -> do
                            graph <- getGraph
                            let edge = getEdgeFromId graph edgeId
                            doWithoutEdge edgeId $
                                do              
                                    maybeFunctionType <- getSubstTypeFull (getGroupFromEdge edge) $ MType t1
                                    maybeExpectedType <- getSubstTypeFull (getGroupFromEdge edge) $ MType t2
                                    
                                    case (maybeFunctionType,maybeExpectedType) of    
                                        (MType functionType, MType expectedType) -> do
                                            axioms <- getAxioms
                                            isSame <- runTG (unifyTypes axioms [] [Constraint_Unify (monotypeTuple xs) (monotypeTuple ys) Nothing] ((fvToList (monotypeTuple xs) :: [TyVar]) ++ fvToList (monotypeTuple ys)))     
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
        f pair@(constraint, eid, info, gm) =
            case maybeNegation info of
                Nothing -> return True
                Just isIntNegation -> case constraint of
                    Constraint_Inst t1 t2 _ -> do
                        graph <- getGraph
                        let edge = getEdgeFromId graph eid
                        doWithoutEdge eid $  
                            do  
                                PType t2' <- getSubstTypeFull (getGroupFromEdge edge) $ PType t2                  
                                axioms <- getAxioms
                                freshV <- fresh (string2Name "a")
                                let testtp = MonoType_Con (if isIntNegation then "Int" else "Float") Nothing :-->: var freshV
                                unif <- runTG (unifyTypes axioms [] [Constraint_Inst testtp t2' Nothing] (freshV : fvToList t2'))
                                return (isNothing unif)
                    _ -> return True

resultsEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((constraint, EdgeId, info, GraphModifier m axiom touchable types constraint info) -> m a) -> Heuristic m axiom touchable types constraint info
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

maximalEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, info, GraphModifier m axiom touchable types constraint info) -> m a) -> Heuristic m axiom touchable types constraint info
maximalEdgeFilter = resultsEdgeFilter maximum

minimalEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, info, GraphModifier m axiom touchable types constraint info) -> m a) -> Heuristic m axiom touchable types constraint info
minimalEdgeFilter = resultsEdgeFilter minimum
                        
edgeFilter :: (Monad m) => String -> ((constraint, EdgeId, info, GraphModifier m axiom touchable types constraint info) -> m Bool) -> Heuristic m axiom touchable types constraint info
edgeFilter description function = 
    Filter description g
        where 
            g es = do  
                xs <- filterM function es
                return (if null xs then es else xs)

