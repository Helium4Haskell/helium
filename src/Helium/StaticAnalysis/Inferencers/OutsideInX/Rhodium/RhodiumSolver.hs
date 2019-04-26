module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumSolver(rhodiumSolve, solveOU) where

import Rhodium.Core
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.TGState hiding (graph)
import Rhodium.TypeGraphs.Graph
import Rhodium.Solver.Rules
import Rhodium.Solver.SolveResult
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.ResidualHeuristics 

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Name

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Messages.HeliumMessages
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances

import Helium.StaticAnalysis.HeuristicsOU.FilterHeuristics
import Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics
import Helium.StaticAnalysis.HeuristicsOU.ResidualHeuristics
import Helium.StaticAnalysis.HeuristicsOU.GADTHeuristics 

import Data.Maybe
import Data.List

import Debug.Trace

rhodiumSolve :: [Axiom] -> [Constraint] -> [Constraint] -> [TyVar] -> SolveResult TyVar RType Constraint ConstraintInfo
rhodiumSolve axioms given wanted touchables = contFreshM (runTG (solve (solveOptions []) axioms given wanted touchables)) 20

solveOU :: Sibblings -> [Axiom] -> [Constraint] -> [Constraint] -> [TyVar] -> FreshM (SolveResult TyVar MonoType Constraint ConstraintInfo)
solveOU sibblings axioms given wanted tchs = trace (unlines $ map (\e -> show (e, getConstraintInfo e)) wanted) $ traceShow (given, tchs) $ let
    in do 
        
        rf <- runTG (solve (solveOptions sibblings) axioms (nub given) (nub wanted) (nub tchs))
        return SolveResult{
            substitution = map (\(t, MType m) -> (t, m)) (substitution rf),
            errors = errors rf,
            smallGiven = smallGiven rf,
            touchables = touchables rf
        }

solveOptions sibblings = emptySolveOptions{
        typeHeuristics = listOfTypeHeuristics sibblings,
        residualHeuristics = listOfResidualHeuristics
        }
        

listOfTypeHeuristics sibblings path = [
        avoidForbiddenConstraints,
        highParticipation 0.95 path,
        phaseFilter,
        Voting [
            sibblingsHeuristic sibblings,
            siblingLiterals, 
            applicationHeuristic,
            variableFunction,
            tupleHeuristic,
            fbHasTooManyArguments,
            constraintFromUser path,
            unreachablePatternHeuristic

        ],
        avoidNegationConstraints,
        avoidApplicationConstraints,
        avoidFolkloreHeuristic,
        avoidTrustedConstraints
    ]

listOfResidualHeuristics path = [
        avoidForbiddenResidualConstraints,
        VotingResidual [
            typeSignatureTooGeneral,
            missingPredicate path
        ],
        avoidTrustedResidualConstraints
    ]