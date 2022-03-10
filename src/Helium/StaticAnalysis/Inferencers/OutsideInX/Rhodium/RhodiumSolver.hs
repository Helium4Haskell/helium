{-# LANGUAGE FlexibleContexts #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumSolver(rhodiumSolve, solveOU) where

import Rhodium.Core
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.TGState hiding (graph)
import Rhodium.TypeGraphs.Graph
import Rhodium.Solver.Rules
import Rhodium.Solver.SolveResult
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.ResidualHeuristics 

import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.Name

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Messages.HeliumMessages
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
--import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances()

import Helium.StaticAnalysis.HeuristicsOU.FilterHeuristics
import Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics
import Helium.StaticAnalysis.HeuristicsOU.ResidualHeuristics
import Helium.StaticAnalysis.HeuristicsOU.GADTHeuristics 

import Data.Maybe
import Data.List

import Debug.Trace
import Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics (typeErrorThroughReduction)
import Helium.Main.Args (Option (ShowTFTrace))

rhodiumSolve :: [Axiom ConstraintInfo] -> [Constraint ConstraintInfo] -> [Constraint ConstraintInfo] -> [TyVar] -> SolveResult TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
rhodiumSolve axioms given wanted touchables = contFreshM (runTG (solve (solveOptions False []) axioms given wanted touchables)) 20

solveOU :: [Option] -> Sibblings -> [Axiom ConstraintInfo] -> [Constraint ConstraintInfo] -> [Constraint ConstraintInfo] -> [TyVar] -> FreshM (SolveResult TyVar MonoType (Constraint ConstraintInfo) ConstraintInfo)
solveOU options sibblings axioms given wanted tchs = 
    trace (unlines (map (\e -> "WANTED CONSTRAINT: " ++ show (e, getConstraintInfo e)) wanted)) $ traceShow (given, tchs) $
      do      
        rf <- runTG (solve (solveOptions (ShowTFTrace `elem` options) sibblings) axioms (nub given) (nub wanted) (nub tchs))
        return SolveResult{
            substitution = map (\(t, MType m) -> (t, m)) (substitution rf),
            errors = errors rf,
            smallGiven = smallGiven rf,
            touchables = touchables rf
        }

solveOptions showTrace sibblings = emptySolveOptions{
        typeHeuristics = listOfTypeHeuristics sibblings,
        teMustShowTrace = showTrace
        }
        

listOfTypeHeuristics sibblings path = [
        avoidForbiddenConstraints,
        highParticipation 0.95 path,
        phaseFilter,
        Voting [
           
            siblingsHeuristic sibblings,
            siblingLiterals, 
            applicationHeuristic,
            variableFunction,
            tupleHeuristic,
            fbHasTooManyArguments,
            constraintFromUser path,
            unreachablePatternHeuristic path,
            typeErrorThroughReduction path,
            typeSignatureTooGeneral path,
            missingPredicate path,
            missingGADTSignature path,
            escapingGADTVariableHeuristic path
        ],
        avoidNegationConstraints,
        avoidApplicationConstraints,
        avoidFolkloreHeuristic,
        avoidTrustedConstraints
    ]
