module Helium.Optimization.CountingAnalysis(countingAnalysis) where

import Helium.Optimization.LVM_Syntax

import Data.Set (Set)
import qualified Data.Set as Set

countingAnalysis :: OptimizationModule -> OptimizationModule
countingAnalysis (Module name majorV minorV decls) = Module name majorV minorV (analyseDecls decls)

analyseDecls :: Decls -> Decls
analyseDecls decls = optimizedDecls
    where optimizedDecls = decls
{-
DATA Decl
    | Start
        name                    : {I.Id}
        access                  : {Module.Access}
        encoding                : {M.Maybe I.Id}
        expr                    : Expr
    | Function
        name                    : {I.Id}
        access                  : {Module.Access}
        encoding                : {M.Maybe I.Id}
        expr                    : Expr
        customs                 : {[Module.Custom]}
        ty                      : {T.TpScheme}
    | Abstract
        name                    : {I.Id}
        access                  : {Module.Access}
        arity                   : {Module.Arity}
        customs                 : {[Module.Custom]}
        ty                      : {T.TpScheme}
    | Constructor
        name                    : {I.Id}
        access                  : {Module.Access}
        arity                   : {Module.Arity}
        tag                     : {Module.Tag}
        customs                 : {[Module.Custom]}
        datalink                : {I.Id}
        ty                      : {T.TpScheme}
    | Data
        name                    : {I.Id}
        access                  : {Module.Access}
        kind                    : {Module.DeclKind}
        customs                 : {[Module.Custom]}
        typeKind                : {Int}
    | Synonym
        name                    : {I.Id}
        access                  : {Module.Access}
        kind                    : {Module.DeclKind}
        customs                 : {[Module.Custom]}
        tpSynonym               : {Synonym}
    | Custom
        name                    : {I.Id}
        access                  : {Module.Access}
        kind                    : {Module.DeclKind}
        customs                 : {[Module.Custom]}
        -- Contains: Infix & Strategy and possibly more
-}
----------
-- Expr --
----------

type GlobalEnv = Map Id Ts
type LocalEnv = Map Id Ts
type Constraints = Set Constraint
type Solution = Map Id Ts

envMatch :: Id -> (LocalEnv,T,Constraints,a) -> (LocalEnv,Ts,T,Constraints,Solution)
envMatch id (localenv, t, constraints, a) = (Map.delete id localenv, localenv Map.! id, t, constraints, a)

constraintGen :: GlobalEnv -> ExportSym ->  DataAnns -> Expr -> Fresh (LocalEnv,T,Constraints,Solution)
constraintGen globalenv, exportsym dataanns expr = case expr of
    Lit lit -> do
        let t = lookupLit lit
        usage <- freshAnn
        return
            ( Map.empty
            , t |^| usage
            , Set.empty
            , Map.empty)
    Var name | Map.member name globalenv -> do
                let ts = globalenv Map.! name
                tvar <- freshTVar
                return
                    ( Map.empty
                    , tvar |^| annTop
                    , Set.singleton (Inst ts tvar)
                    , Map.empty)
             | otherwise -> do
                tvar <- freshTVar
                tsvar <- freshTSVar
                usage <- freshAnn
                return
                    ( Map.singleton name (tsvar |^^| (usage, annOne))
                    , tvar |^| usage
                    , Set.singleton (Inst tsvar tvar)
                    , Map.empty)
    Lam name expr1 -> do
        (localenv, tsann@(TSAnn (Anno2 (usage, demand)) ts), tann, constraints, solution) <- envMatch name <$> constraintGen globalenv exportsym dataanns expr1
        usage2 <- freshAnn
        tvar <- freshTVar
        let (localenv2, constraints2) = undefined -- usage2 `mul` localenv
        let solution' = Map.insert name tsann solution
        return
            ( localenv2
            , ((tvar |^^| (usage, demand)) |-> tann) |^| usage2
            , Set.union (Set.union constraints constraints2) (EqTs ts (t2ts tvar))
            , solution')
    Ap expr1 expr2 -> do
        (_, tsann@(TSAnn (Anno2 (usage, demand)) ts), tann, constraints, _) <- envMatch name <$> constraintGen globalenv exportsym dataanns expr1
        demand2 <- freshAnn




lookupLit :: Literal -> T
lookupLit (LInt int_) = TCon "Int"
lookupLit (LDouble double_) = TCon "Double"
lookupLit (LBytes bytes_) = TCon "Bytes"


DATA Expr
    | Let
        binds                   : Binds
        expr                    : Expr
    | Match
        name                    : {I.Id}
        alts                    : Alts
    | Ap
        expr1                   : Expr
        expr2                   : Expr
    | Lam
        name                    : {I.Id}
        expr                    : Expr
    | ConId
        name                    : {I.Id}
    | ConTag
        expr                    : Expr
        arity                   : {Module.Arity}

-- Let bindings
DATA Binds
    | Rec
        binds                   : Binds'
    | NonRec
        bind                    : Bind
    | Strict
        bind                    : Bind

TYPE Binds'                     = [ Bind ]

DATA Bind
    | Bind
        name                    : {I.Id}
        expr                    : Expr

-- Guard alternatives
TYPE Alts                       = [ Alt ]

DATA Alt
    | Alt
        pat                     : Pat
        expr                    : Expr

DATA Pat
    | ConId
        name                    : {I.Id}
        ids                     : {[I.Id]}
    | ConTag
        tag                     : {Module.Tag}
        arity                   : {Module.Arity}
        ids                     : {[I.Id]}
    | Lit
        lit                     : Literal
    | Default
