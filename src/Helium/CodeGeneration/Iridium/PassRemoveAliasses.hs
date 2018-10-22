{-| Module      :  PassRemoveAliasses
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Iridium.PassRemoveAliasses(passRemoveAliasses) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data

type Env = IdMap (Id, Bool)

passRemoveAliasses :: Module -> Module
passRemoveAliasses = mapBlocks (removeAliasses emptyMap)

lookupId :: Env -> Id -> (Id, Bool)
lookupId env name = case lookupMap name env of
  Nothing -> (name, False)
  Just (x, False) -> lookupId env x
  Just a -> a

mapId :: Env -> Id -> Id
mapId env name = fst $ lookupId env name

mapIds :: Env -> [Id] -> [Id]
mapIds env = map $ mapId env

removeAliasses :: Env -> Instruction -> Instruction
removeAliasses env (Let name expr next) = aliassesInLet env name expr next
removeAliasses env (LetAlloc thunks next) = LetAlloc (map (aliassesInThunk env) thunks) $ removeAliasses env next
removeAliasses env (Jump to args) = Jump to $ mapIds env args
removeAliasses env (Match name con args next) = Match (mapId env name) con args $ removeAliasses env next
removeAliasses env (If name pat whenTrue whenFalse) = If (mapId env name) pat whenTrue whenFalse
removeAliasses env (Return name) = Return $ mapId env name

aliassesInThunk :: Env -> BindThunk -> BindThunk
aliassesInThunk env (BindThunk var fn args) = BindThunk var (mapId env fn) (mapIds env args)

aliassesInLet :: Env -> Id -> Expr -> Instruction -> Instruction
aliassesInLet env name (Var x) next = removeAliasses env' next
  where
    env' = insertMap name (x, False) env
aliassesInLet env name (Eval x) next
  -- If `x` is already evaluated, we don't need to evaluate it again.
  | evaluated =
    let env' = insertMap name (mapped, True) env
    in removeAliasses env' next
  -- `x` might not be evaluated, so we keep the Eval instruction.
  -- Other references to `mapped` must be mapped to `name`.
  | otherwise =
    let env' = updateMap mapped (name, True) $ insertMap name (name, True) env
    in
      Let name (Eval mapped)
      $ removeAliasses env' next
  where
    (mapped, evaluated) = lookupId env x

-- Expressions that don't change the environment.
aliassesInLet env name (Call fn args) next = Let name (Call (mapId env fn) (mapIds env args)) $ removeAliasses env next
aliassesInLet env name (Alloc con args) next = Let name (Alloc con (mapIds env args)) $ removeAliasses env next
aliassesInLet env name expr next = Let name expr $ removeAliasses env next
