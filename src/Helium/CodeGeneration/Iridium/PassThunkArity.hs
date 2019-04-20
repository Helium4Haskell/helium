-- Assures that primary thunks (which point to function pointers) are not overstaturated
-- and that secondary thunks (which point to other thunks) have exactly one argument.

module Helium.CodeGeneration.Iridium.PassThunkArity (passThunkArity) where

import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Utils
import Lvm.Common.Id (Id, NameSupply, freshIdFromId, mapWithSupply, splitNameSupply)
import Data.Either

passThunkArity :: NameSupply -> Module -> Module
passThunkArity supply mod = mapBlocksWithSupply (handleInstruction $ envWithSynonyms mod) supply mod

handleInstruction :: TypeEnvironment -> NameSupply -> Instruction -> Instruction
handleInstruction env supply (Let name expr next) = Let name expr $ handleInstruction env supply next
handleInstruction env supply (LetAlloc binds next) = LetAlloc (concat $ mapWithSupply (handleBind env) supply1 binds) $ handleInstruction env supply2 next
  where
  (supply1, supply2) = splitNameSupply supply
handleInstruction env supply (Match var target instantiation fields next) = Match var target instantiation fields $ handleInstruction env supply next
handleInstruction _ _ instr = instr -- Jump, Case, Return and Unreachable

handleBind :: TypeEnvironment -> NameSupply -> Bind -> [Bind]
handleBind env supply b@(Bind var target@(BindTargetFunction global@(VarGlobal (GlobalVariable _ _))) params)
  | null (filter isRight params) = error "passThunkArity: Cannot bind zero arguments to a global function"
  | otherwise = handleBind env supply bindThunk
  where
    bindThunk = Bind var (BindTargetThunk global) params
handleBind env supply (Bind var target@(BindTargetFunction (VarGlobal (GlobalFunction _ arity fnType))) params)
  | length (filter isRight params) > arity = bindFn : bindThunks
  -- Too many arguments are passed, the thunk is oversaturated.
  where
  -- Saturate the call to `target`
  (bindFnArgs, remaining) = paramsTakeValues arity params
  bindFn = Bind varTemp target bindFnArgs
  bindFnType = bindType env bindFn
  -- Put the remaining arguments in a secondary thunk
  bindThunk = Bind var (BindTargetThunk $ VarLocal $ Local varTemp bindFnType) remaining
  -- If there were multiple remaining arguments for the secondary thunk, we must split that thunk further,
  -- as a secondary thunk should have exactly one argument
  bindThunks = handleBind env supply' bindThunk
  (varTemp, supply') = freshIdFromId var supply
handleBind _ _ b = [b]
