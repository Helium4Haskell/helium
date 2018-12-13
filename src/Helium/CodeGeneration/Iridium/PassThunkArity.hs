-- Assures that primary thunks (which point to function pointers) are not overstaturated
-- and that secondary thunks (which point to other thunks) have exactly one argument.

-- TODO: If a global without arguments is the target of a thunk, we need to add a cast from global to local here,
-- as a bind with zero arguments will cause that the global is not shared.

module Helium.CodeGeneration.Iridium.PassThunkArity (passThunkArity) where

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Utils
import Lvm.Common.Id (Id, NameSupply, freshIdFromId, mapWithSupply, splitNameSupply)

passThunkArity :: NameSupply -> Module -> Module
passThunkArity = mapBlocksWithSupply handleInstruction

handleInstruction :: NameSupply -> Instruction -> Instruction
handleInstruction supply (Let name expr next) = Let name expr $ handleInstruction supply next
handleInstruction supply (LetAlloc binds next) = LetAlloc (concat $ mapWithSupply handleBind supply1 binds) $ handleInstruction supply2 next
  where
  (supply1, supply2) = splitNameSupply supply
handleInstruction supply (Match var target fields next) = Match var target fields $ handleInstruction supply next
handleInstruction _ instr = instr -- Jump, Case, Return and Unreachable

handleBind :: NameSupply -> Bind -> [Bind]
handleBind supply b@(Bind var target@(BindTargetFunction global@(VarGlobal (GlobalVariable _ _))) params)
  | null params = error "passThunkArity: Cannot bind zero arguments to a global function"
  | otherwise = handleBind supply bindThunk
  where
    bindThunk = Bind var (BindTargetThunk global) params
handleBind supply (Bind var target@(BindTargetFunction (VarGlobal (GlobalFunction _ (FunctionType args returnType)))) params)
  | length params > arity = bindFn : bindThunks
  -- Too many arguments are passed, the thunk is oversaturated.
  where
  -- Saturate the call to `target`
  bindFn = Bind varTemp target (take arity params)
  -- Put the remaining arguments in a secondary thunk
  bindThunk = Bind var (BindTargetThunk $ VarLocal $ Local varTemp returnType) (drop arity params)
  -- If there were multiple remaining arguments for the secondary thunk, we must split that thunk further,
  -- as a secondary thunk should have exactly one argument
  bindThunks = handleBind supply' bindThunk
  (varTemp, supply') = freshIdFromId var supply
  arity = length args
handleBind supply (Bind var target@(BindTargetThunk _) params)
  | length params == 0 = error "Secondary thunk must have at least 1 argument"
  | length params > 1 = -- A secondary thunk should have exactly one argument.
  zipWith3 Bind names targets $ map return params
  where
  tempVars :: [Id]
  tempVars = mapWithSupply (\s _ -> fst $ freshIdFromId var s) supply [0 .. length params - 2]
  names = tempVars ++ [var]
  targets = target : map (BindTargetThunk . VarLocal . (`Local` TypeAnyThunk)) tempVars
handleBind _ b = [b]
