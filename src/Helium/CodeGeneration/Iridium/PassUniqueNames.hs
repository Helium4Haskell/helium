{-| Module      :  PassUniqueNames
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- After the conversion from Core to Iridium, a variable name might be used in multiple blocks of the same function.
-- We rename the arguments of all blocks except the entry block, to make sure all variables are unique.
-- Note that we do not need to change the arugments of the entry block, as we rename all other blocks.
-- We also do not need to rename the variables introduced in let-bindings, as they are unique.

module Helium.CodeGeneration.Iridium.PassUniqueNames where

import Lvm.Common.Id(Id, NameSupply, freshIdFromId, splitNameSupply, mapWithSupply, idFromString)
import Lvm.Common.IdMap
import Data.Maybe(fromMaybe)

import Helium.CodeGeneration.Iridium.Data

type Env = IdMap Id

passUniqueNames :: NameSupply -> Module -> Module
passUniqueNames supply (Module name datas methods) = Module name datas $ mapWithSupply renameMethod supply methods

renameMethod :: NameSupply -> Method -> Method
renameMethod supply (Method name rettype entry blocks) = Method name rettype entry $ mapWithSupply renameInBlock supply blocks

renameId :: Env -> Id -> Id
renameId env name = fromMaybe name $ lookupMap name env

renameIds :: Env -> [Id] -> [Id]
renameIds env = map (renameId env)

renameArguments :: Env -> [Argument] -> [Argument]
renameArguments env = map (\(Argument name a) -> Argument (renameId env name) a)

renameInBlock :: NameSupply -> Block -> Block
renameInBlock supply (Block name args instr) = Block name (renameArguments env args) (renameInInstruction env instr)
  where
    env = mapFromList $ mapWithSupply (\s (Argument name _) -> (name, fst $ freshIdFromId name s)) supply args

renameInInstruction :: Env -> Instruction -> Instruction
renameInInstruction env (Let name expr next) = Let name (renameInExpr env expr) $ renameInInstruction env next
renameInInstruction env (LetAlloc thunks next) = LetAlloc (map (renameInBindThunk env) thunks) $ renameInInstruction env next
renameInInstruction env (Jump to args) = Jump to $ renameIds env args
renameInInstruction env (Match var pat next) = Match (renameId env var) pat $ renameInInstruction env next
renameInInstruction env (IfMatch var pat to args next) = IfMatch (renameId env var) pat to (renameIds env args) $ renameInInstruction env next
renameInInstruction env (Return var) = Return $ renameId env var

renameInExpr :: Env -> Expr -> Expr
renameInExpr env l@(Literal _) = l
renameInExpr env (Call fn args) = Call (renameId env fn) (renameIds env args)
renameInExpr env (Eval x) = Eval (renameId env x)
renameInExpr env (Alloc con args) = Alloc con $ renameIds env args
renameInExpr env (Var var) = Var $ renameId env var

renameInBindThunk :: Env -> BindThunk -> BindThunk
renameInBindThunk env (BindThunk var fn args) = BindThunk var (renameId env fn) (renameIds env args)
