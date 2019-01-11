-- Rewrites tail recusion to loops

module Helium.CodeGeneration.Iridium.PassTailRecursion (passTailRecursion) where

import Data.Maybe (mapMaybe)

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Utils
import Lvm.Common.Id (Id, NameSupply, freshId, freshIdFromId, mapWithSupply, splitNameSupply)

passTailRecursion :: NameSupply -> Module -> Module
passTailRecursion = mapMethodsWithSupply transformMethod

data TailRecursion = TailRecursion !BlockName ![Variable]

data Context = Context !Id !BlockName

findTailRecursion :: Context -> Instruction -> Maybe TailRecursion
findTailRecursion (Context fnName blockName) (Let var (Call (GlobalFunction fn _) args) (Return (VarLocal (Local ret _))))
  | fnName == fn && var == ret = Just $ TailRecursion blockName args
findTailRecursion context (Let _ _ next) = findTailRecursion context next
findTailRecursion context (LetAlloc _ next) = findTailRecursion context next
findTailRecursion context (Match _ _ _ next) = findTailRecursion context next
findTailRecursion _ _ = Nothing

transformMethod :: NameSupply -> Declaration Method -> Declaration Method
transformMethod supply decl@(Declaration name vis mod customs (Method params retType annotations b@(Block entryName entryInstr) bs))
  | null tails = decl -- No tail recursion
  | otherwise = Declaration name vis mod customs $ Method params' retType annotations entry $ b' : bs'
  where
    blocks :: [(Block, Maybe TailRecursion)]
    blocks = map (\b@(Block blockName instr) -> (b, findTailRecursion (Context name blockName) instr)) $ b : bs
    tails = mapMaybe snd blocks
    (entryName', supply') = freshId supply
    entry = Block entryName' (Jump entryName)
    Block _ entryInstr' : bs' = map (transformBlock entryName) blocks
    b' = Block entryName $ phis entryInstr'

    -- The phi nodes
    phis :: Instruction -> Instruction
    phis = createPhis entryName' params params' tails

    -- The renamed arguments
    params' :: [Local]
    params' = mapWithSupply (\s (Local argName t) -> Local (fst $ freshIdFromId argName s) t) supply' params

createPhis :: BlockName -> [Local] -> [Local] -> [TailRecursion] -> Instruction -> Instruction
createPhis entryName [] [] tails = id
createPhis entryName (Local arg t : args) (Local arg' _ : args') tails = phi . createPhis entryName args args' tails'
  where
    phi = Let arg $ Phi $ PhiBranch entryName (VarLocal $ Local arg' t) : tailBranches
    tailBranches = map (\(TailRecursion block (v:_)) -> PhiBranch block v) tails

    -- Remove first argument from tails, for recursive call
    tails' = map (\(TailRecursion block (_:vs)) -> TailRecursion block vs) tails

transformBlock :: Id -> (Block, Maybe TailRecursion) -> Block
transformBlock _ (b, Nothing) = b
transformBlock entryName (Block name instr, Just _) = Block name $ transformInstruction entryName instr

-- Transforms an instruction, in a block which does tail recursion
transformInstruction :: Id -> Instruction -> Instruction
transformInstruction entryName (Let _ (Call _ _) (Return _)) = Jump entryName
transformInstruction entryName (Let var expr next) = Let var expr $ transformInstruction entryName next
transformInstruction entryName (LetAlloc binds next) = LetAlloc binds $ transformInstruction entryName next
transformInstruction entryName (Match var target fields next) = Match var target fields $ transformInstruction entryName next
transformInstruction entryName _ = error "PassTailRecursion: Expected block to be tail recursive"
