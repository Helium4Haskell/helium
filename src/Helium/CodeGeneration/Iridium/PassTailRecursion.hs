-- Rewrites tail recusion to loops

module Helium.CodeGeneration.Iridium.PassTailRecursion (passTailRecursion) where

import Data.Maybe (mapMaybe)
import Data.Either (lefts)

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Utils
import Helium.Lvm.Common.Id (Id, NameSupply, freshId, freshIdFromId, mapWithSupply, splitNameSupply)
import Helium.Lvm.Core.Type

passTailRecursion :: NameSupply -> Module -> Module
passTailRecursion = mapMethodsWithSupply transformMethod

data TailRecursion = TailRecursion !BlockName ![Either Type Variable]

data Context = Context !Id ![Either Quantor Local] !BlockName

findTailRecursion :: Context -> Instruction -> Maybe TailRecursion
findTailRecursion (Context fnName params blockName) (Let var (Call (GlobalFunction fn _ _) args) (Return (VarLocal (Local ret _))))
  | fnName == fn && var == ret && typeArgumentsPreserved (length (lefts params) - 1) params args = Just $ TailRecursion blockName args
findTailRecursion context (Let _ _ next) = findTailRecursion context next
findTailRecursion context (LetAlloc _ next) = findTailRecursion context next
findTailRecursion context (Match _ _ _ _ next) = findTailRecursion context next
findTailRecursion _ _ = Nothing

-- Checks whether no type arguments have changed.
-- We currently only allow tail recursion when type argument instantiation does
-- not change, as we do not have phi nodes on type arguments, and it is
-- probably not a good idea to introduce those.
-- The first argument in the TypeVar (as a Debruijn index) of the left-most type variable.
typeArgumentsPreserved :: Int -> [Either Quantor Local] -> [Either Type Variable] -> Bool
typeArgumentsPreserved _ [] [] = True
typeArgumentsPreserved firstTypeVar (Left _ : params) (Left tp : args) = tp == TVar firstTypeVar && typeArgumentsPreserved (firstTypeVar - 1) params args
typeArgumentsPreserved firstTypeVar (Right _ : params) (Right _ : args) = typeArgumentsPreserved firstTypeVar params args
typeArgumentsPreserved _ _ _ = False
  
transformMethod :: NameSupply -> Declaration Method -> Declaration Method
transformMethod supply decl@(Declaration name vis mod customs (Method tp params retType annotations b@(Block entryName entryInstr) bs))
  | null tails = decl -- No tail recursion
  | otherwise = Declaration name vis mod customs $ Method tp params' retType annotations entry $ b' : bs'
  where
    blocks :: [(Block, Maybe TailRecursion)]
    blocks = map (\b@(Block blockName instr) -> (b, findTailRecursion (Context name params blockName) instr)) $ b : bs
    tails = mapMaybe snd blocks
    (entryName', supply') = freshId supply
    entry = Block entryName' (Jump entryName)
    Block _ entryInstr' : bs' = map (transformBlock entryName) blocks
    b' = Block entryName $ phis entryInstr'

    -- The phi nodes
    phis :: Instruction -> Instruction
    phis = createPhis entryName' params params' tails

    -- The renamed arguments
    params' :: [Either Quantor Local]
    params' = mapWithSupply renameParam supply' params
    renameParam s (Right (Local argName t)) = Right $ Local (fst $ freshIdFromId argName s) t
    renameParam _ (Left q) = Left q

createPhis :: BlockName -> [Either Quantor Local] -> [Either Quantor Local] -> [TailRecursion] -> Instruction -> Instruction
createPhis entryName [] [] tails = id
createPhis entryName (Left _ : args) (Left _ : args') tails = createPhis entryName args args' $ map tailRecursionDrop tails
createPhis entryName (Right (Local arg t) : args) (Right (Local arg' _) : args') tails = phi . createPhis entryName args args' tails'
  where
    phi = Let arg $ Phi $ PhiBranch entryName (VarLocal $ Local arg' t) : tailBranches
    tailBranches = map (\(TailRecursion block (Right v:_)) -> PhiBranch block v) tails

    -- Remove first argument from tails, for recursive call
    tails' = map tailRecursionDrop tails

-- Remove first argument from tails
tailRecursionDrop :: TailRecursion -> TailRecursion
tailRecursionDrop (TailRecursion block (_:vs)) = TailRecursion block vs

transformBlock :: Id -> (Block, Maybe TailRecursion) -> Block
transformBlock _ (b, Nothing) = b
transformBlock entryName (Block name instr, Just _) = Block name $ transformInstruction entryName instr

-- Transforms an instruction, in a block which does tail recursion
transformInstruction :: Id -> Instruction -> Instruction
transformInstruction entryName (Let _ (Call _ _) (Return _)) = Jump entryName
transformInstruction entryName (Let var expr next) = Let var expr $ transformInstruction entryName next
transformInstruction entryName (LetAlloc binds next) = LetAlloc binds $ transformInstruction entryName next
transformInstruction entryName (Match var target instantiation fields next) = Match var target instantiation fields $ transformInstruction entryName next
transformInstruction entryName _ = error "PassTailRecursion: Expected block to be tail recursive"
