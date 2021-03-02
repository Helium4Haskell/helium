module Helium.CodeGeneration.Iridium.RegionSize.Analysis
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.List

----------------------------------------------------------------
-- Assumptions
----------------------------------------------------------------
-- Jumps never jump backward (in the order of blocks)

-- The idea now:
-- Build local env by mapAccumL on (init:blocks)
-- Get final effects by building the block env from the last block to the first

----------------------------------------------------------------
-- Analysis
----------------------------------------------------------------

analyse :: GlobalEnv -> Id -> Method -> (Annotation, Effect)
analyse gEnv _ (Method _ _ _ _ block blocks) =
    let localEnv   = foldl (\lEnv -> unionMap lEnv . localsOfBlock (Envs gEnv lEnv)) emptyMap (block:blocks)
        (_, bEffs) = mapAccumR (blockAccum (Envs gEnv localEnv)) emptyMap (block:blocks)
    in head bEffs



-- | Get the annotation of local variabvles from a block
localsOfBlock :: Envs -> Block -> LocalEnv
localsOfBlock envs (Block _ instr) = localsOfInstr envs instr

-- | Get the annotation of local variabvles from an instruction
localsOfInstr :: Envs -> Instruction -> LocalEnv
localsOfInstr envs@(Envs gEnv lEnv) = go
    where go (Let name expr next)    = let (varAnn, _) = analyseExpr envs expr
                                           lEnv'       = insertMap name varAnn lEnv
                                       in localsOfInstr (Envs gEnv lEnv') next
          go (LetAlloc _ next)       = go next
          go (Match    _ _ _ _ next) = go next
          go _ = emptyMap



-- | Put the blockmap in to get the result
blockAccum :: Envs -> BlockEnv -> Block -> (BlockEnv, (Annotation, Effect))
blockAccum envs bEnv (Block name instr) = let bEff  = analyseInstr envs bEnv instr
                                              bEnv' = insertMap name bEff bEnv
                                          in (bEnv', bEff)

-- | Block effect
analyseInstr :: Envs -> BlockEnv -> Instruction -> (Annotation, Effect)
analyseInstr envs@(Envs _ lEnv) bEnv = go
   where go (Let _ expr next)     =  
           let (_     , varEff) = analyseExpr envs expr
               (nxtAnn, nxtEff) = go next
           in (nxtAnn, AAdd varEff nxtEff)
         -- TODO: Allocations with region variables
         go (LetAlloc _    next)  = go next 
         -- Lookup the annotation and effect from block
         go (Jump block)          = lookupBlock bEnv block 
         -- Join the effects of all the blocks
         go (Case _     cas)      = joinBlocks bEnv $ caseBlocks cas
         -- Lookup the variable annotation
         go (Return local)        = (lookupLocal lEnv local, botEffect)
         -- No effect
         go (Unreachable _)       = botAnnEff
         -- TODO: Figure out what to do with this (Probs some expansion of lEnv)
         go (Match _ _ _ _ next)  = go next

-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr (Envs gEnv lEnv) = go
    where 
      -- Literals have unit annotation, no effect. TODO: doesn't count for strings?
      go (Literal _)              = (AUnit, botEffect) 
      -- Eval & Var: Lookup annotation of variable (can be global or local)
      go (Eval var)               = (lookupVar gEnv lEnv var, botEffect)
      go (Var var)                = (lookupVar gEnv lEnv var, botEffect)
      -- TODO: Can we ignore the type cast?
      go (Cast local _)           = (lookupLocal lEnv local, botEffect)
      -- No effect, annotation of local
      go (CastThunk local)        = (lookupLocal lEnv local, botEffect)
      -- Join of the variable annotations in the branches
      go (Phi branches)           = (joinAnnList $ lookupLocal lEnv <$> map phiVariable branches, botEffect) 
      -- Primitive expression, does not allocate or cause any effect -> bottom
      go (PrimitiveExpr _ _)      = botAnnEff 
      -- No effect, bottom annotation
      go (Undefined _)            = botAnnEff
      -- No effect, just annotation of local2
      go (Seq _ local2)           = (lookupLocal lEnv local2, botEffect)
      -- Instantiate types in local
      go (Instantiate local tys)  = (foldl AInstn (lEnv `lookupLocal` local) tys, botEffect) 
      -- Apply all type and variable arguments
      go (Call gFun tyLos)        = -- TODO, fEff = P -> C
          let gFunAnn = gEnv `lookupGlobal` globalFunctionName gFun
              resAnn  = foldl (callApplyArg lEnv) gFunAnn tyLos
          in (resAnn, botEffect)

----------------------------------------------------------------
-- Analysis utilities
----------------------------------------------------------------

-- | Get the case block names out of the case
caseBlocks :: Case -> [BlockName]
caseBlocks (CaseConstructor cases) = map snd cases
caseBlocks (CaseInt cases dflt)    = dflt : map snd cases

-- | Phi expression vars
phiVarAnn :: LocalEnv -> [PhiBranch] -> [Annotation]
phiVarAnn lEnv branches = lookupLocal lEnv <$> phiVariable <$> branches

-- | Apply an argument to a function
callApplyArg :: LocalEnv -> Annotation -> Either Type Local -> Annotation
callApplyArg _    fAnn (Left ty    ) = AInstn fAnn ty 
callApplyArg lEnv fAnn (Right local) = AApl   fAnn $ lookupLocal lEnv local

-- | Join of blocks
joinBlocks :: BlockEnv -> [BlockName] -> (Annotation, Effect)
joinBlocks bEnv blockNames = foldr joinTuples botAnnEff blocks
    where blocks = lookupBlock bEnv <$> blockNames 

-- | The join of two tuples
joinTuples :: (Annotation, Effect) -> (Annotation, Effect) -> (Annotation, Effect)
joinTuples (a,b) (c,d) = (AJoin a c, AJoin b d)

-- | Join a list of annotations
joinAnnList :: [Annotation] -> Annotation
joinAnnList []     = rsError "joinAnnList: Empty annotation list"
joinAnnList [x]    = x
joinAnnList (x:xs) = foldl AJoin x xs

-- | The bottom for annotation & effect (annotation bot, constr bot)
botAnnEff :: (Annotation, Effect)
botAnnEff = (ABot, botEffect)

-- | Bottom for the effect
botEffect :: Effect
botEffect = AConstr constrBot

-- | Get the name of a block
blockName :: Block -> BlockName
blockName (Block name _) = name