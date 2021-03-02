module Helium.CodeGeneration.Iridium.RegionSize.Analysis
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.BindingGroup

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

data InstrAlg a = InstrAlg {
    iLet         :: Id -> Expr -> a -> a,
    iLetAlloc    :: [Bind] -> a -> a,
    iJump        :: BlockName -> a,
    iCase        :: Local -> Case -> a,
    iReturn      :: Local -> a,
    iUnreachable :: Maybe Local -> a,
    iMatch       :: Local -> MatchTarget -> [Type] -> [Maybe Id] -> a -> a
}

idInstrAlg :: InstrAlg Instruction
idInstrAlg = InstrAlg {
    iLet         = Let,
    iLetAlloc    = LetAlloc,
    iJump        = Jump,
    iCase        = Case,
    iReturn      = Return,
    iUnreachable = Unreachable,
    iMatch       = Match
}

dfltInstrAlg :: a -> InstrAlg a
dfltInstrAlg a = InstrAlg {
    -- Pass through default
    iLet         = \_ _ b     -> b,
    iLetAlloc    = \_ b       -> b,
    iMatch       = \_ _ _ _ b -> b,
    -- Return default
    iJump        = \_         -> a,
    iCase        = \_ _       -> a,
    iReturn      = \_         -> a,
    iUnreachable = \_         -> a
}

foldInstrAlg :: InstrAlg a -> Instruction -> a 
foldInstrAlg alg = go
    where go (Let         name expr next      ) = iLet         alg name expr       $ go next              
          go (LetAlloc    binds next          ) = iLetAlloc    alg binds           $ go next      
          go (Match       lcl tgt tys fds next) = iMatch       alg lcl tgt tys fds $ go next                   
          go (Jump        blockName           ) = iJump        alg blockName           
          go (Case        local cas           ) = iCase        alg local cas           
          go (Return      local               ) = iReturn      alg local       
          go (Unreachable local               ) = iUnreachable alg local

----------------------------------------------------------------
-- Analysis
----------------------------------------------------------------

analyse :: GlobalEnv -> Id -> Method -> (Annotation, Effect)
analyse gEnv methodId (Method _ _ _ _ init blocks) =
    let (lEnv, fs)  = mapAccumL (\lEnv -> analyseBlock (Envs gEnv lEnv)) emptyMap (init:blocks)
        (bEnv, res) = mapAccumR blockFold emptyMap $ zip fs (init:blocks)
    in head res

-- | Put the blockmap in to get the result
blockFold :: BlockEnv -> (BlockEnv -> (Annotation, Effect), Block) -> (BlockEnv, (Annotation, Effect))
blockFold bEnv (f, block) = let res   = f bEnv
                                bEnv' = insertMap (blockName block) res bEnv
                   in (bEnv', res)

-- | Get the annotation of local variabvles from a block
analyseBlock :: Envs -> Block -> (LocalEnv, BlockEnv -> (Annotation, Effect))
analyseBlock envs (Block name instr) = analyseInstr envs instr

{- Get the annotation of local variabvles from an instruction
   The second half of the tuple is a computation that, given the effect of the i+1..n blocks
   can compute the effect of the i-th block.
-}
analyseInstr :: Envs -> Instruction -> (LocalEnv, BlockEnv -> (Annotation, Effect))
analyseInstr envs@(Envs gEnv lEnv) = go   
    where go (Let name expr nextInstr) =  
            let (varAnn, varEff) = analyseExpr  envs expr
                lEnv'            = insertMap name varAnn lEnv
                (lEnvR, cont)    = analyseInstr (Envs gEnv lEnv') nextInstr
            in (lEnvR, \bEnv -> let (nxtAnn, nxtEff) = cont bEnv in (nxtAnn, AAdd varEff nxtEff))
          -- TODO: Allocations with region variables
          go (LetAlloc binds next) = (emptyMap, \bEnv -> botAnnEff) 
          -- Lookup the annotation and effect from block
          go (Jump blockName)      = (emptyMap, \bEnv -> lookupBlock bEnv blockName) 
          -- Join the effects of all the blocks
          go (Case local cas)      = (emptyMap, \bEnv -> joinBlocks bEnv $ caseBlocks cas)
          -- Lookup the variable annotation
          go (Return local)        = (emptyMap, \bEnv -> (lookupLocal lEnv local, botEffect))
          -- No effect
          go (Unreachable local)   = (emptyMap, \bEnv -> botAnnEff)
          -- TODO: Figure out what to do with this (Probs some expansion of lEnv)
          go (Match local target types fields next) = analyseInstr envs next

-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr envs@(Envs gEnv lEnv) = go
    where 
      -- Literals have unit annotation, no effect. TODO: doesn't count for strings?
      go (Literal lit)            = (AUnit, botEffect) 
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