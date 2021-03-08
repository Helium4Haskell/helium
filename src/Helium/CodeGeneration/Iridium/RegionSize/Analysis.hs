module Helium.CodeGeneration.Iridium.RegionSize.Analysis
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.List (mapAccumR)
import Data.Maybe (fromJust)
import Data.Either (rights)

-- TODO: Remove
instance Show Quantor where
    show _ = "Quantor"
instance Show Local where
    show (Local id ty) = stringFromId id ++ "::" ++ showType varNames ty
instance Show Type where
    show t = showType varNames t

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

-- TODO: Clean up this mess
-- | Analyse the effect and annotation of a block
analyse :: GlobalEnv -> Id -> Method -> Annotation
analyse gEnv _ method@(Method _ regArgs args _ _ _ block blocks) =
        -- Create inital lEnv with method arguments 
    let argIdxs      = zip args $ map AVar $ reverse [0..(length args-1)]
        initEnv      = foldl (flip $ uncurry insertArgument) emptyMap argIdxs
        -- Retrieve other locals from method body
        localEnv     = foldl (\lEnv -> localsOfBlock (Envs gEnv lEnv)) initEnv (block:blocks) 
        -- Retrieve the annotation and effect of the function body
        (bAnn, bEff) = head.snd $ mapAccumR (blockAccum $ Envs gEnv localEnv) emptyMap (block:blocks)
        -- Generate the method annotation
        (FunctionType argTy resTy) = methodFunctionType method
        argSorts = map argumentSortAssign argTy
        lamCount = length $ rights args   
        resReg   = regionAssign $ typeWeaken lamCount resTy
        fAnn     = case last argSorts of
                      Nothing | length argSorts == 0 -> bAnn
                              | otherwise            -> AQuant bAnn
                      Just s  -> ALam s (ATuple [bAnn, ALam resReg $ annWeaken 1 bEff]) 
        -- Create quantors and lambdas
    in foldr (\s a -> case s of
                        Nothing -> AQuant a
                        Just s' -> ALam s' (ATuple [a, ALam SortUnit botEffect])) fAnn $ init argSorts

----------------------------------------------------------------
-- Gathering local variable annotations
----------------------------------------------------------------

-- | Get the annotation of local variabvles from a block
localsOfBlock :: Envs -> Block -> LocalEnv
localsOfBlock envs (Block _ instr) = localsOfInstr envs instr

-- | Get the annotation of local variabvles from an instruction
localsOfInstr :: Envs -> Instruction -> LocalEnv
localsOfInstr envs@(Envs gEnv lEnv) instr = 
    case instr of
        Let name expr next   -> let (varAnn, _) = analyseExpr envs expr
                                    lEnv'       = insertMap name varAnn lEnv
                                in localsOfInstr (Envs gEnv lEnv') next
        --TODO: Mutrec
        LetAlloc binds next  -> localsOfLetAlloc envs binds next
        Match local target tys ids next -> localsOfMatch envs local target tys ids next
        NewRegion _ _   next -> localsOfInstr envs next
        ReleaseRegion _ next -> localsOfInstr envs next
        -- Other instructions are 'terminal nodes' that do not extend lEnv
        _ -> lEnv

-- TODO: Still lots and lots of duplicated code here between localsOf and analyse
localsOfLetAlloc :: Envs -> [Bind] -> Instruction -> LocalEnv
localsOfLetAlloc envs [] next = localsOfInstr envs next
-- Thunk binds
localsOfLetAlloc envs@(Envs gEnv lEnv) (Bind id (BindTargetThunk var tRegs) args _:bs) next =
    let (bAnn, _) = callApplyArgs lEnv (lookupVar envs var) args $ bindThunkValue tRegs
        lEnv'     = insertMap id bAnn lEnv
    in localsOfLetAlloc (Envs gEnv lEnv') bs next
-- Function binds
localsOfLetAlloc (Envs gEnv lEnv) (Bind id (BindTargetFunction gFun regs _) args _:bs) next = -- TODO: Check if okay
    let gFunAnn   = lookupGlobal gEnv $ globalFunctionName gFun
        (bAnn, _) = callApplyArgs lEnv gFunAnn args regs
        lEnv'     = insertMap id bAnn lEnv
    in localsOfLetAlloc (Envs gEnv lEnv') bs next

-- | Retrieve the local variables from a match instruction
localsOfMatch :: Envs
             -> Local -> MatchTarget -> [Type] -> [Maybe Id] -> Instruction  
             -> LocalEnv
localsOfMatch (Envs gEnv lEnv) local (MatchTargetTuple n) _ ids next =
    let tupleVar = lookupLocal lEnv local
        newVars  = map (flip AProj $ tupleVar) [0..(n-1)]
        -- Insert matched vars into lEnv
        lEnv'    = foldl (flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs gEnv lEnv') next
localsOfMatch _ _ _ _ _ _ = rsError "analyseMatch: No support for data types."

----------------------------------------------------------------
-- Analysing the effect of the function
----------------------------------------------------------------

{-| Put the blockmap in to get the result. 
    Returns the extended bEnv, the annotation of the result and the effect.
-}
blockAccum :: Envs -> BlockEnv -> Block -> (BlockEnv, (Annotation, Effect))
blockAccum envs bEnv (Block name instr) = let bEff  = analyseInstr envs bEnv instr
                                              bEnv' = insertMap name bEff bEnv
                                          in (bEnv', bEff)

-- | Analyse an instruction
analyseInstr :: Envs -> BlockEnv -> Instruction -> (Annotation, Effect)
analyseInstr envs@(Envs _ lEnv) bEnv = go
   where go (Let _ expr      next) =  
           let (_     , varEff) = analyseExpr envs expr
               (nxtAnn, nxtEff) = go next
           in (nxtAnn, AAdd varEff nxtEff)
         -- TODO: Allocations with region variables
         go (LetAlloc bnds   next) = analyseLetAlloc envs bEnv bnds next 
         -- TODO: Remove region from effect
         go (NewRegion _ _   next) = analyseInstr envs bEnv next
         -- TODO: Check if we can ignore a release
         go (ReleaseRegion _ next) = analyseInstr envs bEnv next
         -- Lookup the annotation and effect from block
         go (Jump block)           = lookupBlock bEnv block 
         -- Join the effects of all the blocks
         go (Case _     cas)       = joinBlocks bEnv $ caseBlocks cas
         -- Lookup the variable annotation
         go (Return local)         = (lookupLocal lEnv local, botEffect)
         -- No effect
         go (Unreachable _)        = botAnnEff
         -- Matching only reads, only effect of sub instruction
         go (Match _ _ _ _ next)   = go next

-- | Analyse letalloc (TODO: Abstract some stuff (same impl. in localsOf))
analyseLetAlloc :: Envs -> BlockEnv -> [Bind] -> Instruction ->  (Annotation, Effect)
analyseLetAlloc envs bEnv [] next = analyseInstr envs bEnv next
analyseLetAlloc envs@(Envs gEnv lEnv) bEnv (Bind id (BindTargetThunk var tRegs) args _:bs) next =
    let (bAnn,bEff) = callApplyArgs lEnv (lookupVar envs var) args $ bindThunkValue tRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd rEff bEff)
-- Function binds
analyseLetAlloc envs@(Envs gEnv lEnv) bEnv (Bind id (BindTargetFunction gFun regs _) args _:bs) next = -- TODO: Check if okay
    let gFunAnn = lookupGlobal gEnv $ globalFunctionName gFun
        (bAnn,bEff) = callApplyArgs lEnv gFunAnn args regs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd rEff bEff)


-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr envs@(Envs gEnv lEnv) = go
    where 
      -- Literals have unit annotation, no effect. TODO: doesn't count for strings?
      go (Literal _)              = (AUnit                          , botEffect) 
      -- Eval & Var: Lookup annotation of variable (can be global or local)
      go (Eval var)               = (lookupVar envs var             , botEffect)
      go (Var var)                = (lookupVar envs var             , botEffect)
      -- TODO: Can we ignore the type cast?
      go (Cast local _)           = (lookupLocal lEnv local         , botEffect)
      -- No effect, annotation of local
      go (CastThunk local)        = (lookupLocal lEnv local         , botEffect)
      -- Join of the variable annotations in the branches
      go (Phi branches)           = (joinAnnList $ lookupLocal lEnv <$> map phiVariable branches, botEffect) 
      -- Primitive expression, does not allocate or cause any effect -> bottom
      go (PrimitiveExpr _ _)      = botAnnEff 
      -- No effect, bottom annotation
      go (Undefined _)            = botAnnEff
      -- No effect, just annotation of local2
      go (Seq _ local2)           = (lookupLocal lEnv local2        , botEffect)
      -- Instantiate types in local
      go (Instantiate local tys)  = (foldl AInstn (lEnv `lookupLocal` local) tys, botEffect) 
      -- Apply all type and variable arguments
      go (Call gFun _ args rReg)  = callApplyArgs lEnv (gEnv `lookupGlobal` globalFunctionName gFun) args rReg

----------------------------------------------------------------
-- Function calls
----------------------------------------------------------------

-- | Apply an argument to a function
callApplyArg :: LocalEnv 
             -> Annotation        -- ^ Return region
             -> Annotation        -- ^ Function 
             -> Either Type Local -- ^ Argument
             -> (Annotation, Effect)
-- TODO: Double check: If an AInst is the last argument this might goof up
callApplyArg _    rReg fAnn (Left ty    ) = (AInstn fAnn ty, botEffect) 
callApplyArg lEnv rReg fAnn (Right local) = 
    let (cAnn,cEff) = liftTuple . AApl fAnn $ lookupLocal lEnv local
    in (cAnn, AApl cEff rReg)

-- | Apply a list of arguments to a funtion
callApplyArgs :: LocalEnv -> Annotation -> [Either Type Local] -> RegionVars -> (Annotation, Effect)
callApplyArgs lEnv fAnn args retRegs = 
    let retRegAnn = regionVarsToAnn retRegs
        initArgs  = init args
        (cAnn,cEff) = foldl (\(sAnn,sEff) -> addEffect sEff . callApplyArg lEnv AUnit sAnn) (fAnn,botEffect) initArgs
        lastArg   = last args
        (rAnn,rEff) = callApplyArg lEnv retRegAnn cAnn lastArg
    in (rAnn, AAdd cEff rEff)

-- | Add an effect to an effect tuple
addEffect :: Effect -> (Annotation, Effect) -> (Annotation, Effect)
addEffect eff (a,e) = (a, AAdd eff e)

----------------------------------------------------------------
-- Analysis utilities
----------------------------------------------------------------

-- | Insert an ID if it is present
insertMaybeId :: Maybe Id -> Annotation -> LocalEnv -> LocalEnv
insertMaybeId Nothing  = flip const
insertMaybeId (Just i) = insertMap i

-- | Insert method argument into lEnv, ignore quantors 
insertArgument :: Either Quantor Local -> Annotation -> LocalEnv -> LocalEnv
insertArgument (Left _)      = flip const
insertArgument (Right local) = insertMap $ localName local


-- | Assign sort to types, return Nothing for a quantor
argumentSortAssign :: Either Quantor Type -> Maybe Sort
argumentSortAssign (Left _)   = Nothing
argumentSortAssign (Right ty) = Just $ sortAssign ty

-- | Get the case block names out of the case
caseBlocks :: Case -> [BlockName]
caseBlocks (CaseConstructor cases) = map snd cases
caseBlocks (CaseInt cases dflt)    = dflt : map snd cases

-- | Phi expression vars
phiVarAnn :: LocalEnv -> [PhiBranch] -> [Annotation]
phiVarAnn lEnv branches = lookupLocal lEnv <$> phiVariable <$> branches


-- | Convert an annotation tuple to a haskell tuple
liftTuple :: Annotation -> (Annotation, Effect)
liftTuple a = (AProj 0 a, AProj 1 a) 


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

