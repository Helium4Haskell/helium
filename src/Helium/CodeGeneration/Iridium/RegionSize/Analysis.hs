module Helium.CodeGeneration.Iridium.RegionSize.Analysis
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.List (mapAccumR)
import Data.Maybe (fromJust)
import Data.Either (rights)
import qualified Data.Map as M

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

-- Step 2: Implement the additional variables (as regular arguments)
-- Step 3: Return variable should follow logically

-- | Analyse the effect and annotation of a block
analyse :: GlobalEnv -> Id -> Method -> Annotation
analyse gEnv _ method@(Method _ aRegs args _ rRegs _ block blocks) =
    let initEnv      = initEnvFromArgs args
        rEnv         = regEnvFromArgs (length args) aRegs rRegs
        -- Retrieve locals from method body
        localEnv     = foldl (\lEnv -> localsOfBlock (Envs gEnv rEnv lEnv)) initEnv (block:blocks) 
        -- Retrieve the annotation and effect of the function body
        (bAnn, bEff) = head.snd $ mapAccumR (blockAccum $ Envs gEnv rEnv localEnv) emptyMap (block:blocks)
        -- Generate the method annotation
        (regS, argS, rtnS) = argumentSorts method
        bAnn' = wrapBody (last argS) (bAnn, bEff) rtnS
        fAnn  = if argS == [] -- TODO: Also check retArg
                then bAnn     -- IDEA: Now 'SortUnit' but could be a way to deal with thunk allocations
                else foldr (\s a -> wrapBody s (a,botEffect) SortUnit) bAnn' $ init argS
    in ALam regS $ annWeaken 1 fAnn 

-- | Wrap a function body into a AQuant or `A -> (A, P -> C)'
wrapBody :: Maybe Sort -> (Annotation,Effect) -> Sort -> Effect
wrapBody mS (bAnn,bEff) rrSort = case mS of
                      Nothing -> AQuant bAnn
                      Just s  -> ALam s (ATuple [bAnn, ALam rrSort $ annWeaken 1 bEff])

{- Compute the sort of all method arguments,
    Returns a tuple of:
    0: Additional regions  
    1: Sort of regular argument (`Nothing' if quantifier)  
    2: Sort of return region
-}
argumentSorts :: Method -> (Sort, [Maybe Sort], Sort)
argumentSorts method@(Method _ regArgs args resTy _ _ _ _) = 
    let (FunctionType argTy resTy) = methodFunctionType method
        argSorts = map argumentSortAssign argTy
        aRegSort = sort $ regionVarsToAnn M.empty regArgs
        rrSort   = regionAssign $ typeWeaken (length $ rights args) resTy
    in (aRegSort, argSorts, rrSort)

-- | Assign sort to types, return Nothing for a quantor
argumentSortAssign :: Either Quantor Type -> Maybe Sort
argumentSortAssign (Left _)   = Nothing
argumentSortAssign (Right ty) = Just $ sortAssign ty

-- | Initial enviromentment based on function arguments
initEnvFromArgs :: [Either Quantor Local] -> LocalEnv
initEnvFromArgs args = let argIdxs = zip args $ map AVar $ reverse [0..(length args-1)]
                       in foldl (flip $ uncurry insertArgument) emptyMap argIdxs

-- | Region environment from additional regions and return regions
regEnvFromArgs :: Int -> RegionVars -> RegionVars -> RegionEnv
regEnvFromArgs n aRegs rRegs = M.union (go (AnnVar n) aRegs) (go (AnnVar $ 999) rRegs)
    where go var (RegionVarsSingle r) = M.singleton r var
          go var (RegionVarsTuple rs) = M.unions.map (\(i,r) -> go (CnProj i var) r) $ zip [0..] rs

----------------------------------------------------------------
-- Gathering local variable annotations
----------------------------------------------------------------

-- | Get the annotation of local variabvles from a block
localsOfBlock :: Envs -> Block -> LocalEnv
localsOfBlock envs (Block _ instr) = localsOfInstr envs instr

-- | Get the annotation of local variabvles from an instruction
localsOfInstr :: Envs -> Instruction -> LocalEnv
localsOfInstr envs@(Envs gEnv rEnv lEnv) instr = 
    case instr of
        Let name expr next   -> let (varAnn, _) = analyseExpr envs expr
                                    lEnv'       = insertMap name varAnn lEnv
                                in localsOfInstr (Envs gEnv rEnv lEnv') next
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
localsOfLetAlloc envs@(Envs gEnv rEnv lEnv) (Bind id (BindTargetThunk var tRegs) args _:bs) next =
    let (bAnn, _) = thunkApplyArgs envs (lookupVar envs var) args $ bindThunkValue tRegs
        lEnv'     = insertMap id bAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next
-- Function binds
localsOfLetAlloc envs@(Envs gEnv rEnv lEnv) (Bind id (BindTargetFunction gFun aRegs tRegs) args _:bs) next = -- TODO: Check if okay
    let gFunAnn   = lookupGlobal gEnv $ globalFunctionName gFun
        (bAnn, _) = funcApplyArgs envs gFunAnn aRegs args $ bindThunkValue tRegs
        lEnv'     = insertMap id bAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next
-- TODO: Implement others
localsOfLetAlloc envs (_:bs) next = localsOfLetAlloc envs bs next


-- | Retrieve the local variables from a match instruction
localsOfMatch :: Envs
             -> Local -> MatchTarget -> [Type] -> [Maybe Id] -> Instruction  
             -> LocalEnv
localsOfMatch (Envs gEnv rEnv lEnv) local (MatchTargetTuple n) _ ids next =
    let tupleVar = lookupLocal lEnv local
        newVars  = map (flip AProj $ tupleVar) [0..(n-1)]
        -- Insert matched vars into lEnv
        lEnv'    = foldl (flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs gEnv rEnv lEnv') next
-- TODO: Implement others
localsOfMatch (Envs gEnv rEnv lEnv) _ _ _ _ _ = (lEnv)--rsError "analyseMatch: No support for data types."

----------------------------------------------------------------
-- Analysing the effect of a method
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
analyseInstr envs@(Envs _ _ lEnv) bEnv = go
   where go (Let _ expr      next) =  
           let (_     , varEff) = analyseExpr envs expr
               (nxtAnn, nxtEff) = go next
           in (nxtAnn, AAdd varEff nxtEff)
         -- TODO: Allocations with region variables
         go (LetAlloc bnds   next) = analyseLetAlloc envs bEnv bnds next 
         -- Remove region from effect, size has been detrimined
         -- TODO: Lookup & store size somewhere
         go (NewRegion r _   next) = 
             let (nxtAnn, nxtEff) = analyseInstr envs bEnv next
             in  (nxtAnn, AMinus nxtEff r)
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
analyseLetAlloc envs@(Envs gEnv rEnv lEnv) bEnv (Bind id (BindTargetThunk var tRegs) args dReg:bs) next =
    let (bAnn,bEff) = thunkApplyArgs envs (lookupVar envs var) args $ bindThunkValue tRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg rEnv dReg) (AAdd rEff bEff))
-- Function binds
analyseLetAlloc envs@(Envs gEnv rEnv lEnv) bEnv (Bind id (BindTargetFunction gFun aRegs tRegs) args dReg:bs) next = -- TODO: Check if okay
    let retRegs = bindThunkValue tRegs -- TODO: bindThunkIntermediate?
        gFunAnn = lookupGlobal gEnv $ globalFunctionName gFun
        (bAnn,bEff) = funcApplyArgs envs gFunAnn aRegs args retRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg rEnv dReg) (AAdd rEff bEff))
-- TODO: Implement others
analyseLetAlloc _ _ _ _ = (ATop,ATop)

-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr envs@(Envs gEnv _ lEnv) = go
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
      go (Call gFun aRegs args rReg) = funcApplyArgs envs (gEnv `lookupGlobal` globalFunctionName gFun) aRegs args rReg

----------------------------------------------------------------
-- Function calls
----------------------------------------------------------------

-- | Apply an argument to a function
thunkApplyArg :: LocalEnv 
              -> Annotation        -- ^ Return region
              -> Annotation        -- ^ Function 
              -> Either Type Local -- ^ Argument
              -> (Annotation, Effect)
-- TODO: Double check: If an AInst is the last argument this might goof up
thunkApplyArg _    rReg fAnn (Left ty    ) = (AInstn fAnn ty, botEffect) 
thunkApplyArg lEnv rReg fAnn (Right local) = 
    let (cAnn,cEff) = liftTuple . AApl fAnn $ lookupLocal lEnv local
    in (cAnn, AApl cEff rReg)

-- | Apply a list of arguments to a funtion
thunkApplyArgs :: Envs 
               -> Annotation -> [Either Type Local] -> RegionVars 
               -> (Annotation, Effect)
thunkApplyArgs _    fAnn []   _       = (fAnn, botEffect)
thunkApplyArgs (Envs _ rEnv lEnv) fAnn args retRegs = 
    let retRegAnn   = regionVarsToAnn rEnv retRegs
        (cAnn,cEff) = foldl (\(sAnn,sEff) -> addEffect sEff . thunkApplyArg lEnv AUnit sAnn) 
                            (fAnn,botEffect) 
                            (init args)
        (rAnn,rEff) = thunkApplyArg lEnv retRegAnn cAnn (last args)
    in (rAnn, AAdd cEff rEff)

-- | Apply additional regions first, then arguments to a function
funcApplyArgs :: Envs 
              -> Annotation -> RegionVars -> [Either Type Local] -> RegionVars 
              -> (Annotation, Effect)
funcApplyArgs envs@(Envs _ rEnv _) fAnn aRegs args retRegs = 
    thunkApplyArgs envs (AApl fAnn $ regionVarsToAnn rEnv aRegs) args retRegs 

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


-- | Convert RegionVars to an annotions
regionVarsToAnn :: RegionEnv -> RegionVars -> Annotation
regionVarsToAnn rEnv (RegionVarsSingle r) = AReg r--constrIdxToAnn $ lookupReg rEnv r
regionVarsToAnn rEnv (RegionVarsTuple rs) = ATuple $ map (regionVarsToAnn rEnv) rs


constrIdxToAnn :: ConstrIdx -> Annotation 
constrIdxToAnn (Region r)   = AReg r
constrIdxToAnn (AnnVar a)   = AVar a
constrIdxToAnn (CnProj i c) = AProj i $ constrIdxToAnn c
