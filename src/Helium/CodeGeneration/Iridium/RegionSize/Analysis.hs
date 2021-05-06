module Helium.CodeGeneration.Iridium.RegionSize.Analysis
    (analyseMethods)
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.List(mapAccumL)
import Data.Either (rights)
import qualified Data.Map as M

----------------------------------------------------------------
-- Analysis
----------------------------------------------------------------

-- | Analyse a (possibilty recursive) binding group
type Pass = Int
analyseMethods :: Pass ->  GlobalEnv -> [(Id,Method)] -> Annotation
analyseMethods pass gEnv methods =
    let (gEnv',_)    = case pass of
                          0 -> foldl makeFixVar (gEnv,0) methods
                          _ -> (gEnv,0)
        (anns,sorts) = unzip $ analyseMethod gEnv' <$> methods
        fixpoints    = AFix (SortTuple sorts) anns
    in case pass of 
          0 -> annRemLocalRegs fixpoints
          _ -> ATuple anns
        where makeFixVar (env, i) (methodName, (Method _ _ args _ _ _ _ _)) =
                    let fixIdx = deBruinSize args + 2
                        env'   = updateGlobal methodName (AProj i $ AVar fixIdx) env
                    in (env', i+1)

-- | Give the number of debruijn indexes the argument covers
deBruinSize :: [Either Quantor Local] -> Int
deBruinSize []           = 0 
deBruinSize (Left  _:xs) = 1 + deBruinSize xs
deBruinSize (Right _:xs) = 2 + deBruinSize xs

{-| Analyse the effect and annotation of a block
De Bruijn indices (dbz = de bruijn size):
    0      : Variable & block fixpoint argument
    1..dbz : Return region argument followed by arguments (A -> P -> A -> P -> ...)
    dbz+1  : Additional regions
    dbz+2  : Global fixpoint argument
-}
analyseMethod :: GlobalEnv -> (Id, Method) -> (Annotation, Sort)
analyseMethod gEnv@(GlobalEnv tEnv _ dEnv) (_, method@(Method _ aRegs args _ rRegs _ fstBlock otherBlocks)) =
    let blocks    = (fstBlock:otherBlocks)
        rEnv      = regEnvFromArgs (deBruinSize args) aRegs rRegs

        -- Create the local environment
        initEnv   = initEnvFromArgs dEnv args
        locals    = methodLocals False tEnv method
        fixIdx    = 0
        localAnnMap = mapFromList $ map (\(idx,local) -> (localName local, AProj idx $ AVar fixIdx)) $ zip [length blocks..] locals
        localSrtMap = mapFromList $ map (\local       -> (localName local, sortAssign dEnv $ typeWeaken (lEnvLamCount initEnv) (localType local))) locals
        initEnv'  = initEnv { lEnvAnns = unionMap (lEnvAnns initEnv) localAnnMap
                            , lEnvSrts = unionMap (lEnvSrts initEnv) localSrtMap }
        localEnv  = foldl (\lEnv -> localsOfBlock (Envs gEnv rEnv lEnv)) initEnv' blocks  

        -- Retrieve the annotation and effect of the function body
        initBEnv = mapFromList.map (\(idx,bName) -> (bName, AProj idx $ AVar fixIdx)) $ zip [0..] (blockName <$> blocks)
        blockAnn = blockAccum (Envs gEnv rEnv localEnv) initBEnv <$> blocks

        -- Generate the method annotation
        (aRegS, argS, rrSort, raSort) = argumentSorts dEnv method
        bSorts = const (SortTuple [raSort, SortConstr]) <$> blocks
        lAnnos = map (flip lookupLocalAnn localEnv) locals
        lSorts = map (flip lookupLocalSrt localEnv) locals
        localFix = AProj 0 . AFix (SortTuple (bSorts ++ lSorts)) $ (unliftTuple <$> blockAnn) ++ lAnnos
        fAnn  = ALam aRegS 
              $ if argS == []
                then ALam rrSort localFix -- IDEA: Now 'SortUnit' but could be a way to deal with thunk allocations
                else foldr (\s a -> wrapBody s (ATuple [a,botEffect]) SortUnit) 
                           (wrapBody (last argS) localFix rrSort) 
                           $ init argS
    in ( fAnn
       , SortLam aRegS . sortAssign dEnv $ methodType method) 

-- | Wrap a function body into a AQuant or `A -> P -> (A,C)'
wrapBody :: Maybe Sort -> Annotation -> Sort -> Effect
wrapBody mS bAnn rrSort = 
    case mS of
      Nothing -> AQuant $ AProj 0 bAnn
      Just s  -> ALam s $ ALam rrSort bAnn

{- Compute the sort of all method arguments,
    Returns a tuple of:
    0: Additional regions  
    1: Sort of regular argument (`Nothing' if quantifier)  
    2: Sort of return region
    3: Sort of return type
-}
argumentSorts :: DataTypeEnv -> Method -> (Sort, [Maybe Sort], Sort, Sort)
argumentSorts dEnv method@(Method _ regArgs args resTy _ _ _ _) = 
    let (FunctionType argTy _) = methodFunctionType method
        argSorts = mapAccumL (argumentSortAssign dEnv) 0 argTy
        aRegSort = regionVarsToSort regArgs
        rType    = typeWeaken (2*(length $ rights args)-1) $ TStrict resTy
        rrSort   = regionAssign dEnv rType
        raSort   = sortAssign dEnv rType
    in (aRegSort, snd argSorts, rrSort, raSort)

-- | Assign sort to types, return Nothing for a quantor
argumentSortAssign :: DataTypeEnv -> Int -> Either Quantor Type -> (Int, Maybe Sort)
argumentSortAssign dEnv n (Left _)   = (n,Nothing)
argumentSortAssign dEnv n (Right ty) = (n+2,Just $ sortWeaken n $ sortAssign dEnv ty)

-- | Initial enviromentment based on function arguments
-- TODO: Insert local arg sorts
initEnvFromArgs :: DataTypeEnv -> [Either Quantor Local] -> LocalEnv
initEnvFromArgs dEnv []   = LocalEnv 0 emptyMap emptyMap
initEnvFromArgs dEnv args = let argIdxs = createIdxs 2 $ reverse args
                                lEnv    = LocalEnv (1 + 2 * (length $ rights args)) emptyMap emptyMap
                            in foldr (insertArgument dEnv) lEnv argIdxs
    where createIdxs _ []           = []
          createIdxs n (Left  q:xs) = (Left  q, n) : createIdxs (n+1) xs
          createIdxs n (Right t:xs) = (Right t, n) : createIdxs (n+2) xs


-- | Insert method argument into lEnv, ignore quantors 
insertArgument :: DataTypeEnv -> (Either Quantor Local, Int) -> LocalEnv -> LocalEnv
insertArgument dEnv (Left  _    , _) lEnv = lEnv
insertArgument dEnv (Right local, d) lEnv = lEnv { lEnvAnns = insertMap (localName local) (AVar d) (lEnvAnns lEnv)
                                                 , lEnvSrts = insertMap (localName local) (sortAssign dEnv . typeWeaken d $ localType local) (lEnvSrts lEnv) }

-- | Region environment from additional regions and return regions
regEnvFromArgs :: Int -> RegionVars -> RegionVars -> RegionEnv
regEnvFromArgs dbz aRegs rRegs = M.union (go (AnnVar $ dbz+1) aRegs) (go (AnnVar 1) rRegs)
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
                                    lEnv'       = updateLocal name varAnn lEnv
                                in localsOfInstr (Envs gEnv rEnv lEnv') next
        LetAlloc binds next  -> localsOfLetAlloc envs binds next
        Match local target tys ids next -> localsOfMatch envs local target tys ids next
        NewRegion _ _   next -> localsOfInstr envs next
        ReleaseRegion _ next -> localsOfInstr envs next
        -- Other instructions are 'terminal nodes' that do not extend lEnv
        _ -> lEnv

localsOfLetAlloc :: Envs -> [Bind] -> Instruction -> LocalEnv
localsOfLetAlloc envs [] next = localsOfInstr envs next
-- Thunk binds
localsOfLetAlloc envs@(Envs gEnv rEnv lEnv) (Bind name (BindTargetThunk var tRegs) args _:bs) next =
    let (bAnn, _) = thunkApplyArgs envs (lookupVar var envs) args $ bindThunkValue tRegs
        lEnv'     = updateLocal name bAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next
-- Function binds
localsOfLetAlloc envs@(Envs gEnv rEnv lEnv) (Bind name (BindTargetFunction gFun aRegs tRegs) args _:bs) next =
    let gFunAnn   = lookupGlobal (globalFunctionName gFun) gEnv
        (bAnn, _) = funcApplyArgs envs gFunAnn aRegs args $ bindThunkValue tRegs
        lEnv'     = updateLocal name bAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next
-- Tuples
localsOfLetAlloc (Envs gEnv rEnv lEnv) (Bind name (BindTargetTuple _) args _:bs) next =
    let tAnn  = tupleApplyArgs lEnv args
        lEnv' = updateLocal name tAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next
-- Datatypes
localsOfLetAlloc (Envs gEnv rEnv lEnv) (Bind name (BindTargetConstructor struct) args _:bs) next =
    let dAnn  = dataTypeApplyArgs lEnv (constructorName struct `lookupStruct` globDataEnv gEnv) args 
        lEnv' = updateLocal name dAnn lEnv
    in localsOfLetAlloc (Envs gEnv rEnv lEnv') bs next


-- | Retrieve the local variables from a match instruction
localsOfMatch :: Envs
             -> Local -> MatchTarget -> [Type] -> [Maybe Id] -> Instruction  
             -> LocalEnv
localsOfMatch (Envs gEnv rEnv lEnv) local (MatchTargetTuple n) _ ids next =
    let tupleVar = lookupLocalAnn local lEnv 
        newVars  = map (flip AProj $ tupleVar) [0..(n-1)]
        -- Insert matched vars into lEnv
        lEnv'    = foldl (flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs gEnv rEnv lEnv') next
-- Datatypes
localsOfMatch (Envs gEnv rEnv lEnv) local (MatchTargetConstructor struct) _ ids next =
    let dataVar = lookupLocalAnn local lEnv
        destruc = constructorName struct `lookupDestruct` globDataEnv gEnv
        newVars = map (flip AApl dataVar) destruc
        -- Insert matched vars into lEnv
        lEnv'   = foldl (flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs gEnv rEnv lEnv') next 

----------------------------------------------------------------
-- Analysing the effect of a method
----------------------------------------------------------------

{-| Put the blockmap in to get the result. 
    Returns the extended bEnv, the annotation of the result and the effect.
-}
blockAccum :: Envs -> BlockEnv -> Block -> (Annotation, Effect)
blockAccum envs bEnv (Block _ instr) = analyseInstr envs bEnv instr


-- | Analyse an instruction
analyseInstr :: Envs -> BlockEnv -> Instruction -> (Annotation, Effect)
analyseInstr envs@(Envs _ _ lEnv) bEnv = go
   where go (Let _ expr      next) =  
           let (_     , varEff) = analyseExpr envs expr
               (nxtAnn, nxtEff) = go next
           in (nxtAnn, AAdd varEff nxtEff)
         -- Allocations with region variables
         go (LetAlloc bnds   next) = analyseLetAlloc envs bEnv bnds next 
         -- Remove region from effect, size has been detrimined
         go (NewRegion _ _   next) = 
             let (nxtAnn, nxtEff) = analyseInstr envs bEnv next
            --  in  (nxtAnn, AMinus nxtEff r)
             in  (nxtAnn, nxtEff)
         -- Ignore release region (TODO: Handling release regions correctly within loops for constant bounds?)
         go (ReleaseRegion _ next) = analyseInstr envs bEnv next
         -- Lookup the annotation and effect from block
         go (Jump block)           = liftTuple $ lookupBlock block bEnv 
         -- Join the effects of all the blocks
         go (Case _     cas)       = joinBlocks bEnv $ caseBlocks cas
         -- Lookup the variable annotation
         go (Return local)         = (lookupLocalAnn local lEnv, botEffect)
         -- No effect
         go (Unreachable Nothing)  = (ABot undefined, botEffect) -- TODO: What to do here?
         go (Unreachable (Just l)) = (ABot $ lookupLocalSrt l lEnv, botEffect)
         -- Matching only reads, only effect of sub instruction
         go (Match _ _ _ _ next)   = go next


-- | Analyse letalloc
analyseLetAlloc :: Envs -> BlockEnv -> [Bind] -> Instruction ->  (Annotation, Effect)
analyseLetAlloc envs bEnv [] next = analyseInstr envs bEnv next
-- Thunk binds
analyseLetAlloc envs@(Envs _ rEnv _) bEnv (Bind _ (BindTargetThunk var tRegs) args dReg:bs) next =
    let tnkRegs = bindThunkIntermediate tRegs
        (_   ,bEff) = thunkApplyArgs envs (lookupVar var envs) args $ bindThunkValue tRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg dReg rEnv) 
             (AAdd (AConstr $ collectRegs rEnv tnkRegs)
             (AAdd rEff bEff)))
-- Function binds
analyseLetAlloc envs@(Envs gEnv rEnv _) bEnv (Bind _ (BindTargetFunction gFun aRegs tRegs) args dReg:bs) next =
    let retRegs = bindThunkValue tRegs
        tnkRegs = bindThunkIntermediate tRegs
        gFunAnn = lookupGlobal (globalFunctionName gFun) gEnv
        (_   ,bEff) = funcApplyArgs envs gFunAnn aRegs args retRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg dReg rEnv) 
             (AAdd (AConstr $ collectRegs rEnv tnkRegs)
             (AAdd bEff rEff)))
-- Tuples
analyseLetAlloc envs@(Envs _ rEnv _) bEnv (Bind _ (BindTargetTuple _) _ dReg:bs) next =
    let (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg dReg rEnv) rEff)
-- Datatypes
analyseLetAlloc envs@(Envs _ rEnv _) bEnv (Bind _ (BindTargetConstructor _) _ dReg:bs) next =
    let (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg dReg rEnv) rEff)

-- TODO: Move to a better location & rename maybe
-- | Collect bounds from a regionvars
collectRegs :: RegionEnv -> RegionVars -> Constr
collectRegs rEnv (RegionVarsSingle r) = constrOne $ lookupReg r rEnv
collectRegs rEnv (RegionVarsTuple rs) = M.unions $ collectRegs rEnv <$> rs

-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr envs@(Envs gEnv _ lEnv) = go
    where 
      -- Literals have unit annotation, no effect. TODO: doesn't count for strings?
      go (Literal _)              = (AUnit                          , botEffect) 
      -- Eval & Var: Lookup annotation of variable (can be global or local)
      go (Eval var)               = (lookupVar var envs             , botEffect)
      go (Var var)                = (lookupVar var envs             , botEffect)
      go (Cast local _)           = (lookupLocalAnn local lEnv         , botEffect)
      -- No effect, annotation of local
      go (CastThunk local)        = (lookupLocalAnn local lEnv         , botEffect)
      -- Join of the variable annotations in the branches
      go (Phi branches)           = (joinAnnList $ flip lookupLocalAnn lEnv <$> map phiVariable branches, botEffect) 
      -- Primitive expression, does not allocate or cause any effect -> bottom
      go (PrimitiveExpr _ _)      = (AUnit, botEffect) 
      -- No effect, bottom annotation
      go (Undefined t)            = (ABot . sortAssign (globDataEnv gEnv) $ typeWeaken (lEnvLamCount lEnv) t, botEffect)
      -- No effect, just annotation of local2
      go (Seq _ local2)           = (lookupLocalAnn local2 lEnv        , botEffect)
      -- Instantiate types in local
      go (Instantiate local tys)  = (foldl AInstn (local `lookupLocalAnn` lEnv) (typeWeaken (lEnvLamCount lEnv) <$> tys), botEffect) 
      -- Apply all type and variable arguments
      go (Call gFun aRegs args rReg) = funcApplyArgs envs (globalFunctionName gFun `lookupGlobal` gEnv) aRegs args rReg

----------------------------------------------------------------
-- Function calls
----------------------------------------------------------------

-- | Apply an argument to a function
thunkApplyArg :: LocalEnv 
              -> Annotation        -- ^ Return region
              -> Annotation        -- ^ Function 
              -> Either Type Local -- ^ Argument
              -> (Annotation,Effect)
thunkApplyArg lEnv _    fAnn (Left ty    ) = (AInstn fAnn $ typeWeaken (lEnvLamCount lEnv) ty, botEffect) 
thunkApplyArg lEnv rReg fAnn (Right local) = liftTuple $ AApl (AApl fAnn $ lookupLocalAnn local lEnv) rReg

-- | Apply a list of arguments to a funtion
thunkApplyArgs :: Envs 
               -> Annotation -> [Either Type Local] -> RegionVars 
               -> (Annotation, Effect)
thunkApplyArgs _    fAnn []   _       = (fAnn, botEffect)
thunkApplyArgs (Envs _ rEnv lEnv) fAnn args retRegs = 
    let retRegAnn   = regionVarsToAnn rEnv retRegs
        (cAnn,cEff) = foldl (\(sAnn,sEff) -> addEffect sEff . thunkApplyArg lEnv (AUnit) sAnn) 
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

-- | Apply bind arguments to a tuple
tupleApplyArgs :: LocalEnv 
               -> [Either Type Local] 
               -> Annotation
tupleApplyArgs lEnv = ATuple . foldr go []
    where go (Left _ ) xs = xs -- error "Cannot apply type to tuple" 
          go (Right x) xs = lookupLocalAnn x lEnv : xs

-- | Apply bind arguments to a tuple
dataTypeApplyArgs :: LocalEnv
                  -> Annotation
                  -> [Either Type Local] 
                  -> Annotation
dataTypeApplyArgs lEnv = foldl go
    where go ann (Left ty) = AInstn ann ty
          go ann (Right x) = AApl ann (lookupLocalAnn x lEnv)

----------------------------------------------------------------
-- Analysis utilities
----------------------------------------------------------------

-- | Add an effect to an effect tuple
addEffect :: Effect -> (Annotation, Effect) -> (Annotation, Effect)
addEffect eff (a,e) = (a, AAdd eff e)

-- | Insert an ID if it is present
insertMaybeId :: Maybe Id -> Annotation -> LocalEnv -> LocalEnv
insertMaybeId Nothing  = flip const
insertMaybeId (Just i) = updateLocal i


-- | Get the case block names out of the case
caseBlocks :: Case -> [BlockName]
caseBlocks (CaseConstructor cases) = map snd cases
caseBlocks (CaseInt cases dflt)    = dflt : map snd cases


-- | Join of blocks
joinBlocks :: BlockEnv -> [BlockName] -> (Annotation, Effect)
joinBlocks bEnv blockNames = foldr joinTuples block blocks
    where (block:blocks) = liftTuple <$> flip lookupBlock bEnv <$> blockNames 

-- | The join of two tuples
joinTuples :: (Annotation, Effect) -> (Annotation, Effect) -> (Annotation, Effect)
joinTuples (a,b) (c,d) = (AJoin a c, AJoin b d)

-- | Join a list of annotations
joinAnnList :: [Annotation] -> Annotation
joinAnnList []     = rsError "joinAnnList: Empty annotation list"
joinAnnList [x]    = x
joinAnnList (x:xs) = foldl AJoin x xs


-- | Bottom for the effect
botEffect :: Effect
botEffect = AConstr constrBot

-- | Get the name of a block
blockName :: Block -> BlockName
blockName (Block name _) = name

-- | Convert RegionVars to an annotions
regionVarsToAnn :: RegionEnv -> RegionVars -> Annotation
regionVarsToAnn rEnv (RegionVarsSingle r) = constrIdxToAnn $ lookupReg r rEnv
regionVarsToAnn rEnv (RegionVarsTuple rs) = ATuple $ map (regionVarsToAnn rEnv) rs

