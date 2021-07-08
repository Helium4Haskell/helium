{-# LANGUAGE BangPatterns #-}
module Helium.CodeGeneration.Iridium.RegionSize.Analysis
    (analyseMethods)
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.Either(rights,lefts)
import Data.List(foldl')
import qualified Data.Map.Strict as M

-- | De bruijn index for the local fixpoint
localFixIdx :: Int
localFixIdx = 0

-- | Return region de bruijn index
rRegIdx :: Int
rRegIdx = 1

-- | Index for the last function argument
lstArgIdx :: Int
lstArgIdx = 2

-- | Additional regions de bruijn index
aRegIdx :: Int -> Int
aRegIdx dbz = dbz + 1

{- De bruijn index for the fixpoint for multually recursive methods
    Index is based on the 'de bruijn size' of the arguments.
-}
mutaulRecursionFixIdx :: Int -> Int
mutaulRecursionFixIdx dbz = dbz + 2

-- | The number of debruin indices created by the function arguments
deBruinSize :: [Either Quantor Local] -> Int
deBruinSize = (*) 2 . length . rights

----------------------------------------------------------------
-- Analysis
----------------------------------------------------------------

{-| Analyse a (possibilty recursive) binding group
    Pass == 0: Create a fixpoint for the binding group and insert it in the gEnv
    Pass \= 0: Leave the global env as is
-}
type Pass = Int
analyseMethods :: Pass ->  GlobalEnv -> [(Id,Method)] -> (Annotation, [Effect])
analyseMethods pass gEnv methods =
    let (anns, effects, sorts) = unzip3 $ (\m -> analyseMethod (makeGEnv m) m) <$> methods
    in case pass of 
          0 -> (annRemLocalRegs $ AFix sorts anns, effects)
          _ -> (ATuple anns, effects)
  where {- Replace the mutually recurcive positions in GEnv 
            with a debruijn index of the recursive fixpoint -}
        makeGEnv (methodName, method) = 
            let idx = mutaulRecursionFixIdx (deBruinSize $ methodArguments method)
                -- Account for two extra lambdas in the case of zero arity functions
                mutRecIdx = if methodArity method == 0 then idx + 2 else idx 
            in case pass of
                 0 -> fst $ foldl' (makeFixVar mutRecIdx) (gEnv,0) methods
                 _ -> gEnv
        makeFixVar fixIdx (env, i) (methodName, _) =
            (updateGlobal methodName (AProj i $ AVar fixIdx) env, i+1)

-- | Analyse the effect and annotation of a method
analyseMethod :: GlobalEnv -> (Id, Method) -> (Annotation, Effect, Sort)
analyseMethod gEnv@(GlobalEnv tEnv _ dEnv) (methodName, method@(Method _ aRegs args rType rRegs _ fstBlock otherBlocks)) =
    let !rEnv      = regEnvFromArgs (deBruinSize args) aRegs rRegs
        !(lEnv,lAnns,lSrts)  = analyseLocals gEnv rEnv method
        !envs      = (Envs gEnv rEnv lEnv)
        !rSort     = sortAssign dEnv $ typeNormalize tEnv rType
        !(bAnns,bSrts) = analyseBlocks rSort envs (fstBlock:otherBlocks)

        -- Wrap body in fixpoint, quants and lambdas
        !localFix = AProj 0 . AFix (bSrts ++ lSrts) $ bAnns ++ lAnns 
        !fAnn = wrapBody gEnv rType args localFix

        !(annotation, effect) = fixZeroArity method $ ALam (regionVarsToSort aRegs) fAnn
    in ( annotation 
       , effect 
       , methodSortAssign tEnv dEnv method) 


-- | Wrap a function body into its arguments (AQuant or `A -> P -> (A,C)')
wrapBody :: GlobalEnv 
         -> Type                   -- ^ Return type 
         -> [Either Quantor Local] -- ^ Arguments 
         -> Annotation -> Annotation
wrapBody (GlobalEnv tEnv _ dEnv) rType args a 
        | length (rights args) == 0 = annWrapQuants (length $ lefts args) (ALam retRegSrt a)
        | otherwise = foldr (wrapBody' False) (wrapBody' True (last args) a) (init args) 
    where
        wrapBody' _     (Left  _) bAnn = AQuant bAnn
        wrapBody' first (Right l) bAnn = let argS  = sortAssign dEnv . typeNormalize tEnv $ localType l
                                             rSort = if first then retRegSrt else SortTuple [SortMonoRegion,SortUnit]
                                             bAnn' = if first then bAnn      else ATuple [bAnn,botEffect]
                                         in ALam argS $ ALam rSort bAnn'
        -- Sort of the return region
        retRegSrt = regionAssign dEnv $ TStrict (typeNormalize tEnv rType)


-- | Initial enviromentment based on function arguments
initEnvFromArgs :: TypeEnvironment -> DataTypeEnv -> [Either Quantor Local] -> LocalEnv
initEnvFromArgs _    _    []   = LocalEnv emptyMap emptyMap
initEnvFromArgs tEnv dEnv args = let argIdxs = createIdxs lstArgIdx $ reverse args
                                     lEnv    = LocalEnv emptyMap emptyMap
                                 in foldr insertArgument lEnv argIdxs
    where createIdxs _ []           = []
          createIdxs n (Left  q:xs) = (Left  q, n) : createIdxs (n) xs
          createIdxs n (Right t:xs) = (Right t, n) : createIdxs (n+2) xs

          -- | Insert method argument into lEnv, ignore quantors 
          insertArgument :: (Either Quantor Local, Int) -> LocalEnv -> LocalEnv
          insertArgument (Left  _    , _) lEnv = lEnv
          insertArgument (Right local, d) lEnv = lEnv { lEnvAnns = insertMap (localName local) (AVar d) (lEnvAnns lEnv)
                                                      , lEnvSrts = insertMap (localName local) (sortAssign dEnv . typeNormalize tEnv $ localType local) (lEnvSrts lEnv) }

-- | Region environment from additional regions and return regions
regEnvFromArgs :: Int -> RegionVars -> RegionVars -> RegionEnv
regEnvFromArgs dbz aRegs rRegs = M.union (go (AnnVar $ aRegIdx dbz) aRegs) (go (AnnVar rRegIdx) rRegs)
    where go var (RegionVarsSingle r) = M.singleton r var
          go var (RegionVarsTuple rs) = M.unions.map (\(i,r) -> go (CnProj i var) r) $ zip [0..] rs

{-| Fix problems arising from zero arity functions 
  Assigns the global regions to the return regions and additional regions. 
-} 
fixZeroArity :: Method -> Annotation -> (Annotation, Effect)
fixZeroArity (Method _ aRegs args _ rRegs _ _ _) ann = 
  case length $ rights args of 
    0 -> let aplARegs = AApl ann $ regionVarsToGlobal aRegs 
             newQuantIndexes = reverse $ TVar <$> [0..(length $ lefts args)-1] 
             quants a = foldr (const AQuant) a (lefts args) 
             aplTypes = foldl' AInstn aplARegs newQuantIndexes 
             aplRRegs = AApl aplTypes $ regionVarsToGlobal rRegs
         in (ALam SortUnit $ quants $ AProj 0 aplRRegs, AProj 1 aplRRegs) 
    _ -> (ann, botEffect)

----------------------------------------------------------------
-- Gathering local variable annotations
----------------------------------------------------------------

-- | Extract annotations for the locals from the method
analyseLocals :: GlobalEnv -> RegionEnv -> Method -> (LocalEnv, [Annotation], [Sort])
analyseLocals gEnv@(GlobalEnv tEnv _ dEnv) rEnv method@(Method _ _ args _ _ _ fstBlock otherBlocks) =
    let blocks = fstBlock:otherBlocks
        initEnv   = initEnvFromArgs tEnv dEnv args
        locals    = methodLocals False tEnv method 

        mkLocalFix = (\(idx,local) -> (localName local, AProj idx $ AVar localFixIdx))
        localAnnMap = mapFromList $ mkLocalFix <$> zip [length blocks..] locals
        
        mkLocalSrt = (\local -> (localName local, sortAssign dEnv $ (typeNormalize tEnv $ (localType local))))
        localSrtMap = mapFromList $ mkLocalSrt <$> locals
       
        initEnv'  = initEnv { lEnvAnns = unionMap (lEnvAnns initEnv) localAnnMap
                            , lEnvSrts = unionMap (lEnvSrts initEnv) localSrtMap }

        localEnv = foldl' (\lEnv -> localsOfBlock (Envs gEnv rEnv lEnv)) initEnv' blocks
        lAnnos = flip lookupLocalAnn localEnv <$> locals 
        lSorts = flip lookupLocalSrt localEnv <$> locals
    in (localEnv, lAnnos, lSorts)

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
        Match local target tys ids next -> localsOfMatch envs local target (typeNormalize (globTypeEnv gEnv) <$> tys) ids next
        NewRegion _ _   next -> localsOfInstr envs next
        ReleaseRegion _ next -> localsOfInstr envs next
        -- Other instructions are 'terminal nodes' that do not extend lEnv
        _ -> lEnv

-- | Locals of an allocation
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
    let dAnn  = dataTypeApplyArgs (globTypeEnv gEnv) lEnv (constructorName struct `lookupStruct` globDataEnv gEnv) args 
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
        lEnv'    = foldl'(flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs gEnv rEnv lEnv') next
-- Datatypes
localsOfMatch (Envs (GlobalEnv tEnv fEnv dEnv) rEnv lEnv) local (MatchTargetConstructor struct) tys ids next =
    let dataVar = lookupLocalAnn local lEnv
        destrcs = constructorName struct `lookupDestruct` dEnv
        deInsts = flip (dataTypeApplyArgs tEnv lEnv) (map Left tys) <$> destrcs
        -- Insert matched vars into lEnv
        newVars = flip AApl dataVar <$> deInsts
        lEnv'   = foldl'(flip $ uncurry insertMaybeId) lEnv (zip ids newVars)
    in localsOfInstr (Envs (GlobalEnv tEnv fEnv dEnv) rEnv lEnv') next 

----------------------------------------------------------------
-- Analysing the effect of a method
----------------------------------------------------------------

-- | Analyse each block to retrieve its annotation and sort
analyseBlocks :: Sort -- ^ Sort of functions return type 
              -> Envs -> [Block] -> ([Annotation], [Sort])
analyseBlocks retSrt envs blocks = 
    let mkBlockFix = (\(idx,bName) -> (bName, AProj idx $ AVar localFixIdx))
        initBEnv = mapFromList $ mkBlockFix <$> zip [0..] (blockName <$> blocks)
        bSrts = const (SortTuple [retSrt, SortConstr]) <$> blocks
        bAnns = analyseInstr envs initBEnv . blockInstr <$> blocks 
    in (unliftTuple <$> bAnns, bSrts) 


-- | Analyse an instruction for its annotation and effect
analyseInstr :: Envs -> BlockEnv -> Instruction -> (Annotation, Effect)
analyseInstr envs@(Envs _ _ lEnv) bEnv = go 
   where go (Let _ expr      next) =  
           let (_     , varEff) = analyseExpr envs expr
               (nxtAnn, nxtEff) = go next
           in (nxtAnn, AAdd varEff nxtEff)
         -- Allocations with region variables
         go (LetAlloc bnds   next) = analyseLetAlloc envs bEnv bnds next 
         -- Remove region from effect, size has been detrimined
         go (NewRegion _ _   next) = analyseInstr envs bEnv next
         -- Ignore release region
         go (ReleaseRegion r next) =
             let (nxtAnn, nxtEff) = analyseInstr envs bEnv next
             in  (nxtAnn, AMinus nxtEff r)
         -- Lookup the annotation and effect from block
         go (Jump block)           = liftTuple $ lookupBlock block bEnv 
         -- Join the effects of all the blocks
         go (Case _     cas)       = joinBlocks bEnv $ caseBlocks cas
         -- Lookup the variable annotation
         go (Return local)         = (lookupLocalAnn local lEnv, botEffect)
         -- No effect
         go (Unreachable Nothing)  = (ABot undefined, botEffect)
         go (Unreachable (Just l)) = (ABot $ lookupLocalSrt l lEnv, botEffect)
         -- Matching only reads, only effect of sub instruction
         go (Match _ _ _ _ next)   = go next


-- | Analyse letalloc for its annotation and effect
analyseLetAlloc :: Envs -> BlockEnv -> [Bind] -> Instruction ->  (Annotation, Effect)
analyseLetAlloc envs bEnv [] next = analyseInstr envs bEnv next
-- Thunk binds
analyseLetAlloc envs@(Envs _ rEnv _) bEnv (Bind _ (BindTargetThunk var tRegs) args dReg:bs) next =
    let tnkRegs = bindThunkIntermediate tRegs
        valRegs = bindThunkValue tRegs
        (_   ,bEff) = thunkApplyArgs envs (lookupVar var envs) args $ bindThunkValue tRegs
        (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd (AConstr $ constrOne $ lookupReg dReg rEnv) 
            --  (AAdd (AConstr $ collectRegs rEnv tnkRegs)
             (AAdd (AConstr $ collectRegs rEnv valRegs)
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
    in (rAnn, AAdd rEff (AConstr $ constrOne $ lookupReg dReg rEnv))
-- Datatypes
analyseLetAlloc envs@(Envs _ rEnv _) bEnv (Bind _ (BindTargetConstructor _) _ dReg:bs) next =
    let (rAnn,rEff) = analyseLetAlloc envs bEnv bs next
    in (rAnn, AAdd rEff (AConstr $ constrOne $ lookupReg dReg rEnv))

-- | Collect bounds from a regionvars
collectRegs :: RegionEnv -> RegionVars -> Constr
collectRegs rEnv (RegionVarsSingle r) = constrOne $ lookupReg r rEnv
collectRegs rEnv (RegionVarsTuple rs) = M.unions $ collectRegs rEnv <$> rs

-- | Find the annotation and effect of an expression
analyseExpr :: Envs -> Expr -> (Annotation, Effect)
analyseExpr envs@(Envs gEnv _ lEnv) = go
    where 
      -- Literals have unit annotation, no effect.
      go (Literal (LitString _))  = (literalStringAnn         , botEffect) 
      go (Literal _)              = (AUnit                    , botEffect) 
      -- Eval & Var: Lookup annotation of variable (can be global or local)
      go (Eval var)               = (lookupVar var envs       , botEffect)
      go (Var var)                = (lookupVar var envs       , botEffect)
      go (Cast local _)           = (lookupLocalAnn local lEnv, botEffect)
      -- No effect, annotation of local
      go (CastThunk local)        = (lookupLocalAnn local lEnv, botEffect)
      -- Join of the variable annotations in the branches
      go (Phi branches)           = (joinAnnList $ flip lookupLocalAnn lEnv <$> map phiVariable branches, botEffect)
      -- Primitive expression, does not allocate or cause any effect -> bottom
      go (PrimitiveExpr _ _)      = (AUnit, botEffect) 
      -- No effect, bottom annotation
      go (Undefined t)            = (ABot $ sortAssign (globDataEnv gEnv) t, botEffect)
      -- No effect, just annotation of local2
      go (Seq _ local2)           = (lookupLocalAnn local2 lEnv, botEffect)
      -- Instantiate types in local
      go (Instantiate local tys)  = (foldl' AInstn (local `lookupLocalAnn` lEnv) (typeNormalize (globTypeEnv gEnv) <$> tys), botEffect) 
      -- Apply all type and variable arguments
      go (Call gFun aRegs args rReg) = funcApplyArgs envs (globalFunctionName gFun `lookupGlobal` gEnv) aRegs args rReg

literalStringAnn :: Annotation
literalStringAnn = ATuple[ATuple[AUnit,ATuple[AUnit,AUnit]]]

----------------------------------------------------------------
-- Function calls
----------------------------------------------------------------

-- | Apply an argument to a function
thunkApplyArg :: TypeEnvironment -> LocalEnv 
              -> Annotation        -- ^ Return region
              -> Annotation        -- ^ Function 
              -> Either Type Local -- ^ Argument
              -> (Annotation,Effect)
thunkApplyArg tEnv _    _    fAnn (Left ty    ) = (AInstn fAnn $ typeNormalize tEnv ty, botEffect)
thunkApplyArg _    lEnv rReg fAnn (Right local) = liftTuple $ AApl (AApl fAnn $ lookupLocalAnn local lEnv) rReg

-- | Apply a list of arguments to a funtion
thunkApplyArgs :: Envs 
               -> Annotation -> [Either Type Local] -> RegionVars 
               -> (Annotation, Effect)
thunkApplyArgs _ fAnn [] _ = (fAnn, botEffect)
thunkApplyArgs (Envs gEnv rEnv lEnv) fAnn args retRegs = 
    let retRegAnn   = regionVarsToAnn rEnv retRegs
        (cAnn,cEff) = foldl'(\(sAnn,sEff) -> addEffect sEff . thunkApplyArg (globTypeEnv gEnv) lEnv (ATuple [AReg RegionGlobal, AUnit]) sAnn) 
                            (fAnn,botEffect) 
                            (init args)
        (rAnn,rEff) = thunkApplyArg (globTypeEnv gEnv) lEnv retRegAnn cAnn (last args)
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
    where go (Left _ ) xs = xs
          go (Right x) xs = lookupLocalAnn x lEnv : xs

-- | Apply bind arguments to a tuple
dataTypeApplyArgs :: TypeEnvironment -> LocalEnv
                  -> Annotation
                  -> [Either Type Local] 
                  -> Annotation
dataTypeApplyArgs tEnv lEnv = foldl' go
    where go ann (Left ty) = AInstn ann $ typeNormalize tEnv ty
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
joinAnnList (x:xs) = foldl' AJoin x xs


-- | Bottom for the effect
botEffect :: Effect
botEffect = AConstr constrBot

-- | Get the name of a block
blockName :: Block -> BlockName
blockName (Block name _) = name

-- | Get the name of a block
blockInstr :: Block -> Instruction
blockInstr (Block _ instr) = instr


-- | Convert RegionVars to an annotions
regionVarsToAnn :: RegionEnv -> RegionVars -> Annotation
regionVarsToAnn rEnv (RegionVarsSingle r) = constrIdxToAnn $ lookupReg r rEnv
regionVarsToAnn rEnv (RegionVarsTuple rs) = ATuple $ map (regionVarsToAnn rEnv) rs
