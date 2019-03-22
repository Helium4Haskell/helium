{-| Module      :  FromCore
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Converts Core into Iridium.

module Helium.CodeGeneration.Iridium.FromCore where

import Helium.CodeGeneration.Core.FunctionType(functionsMap)
import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString, stringFromId, freshIdFromId)
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Common.Byte(stringFromBytes)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as CoreModule
import Data.List(find, replicate, group, sort, sortOn, partition)
import Data.Maybe(fromMaybe, mapMaybe)
import Data.Either(partitionEithers)

import Text.PrettyPrint.Leijen (pretty)

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.TypeEnvironment
import Helium.CodeGeneration.Iridium.Parse.Module (parseFunctionType)
import Helium.CodeGeneration.Iridium.Parse.Parser (ParseError)
import Helium.CodeGeneration.Iridium.FileCache
import Helium.CodeGeneration.Iridium.FromCoreImports

fromCore :: FileCache -> NameSupply -> Core.CoreModule -> IO Module
fromCore cache supply mod@(CoreModule.Module name _ _ decls) = do
  imports <- fromCoreImports cache imported
  return $ fromCoreAfterImports imports supply mod defs dependencies
  where
    dependencies = listFromSet $ foldr gatherDependencies emptySet imported
    (imported, defs) = partition isImported decls

fromCoreAfterImports :: ([(Id, Declaration CustomDeclaration)], [(Id, Declaration DataType)], [(Id, Declaration TypeSynonym)], [(Id, Declaration AbstractMethod)]) -> NameSupply -> Core.CoreModule -> [Core.CoreDecl] -> [Id] -> Module
fromCoreAfterImports (importedCustoms, importedDatas, importTypes, importedAbstracts) supply mod@(CoreModule.Module name _ _ _) decls dependencies
  | not $ null abstracts = error "fromCore: Abstract method should be an imported declaration, found a definition instead"
  | otherwise = Module name dependencies (map snd $ importedCustoms ++ customs) (map snd importedDatas ++ datas) (map snd importTypes ++ synonyms) (map snd $ importedAbstracts ++ abstracts) (map snd methods)
  where
    datas = decls >>= dataTypeFromCoreDecl consMap
    synonyms = [ Declaration (CoreModule.declName decl) (visibility decl) (origin decl) (CoreModule.declCustoms decl) $ TypeSynonym (CoreModule.declType decl) | decl@CoreModule.DeclTypeSynonym{} <- decls ]
    consMap = foldr dataTypeConFromCoreDecl emptyMap decls
    (methods, abstracts) = partitionEithers $ concat $ mapWithSupply (`fromCoreDecl` env) supply decls
    customs = mapMaybe (customFromCoreDecl name) decls
    env = TypeEnv name (mapFromList $ map (\(dataName, d) -> (dataName, getConstructors d)) importedDatas ++ map (\d -> (declarationName d, getConstructors d)) datas) (unionMap valuesFunctions $ unionMap valuesAbstracts valuesCons {- $ unionMap valuesCons $ mapFromList builtins-}) Nothing
    valuesFunctions = mapMapWithId (\fnName fn -> ValueFunction (qualifiedName name fnName) fn CCFast) $ functionsMap mod
    valuesAbstracts = mapFromList $ map (\(fnName, Declaration qualified _ _ _ (AbstractMethod fnType annotations)) -> (fnName, ValueFunction qualified fnType $ callingConvention annotations)) importedAbstracts

    allConsList = map (\(name, Declaration qualified _ _ _ (DataType cons)) -> (name, cons)) importedDatas ++ listFromMap consMap
    valuesCons = mapFromList $ allConsList >>= (\(dataName, cons) -> map (\(Declaration conName _ _ _ (DataTypeConstructorDeclaration fields)) -> (conName, ValueConstructor (DataTypeConstructor dataName conName fields))) cons)

isImported :: Core.CoreDecl -> Bool
isImported decl = case CoreModule.declAccess decl of
  CoreModule.Defined _ -> False
  _ -> True

seqString :: String -> a -> a
seqString str a = foldr seq a str

-- We currently need to fully evaluate string q before calling idFromString. This is caused by the unsafe IO which idFromString does.
-- I think that if idFromString is called with a string which is not yet evaluated, idFromString will be called recursively
-- while evaluating the argument. This causes that there are two unsafe calls at the same time, which probably cause some conflict.
-- I don't know what exactly happens, but the compiler loops.
qualifiedName :: Id -> Id -> Id
qualifiedName moduleName name = seqString q $ idFromString q
  where
    q
      | stringFromId name == "main$" = "main"
      | otherwise = stringFromId moduleName ++ "#" ++ stringFromId name

customFromCoreDecl :: Id -> Core.CoreDecl -> Maybe (Id, Declaration CustomDeclaration)
customFromCoreDecl moduleName decl@CoreModule.DeclCustom{}
  | not isData = Just (name, Declaration (qualifiedName moduleName name) (visibility decl) (origin decl) (CoreModule.declCustoms decl) $ CustomDeclaration $ CoreModule.declKind decl)
  where
    name = CoreModule.declName decl
    isData = CoreModule.declKind decl == CoreModule.DeclKindCustom (idFromString "data")
customFromCoreDecl _ _ = Nothing

gatherDependencies :: Core.CoreDecl -> IdSet -> IdSet
gatherDependencies decl = case CoreModule.declAccess decl of
  CoreModule.Imported _ mod _ _ _ _ -> insertSet mod
  _ -> id

dataTypeFromCoreDecl :: IdMap [Declaration DataTypeConstructorDeclaration] -> Core.CoreDecl -> [Declaration DataType]
dataTypeFromCoreDecl consMap decl@CoreModule.DeclCustom{}
  | CoreModule.declKind decl == CoreModule.DeclKindCustom (idFromString "data")
    = [Declaration name (visibility decl) (origin decl) (CoreModule.declCustoms decl) $ DataType $ fromMaybe [] $ lookupMap name consMap]
  where
    name = CoreModule.declName decl
dataTypeFromCoreDecl _ _ = []

dataTypeConFromCoreDecl :: Core.CoreDecl -> IdMap [Declaration DataTypeConstructorDeclaration] -> IdMap [Declaration DataTypeConstructorDeclaration]
dataTypeConFromCoreDecl decl@CoreModule.DeclCon{} = case find isDataName (CoreModule.declCustoms decl) of
    Just (CoreModule.CustomLink dataType _) -> insertMapWith dataType [con] (con :)
    Nothing -> id
  where
    isDataName (CoreModule.CustomLink _ (CoreModule.DeclKindCustom name)) = name == idFromString "data"
    isDataName _ = False
    -- When adding strictness annotations to data types, `TypeAny` on the following line should be changed.
    con = Declaration (CoreModule.declName decl) (visibility decl) (origin decl) (CoreModule.declCustoms decl) (DataTypeConstructorDeclaration $ replicate (CoreModule.declArity decl) TypeAny)
dataTypeConFromCoreDecl _ = id

fromCoreDecl :: NameSupply -> TypeEnv -> Core.CoreDecl -> [Either (Id, Declaration Method) (Id, Declaration AbstractMethod)]
fromCoreDecl supply env decl@CoreModule.DeclValue{} = [Left (name, Declaration (qualifiedName (teModuleName env) name) (visibility decl) (origin decl) (CoreModule.declCustoms decl) method)]
  where
    name = CoreModule.declName decl
    method = toMethod supply env (CoreModule.declName decl) (CoreModule.valueValue decl)

-- This is not used anymore, as abstract methods are handled by FromCoreImports
fromCoreDecl supply env decl@CoreModule.DeclAbstract{} = [Right (name, Declaration (qualifiedName (teModuleName env) name) (visibility decl) (origin decl) (CoreModule.declCustoms decl) method)]
  where
    name = CoreModule.declName decl
    method = AbstractMethod (findType $ CoreModule.declArity decl) (if name == idFromString "main" then [AnnotateTrampoline, AnnotateCallConvention CCC] else [AnnotateTrampoline])

    findType :: CoreModule.Arity -> FunctionType
    findType arity = FunctionType (replicate arity TypeAny) TypeAnyWHNF

fromCoreDecl _ _ _ = []

idEntry, idMatchAfter, idMatchCase, idMatchDefault :: Id
idEntry = idFromString "entry"
idMatchAfter = idFromString "match_after"
idMatchCase = idFromString "match_case"
idMatchDefault = idFromString "match_default"

toMethod :: NameSupply -> TypeEnv -> Id -> Core.Expr -> Method
toMethod supply env name expr = Method args' returnType [AnnotateTrampoline] (Block entryName entry) blocks
  where
    (entryName, supply') = freshIdFromId idEntry supply
    (_, fntype@(FunctionType fnArgs returnType)) = fromMaybe (error "toMethod: could not find function signature") $ resolveFunction env name
    args' = zipWith (\(Core.Variable name _) t -> Local name t) args fnArgs -- TODO: Use types from Core
    (args, expr') = consumeLambdas expr
    env' = enterFunction name fntype $ expandEnvWithLocals args' env
    Partial entry blocks = toInstruction supply' env' CReturn expr'

-- Removes all lambda expression, returns a list of arguments and the remaining expression.
consumeLambdas :: Core.Expr -> ([Core.Variable], Core.Expr)
consumeLambdas (Core.Lam arg expr) = (arg : args, expr')
  where
    (args, expr') = consumeLambdas expr
consumeLambdas (Core.Forall x k expr) = consumeLambdas expr
consumeLambdas expr = ([], expr)

-- Represents a part of a method. Used during the construction of a method.
data Partial = Partial Instruction [Block]

data Continue = CReturn | CBind (Id -> PrimitiveType -> Partial)

infixr 3 +>
(+>) :: (Instruction -> Instruction) -> Partial -> Partial
f +> (Partial instr blocks) = Partial (f instr) blocks

infixr 2 &>
(&>) :: [Block] -> Partial -> Partial
bs &> (Partial instr blocks) = Partial instr $ bs ++ blocks

ret :: NameSupply -> TypeEnv -> Id -> PrimitiveType -> Continue -> Partial
ret supply env x t CReturn = Partial (castInstr $ Return casted) []
  where
    retType = teReturnType env
    (casted, castInstr) = maybeCastVariable supply (VarLocal $ Local x t) retType 
ret _ _ x t (CBind next) = next x t

toInstruction :: NameSupply -> TypeEnv -> Continue -> Core.Expr -> Partial
toInstruction supply env continue (Core.Forall x k e) = toInstruction supply env continue e
toInstruction supply env continue (Core.ApType e t) = toInstruction supply env continue e
-- Let bindings
toInstruction supply env continue (Core.Let (Core.NonRec b) expr)
  = castInstr
    +> LetAlloc [letbind]
    +> toInstruction supply2 env' continue expr
  where
    (castInstr, letbind) = bind supply1 env [] b
    (supply1, supply2) = splitNameSupply supply
    env' = expandEnvWithLetAlloc [letbind] env

toInstruction supply env continue (Core.Let (Core.Strict (Core.Bind (Core.Variable x _) val)) expr)
  = toInstruction supply1 env (CBind next) val
  where
    (supply1, supply2) = splitNameSupply supply
    next var t = Let x (Var $ VarLocal $ Local var t) +> toInstruction supply2 env' continue expr
      where env' = expandEnvWith (Local x t) env

toInstruction supply env continue (Core.Let (Core.Rec bs) expr)
  = foldr (.) id castInstructions
  +> LetAlloc binds
  +> toInstruction supply2 env' continue expr
  where
    (supply1, supply2) = splitNameSupply supply
    (castInstructions, binds) = unzip $ mapWithSupply (\s -> bind s env' locals) supply1 bs
    locals = map (coreBindLocal env) bs
    env' = expandEnvWithLocals locals env

-- Match
toInstruction supply env continue (Core.Match x alts) =
  blocks &> (case head alts of
    Core.Alt Core.PatDefault expr -> toInstruction supply'' env (head continues) expr
    -- We don't need to create a Case statement for tuples, we only Match on the elements of the tuple.
    Core.Alt (Core.PatCon (Core.ConTuple arity) _ fields) expr ->
      let
        locals = map (\name -> Local name TypeAny) fields
        env' = expandEnvWithLocals locals env
      in
        Match (resolve env x) (MatchTargetTuple arity) (map Just fields)
        +> toInstruction supply'' env' (head continues) expr
    Core.Alt (Core.PatCon (Core.ConId con) _ _) _ ->
      let ValueConstructor (DataTypeConstructor dataName _ _) = findMap con (teValues env)
      in transformCaseConstructor supply'' env continues x dataName alts
    Core.Alt (Core.PatLit (Core.LitInt _ _)) _ -> transformCaseInt supply'' env continues x alts
    Core.Alt (Core.PatLit _) _ -> error "Match on float literals is not yet supported"
    )
  where
    (supply1, supply2) = splitNameSupply supply
    jumps :: [(Local, Id)] -- Names of intermediate blocks and names of the variables containing the result
    jumps = mapWithSupply (\s _ ->
      let
        (blockName, s') = freshIdFromId idMatchCase s
        (varName, _) = freshId s'
      in (Local varName expectedType, blockName)) supply1 alts
    phiBranches = map (\(loc, block) -> PhiBranch block $ VarLocal loc) jumps
    (blockId, supply') = freshIdFromId idMatchAfter supply2
    (result, supply'') = freshId supply'
    expectedType = TypeAnyWHNF -- TODO: More precise type
    blocks = case continue of
      CReturn -> []
      CBind next ->
        let
          Partial cInstr cBlocks = next result expectedType
          resultBlock = Block blockId (Let result (Phi phiBranches) cInstr)
        in resultBlock : cBlocks
    continues = case continue of
      CReturn -> repeat CReturn
      CBind _ -> map (altJump blockId) jumps

-- Non-branching expressions
toInstruction supply env continue (Core.Lit lit) = Let name expr +> ret supply' env name (typeOfExpr expr) continue
  where
    (name, supply') = freshId supply
    expr = (Literal $ literal lit)
toInstruction supply env continue (Core.Var var) = case variable of
  VarGlobal (GlobalFunction _ (FunctionType (_ : _) _)) ->
    let
      bind = Bind name (BindTargetFunction variable) []
    in
      LetAlloc [bind] +> ret supply' env name TypeFunction continue
  _ ->
    Let name (Eval variable) +> ret supply' env name TypeAnyWHNF continue
  where
    variable = resolve env var
    (name, supply') = freshId supply
    (nameThunk, supply'') = freshId supply'

toInstruction supply env continue expr = case getApplicationOrConstruction expr [] of
  (Left (Core.ConId con), args) ->
    let
      dataTypeCon@(DataTypeConstructor dataName _ params) = case valueDeclaration env con of
        ValueConstructor c -> c
        _ -> error "toInstruction: Illegal target of allocation, expected a constructor"
      (casted, castInstructions) = maybeCasts supply''' env (zip args params)
      bind = Bind x (BindTargetConstructor dataTypeCon) casted
    in
      castInstructions
        +> LetAlloc [bind]
        +> ret supplyRet env x (TypeDataType dataName) continue
  (Left (Core.ConTuple arity), args) ->
    let
      (casted, castInstructions) = maybeCasts supply''' env (zip args $ repeat TypeAnyWHNF)
      bind = Bind x (BindTargetTuple arity) casted
    in
      castInstructions
        +> LetAlloc [bind]
        +> ret supplyRet env x (TypeTuple arity) continue
  (Right fn, args) ->
    case resolveFunction env fn of
      Just (qualifiedName, fntype@(FunctionType params returnType))
        | length params == length args ->
          -- Applied the correct number of arguments, compile to a Call.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args params)
          in
            castInstructions +> Let x (Call (GlobalFunction qualifiedName fntype) args') +> ret supplyRet env x returnType continue
        | length params >  length args ->
          -- Not enough arguments, cannot call the function yet. Compile to a thunk.
          -- The thunk is already in WHNF, as the application does not have enough arguments.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args params)
          in
            castInstructions
              +> LetAlloc [Bind x (BindTargetFunction $ VarGlobal $ GlobalFunction qualifiedName fntype) args']
              +> ret supplyRet env x TypeFunction continue
        | null params ->
          -- Function has no arguments, e.g. it is a global variable.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args (repeat TypeAny))
          in
            castInstructions
              +> LetAlloc [Bind y (BindTargetThunk $ VarGlobal $ GlobalVariable qualifiedName TypeAnyThunk) args']
              +> Let z (Eval $ VarLocal $ Local y TypeAnyThunk)
              +> ret supplyRet env z TypeAnyWHNF continue
        | otherwise ->
          -- Too many arguments. Evaluate the function with the first `length params` arguments,
          -- and build a thunk for the additional arguments. This thunk might need to be
          -- evaluated.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args (params ++ repeat TypeAny))
          in
            castInstructions
              +> Let x (Call (GlobalFunction qualifiedName fntype) $ take (length params) args')
              +> LetAlloc [Bind y (BindTargetThunk $ VarLocal $ Local x returnType) $ drop (length params) args']
              +> Let z (Eval $ VarLocal $ Local y TypeAnyThunk)
              +> ret supplyRet env z TypeAnyWHNF continue
      Nothing ->
        -- Don't know whether some function must be evaluated, so bind it to a thunk
        -- and try to evaluate it.
        let
          (supplyCast1, supplyCast2) = splitNameSupply supply'''
          (args', castInstructions) = maybeCasts supplyCast1 env (zip args $ repeat TypeAny)
          (fn', castInstructionFn) = maybeCast supplyCast2 env fn TypeFunction
        in
          castInstructions
            +> castInstructionFn
            +> LetAlloc [Bind x (BindTargetThunk fn') args']
            +> Let y (Eval $ VarLocal $ Local x TypeAnyThunk)
            +> ret supplyRet env y TypeAnyWHNF continue
  where
    (fn, args) = getApplication expr
    (supply1, supplyRet) = splitNameSupply supply
    (x, supply') = freshId supply1
    (y, supply'') = freshId supply'
    (z, supply''') = freshId supply''

altJump :: Id -> (Local, Id) -> Continue
altJump toBlock (Local toVar toType, intermediateBlockId) = CBind (\resultVar resultType ->
    let
      intermediateBlock = Block intermediateBlockId
        $ Let toVar (Cast (VarLocal $ Local resultVar resultType) toType)
        $ Jump toBlock
    in
      Partial (Jump intermediateBlockId) [intermediateBlock]
  )

maybeCast :: NameSupply -> TypeEnv -> Id -> PrimitiveType -> (Variable, Instruction -> Instruction)
maybeCast supply env name expected = maybeCastVariable supply (resolve env name) expected

maybeCastVariable :: NameSupply -> Variable -> PrimitiveType -> (Variable, Instruction -> Instruction)
maybeCastVariable supply var expected
  | expected == varType = (var, id)
  | otherwise = castTo supply var varType expected
  where
    varType = variableType var

castTo :: NameSupply -> Variable -> PrimitiveType -> PrimitiveType -> (Variable, Instruction -> Instruction)
castTo _ _ from TypeAnyThunk = error $ "FromCore.castTo: cannot cast from " ++ show from ++ " to any_thunk"
castTo supply var from to
  | from == TypeAny || from == TypeAnyThunk = (newVar, Let nameAnyWhnf (Eval var) . instructions)
  where
    (nameAnyWhnf, supply') = freshIdFromId (variableName var) supply
    (newVar, instructions) = maybeCastVariable supply' (VarLocal $ Local nameAnyWhnf TypeAnyWHNF) to
-- A function type with at least one argument is casted using a `letalloc`.
-- A function type with no arguments is handled using a normal `Cast` instruction.
castTo supply var (TypeGlobalFunction (FunctionType (_ : _) _)) to = (newVar, LetAlloc [Bind nameFunc (BindTargetFunction var) []] . instructions)
  where
    (nameFunc, supply') = freshIdFromId (variableName var) supply
    (newVar, instructions) = maybeCastVariable supply' (VarLocal $ Local nameFunc TypeFunction) to
castTo supply var _ to = (VarLocal $ Local casted to, Let casted $ Cast var to)
  where
    (casted, _) = freshIdFromId (variableName var) supply

maybeCasts :: NameSupply -> TypeEnv -> [(Id, PrimitiveType)] -> ([Variable], Instruction -> Instruction)
maybeCasts _ _ [] = ([], id)
maybeCasts supply env ((name, t) : tail) = (var : tailVars, instr . tailInstr)
  where
    (supply1, supply2) = splitNameSupply supply
    (var, instr) = maybeCast supply1 env name t
    (tailVars, tailInstr) = maybeCasts supply2 env tail

transformCaseInt :: NameSupply -> TypeEnv -> [Continue] -> Id -> [Core.Alt] -> Partial
transformCaseInt supply env continues name alts = Partial (castInstr $ Case var c) $ concat blocks
  where
    (supply1, supply2) = splitNameSupply supply
    (var, castInstr) = maybeCast supply1 env name TypeInt
    c = gatherCaseIntAlts branches
    branches :: [(Maybe Int, BlockName)]
    blocks :: [[Block]]
    (branches, blocks) = unzip $ mapWithSupply (`transformAltInt` env) supply2 $ zip alts continues 

gatherCaseIntAlts :: [(Maybe Int, BlockName)] -> Case
gatherCaseIntAlts ((Nothing, block) : _) = CaseInt [] block
gatherCaseIntAlts [(Just _, block)] = CaseInt [] block -- Promote last branch to the `otherwise` branch.
gatherCaseIntAlts ((Just value, block) : xs) = CaseInt ((value, block) : alts) def
  where
    CaseInt alts def = gatherCaseIntAlts xs

transformAltInt :: NameSupply -> TypeEnv -> (Core.Alt, Continue) -> ((Maybe Int, BlockName), [Block])
transformAltInt supply env (Core.Alt pattern expr, continue) = ((value, blockName), Block blockName instr : blocks)
  where
    value = case pattern of
      Core.PatLit (Core.LitInt value _) -> Just value
      _ -> Nothing
    (blockName, supply') = freshIdFromId idMatchCase supply
    Partial instr blocks = toInstruction supply' env continue expr

transformAlt :: NameSupply -> TypeEnv -> Continue -> Variable -> DataTypeConstructor -> [Id] -> Core.Expr -> Partial
transformAlt supply env continue var con@(DataTypeConstructor _ _ fields) args expr = 
  let
    locals = zipWith (\name t -> Local name t) args fields
    env' = expandEnvWithLocals locals env
  in
    Match var (MatchTargetConstructor con) (map Just args)
    +> toInstruction supply env' continue expr

transformCaseConstructor :: NameSupply -> TypeEnv -> [Continue] -> Id -> Id -> [Core.Alt] -> Partial
transformCaseConstructor supply env continues varName dataType alts = Partial (castInstr $ Case var c) blocks
  where
    (supply1, supply2) = splitNameSupply supply
    (var, castInstr) = maybeCast supply1 env varName (TypeDataType dataType)
    c = CaseConstructor alts'
    constructors = findMap dataType (teDataTypes env)
    (alts', blocks) = gatherCaseConstructorAlts supply2 env continues constructors var alts

gatherCaseConstructorAlts :: NameSupply -> TypeEnv -> [Continue] -> [DataTypeConstructor] -> Variable -> [Core.Alt] -> ([(DataTypeConstructor, BlockName)], [Block])
gatherCaseConstructorAlts _ _ _ _ _ [] = ([], [])
gatherCaseConstructorAlts supply env (continue:_) remaining _ (Core.Alt Core.PatDefault expr : _) = (map (\con -> (con, blockName)) remaining, Block blockName instr : blocks)
  where
    (blockName, supply') = freshIdFromId idMatchDefault supply
    Partial instr blocks = toInstruction supply' env continue expr
gatherCaseConstructorAlts supply env (continue:continues) remaining var (Core.Alt (Core.PatCon c _ args) expr : alts) = ((con, blockName) : nextAlts, Block blockName instr : blocks ++ nextBlocks)
  where
    ValueConstructor con = valueDeclaration env $ conId c
    remaining' = filter (/= con) remaining
    (blockName, supply') = freshIdFromId idMatchCase supply
    (supply1, supply2) = splitNameSupply supply'
    Partial instr blocks = transformAlt supply1 env continue var con args expr
    (nextAlts, nextBlocks) = gatherCaseConstructorAlts supply2 env continues remaining' var alts

-- locals: a list of all locals declared in the current Core.Let, in case of a recursive bind.
-- For a non recursive bind, locals is an empty list.
bind :: NameSupply -> TypeEnv -> [Local] -> Core.Bind -> (Instruction -> Instruction, Bind)
bind supply env locals (Core.Bind (Core.Variable x _) val) = (castInstructions . targetCast, Bind x target args')
  where
    (apOrCon, args) = getApplicationOrConstruction val []
    (supply1, supply2) = splitNameSupply supply
    (args', castInstructions) = maybeCasts supply1 env (zipWith argType args params)
    locals' = map (\l@(Local n t) -> (n, t)) locals
    -- We should not add casts for recursive references. This function prevents those casts,
    -- by replacing the expected type with the actual type of the variable
    argType :: Id -> PrimitiveType -> (Id, PrimitiveType)
    argType name t = case lookup name locals' of
      Nothing -> (name, t)
      Just ty -> (name, ty)

    target :: BindTarget
    params :: [PrimitiveType]
    targetCast :: Instruction -> Instruction
    (target, params, targetCast) = case apOrCon of
      Left (Core.ConId con) ->
        let ValueConstructor constructor@(DataTypeConstructor _ _ fields) = valueDeclaration env con
        in (BindTargetConstructor constructor, fields, id)
      Left (Core.ConTuple arity) -> (BindTargetTuple arity, replicate arity TypeAny, id)
      Right fn -> case resolveFunction env fn of
        Just (qualifiedName, fntype@(FunctionType fparams@(_ : _) returnType)) ->
          -- The bind might provide more arguments than the arity of the function, if the function returns another function.
          (BindTargetFunction $ VarGlobal $ GlobalFunction qualifiedName fntype, fparams ++ repeat TypeAny, id)
        _
          | null args -> error $ "bind: a secondary thunk cannot have zero arguments"
        _ ->
          let (t, castInstr) = maybeCast supply2 env fn TypeFunction
          in (BindTargetThunk t, repeat TypeAny, castInstr)

coreBindLocal :: TypeEnv -> Core.Bind -> Local
coreBindLocal env (Core.Bind (Core.Variable name _) expr) = Local name $ coreBindType env expr

coreBindType :: TypeEnv -> Core.Expr -> PrimitiveType
coreBindType env val = case apOrCon of
  Left (Core.ConId con) ->
    let ValueConstructor constructor@(DataTypeConstructor dataName _ fields) = valueDeclaration env con
    in TypeDataType dataName
  Left (Core.ConTuple arity) -> TypeTuple arity
  Right fn -> case resolveFunction env fn of
    Just (_, fntype@(FunctionType fparams returnType))
      | length args >= length fparams -> TypeAnyThunk
      | otherwise -> TypeFunction
    Nothing -> TypeAnyThunk
  where
    (apOrCon, args) = getApplicationOrConstruction val []

conId :: Core.Con -> Id
conId (Core.ConId x) = x
conId _ = error "conId: unexpected ConTuple in gatherCaseConstructorAlts"

getApplicationOrConstruction :: Core.Expr -> [Id] -> (Either Core.Con Id, [Id])
getApplicationOrConstruction (Core.Var x) accum = (Right x, accum)
getApplicationOrConstruction (Core.Con c) accum = (Left c, accum)
getApplicationOrConstruction (Core.Ap expr (Core.Var arg)) accum = getApplicationOrConstruction expr (arg : accum)
getApplicationOrConstruction (Core.ApType expr _) accum = getApplicationOrConstruction expr accum
getApplicationOrConstruction e _ = error $ "getApplicationOrConstruction: expression is not properly normalized: " ++ show (pretty e)

getApplication :: Core.Expr -> (Id, [Id])
getApplication expr = case getApplicationOrConstruction expr [] of
  (Left _, _) -> error $ "getApplication: expression is not property normalized, found a constructor, expected a function name"
  (Right fn, args) -> (fn, args)

literal :: Core.Literal -> Literal
literal (Core.LitInt x _) = LitInt x
literal (Core.LitDouble x) = LitFloat Float64 x
literal (Core.LitBytes x) = LitString $ stringFromBytes x 

resolve :: TypeEnv -> Id -> Variable
resolve env name = case valueDeclaration env name of
  ValueConstructor _ -> error "resolve: Constructor cannot be used as a value."
  ValueFunction qualifiedName (FunctionType [] _) _ -> VarGlobal $ GlobalVariable qualifiedName TypeAnyThunk
  ValueFunction qualifiedName fntype _ -> VarGlobal $ GlobalFunction qualifiedName fntype
  ValueVariable t -> VarLocal $ Local name t

resolveList :: TypeEnv -> [Id] -> [Variable]
resolveList env = map (resolve env)

origin :: Core.CoreDecl -> Maybe Id
origin decl = case CoreModule.declAccess decl of
  (CoreModule.Imported _ mod _ _ _ _) -> Just mod
  _ -> Nothing
