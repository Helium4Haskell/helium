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
import qualified Lvm.Core.Type as Core
import qualified Helium.CodeGeneration.Core.TypeEnvironment as Core
import qualified Lvm.Core.Module as Core
import Data.List(find, replicate, group, sort, sortOn, partition)
import Data.Maybe(fromMaybe, mapMaybe)
import Data.Either(partitionEithers, isLeft, isRight, fromLeft)

import Text.PrettyPrint.Leijen (pretty)

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.TypeEnvironment
import Helium.CodeGeneration.Iridium.Parse.Parser (ParseError)
import Helium.CodeGeneration.Iridium.FileCache
import Helium.CodeGeneration.Iridium.FromCoreImports
import Helium.CodeGeneration.Iridium.Utils

fromCore :: FileCache -> NameSupply -> Core.CoreModule -> IO Module
fromCore cache supply mod@(Core.Module name _ _ decls) = do
  imports <- fromCoreImports cache imported
  return $ fromCoreAfterImports imports supply mod defs dependencies
  where
    dependencies = listFromSet $ foldr gatherDependencies emptySet imported
    (imported, defs) = partition isImported decls

fromCoreAfterImports :: ([(Id, Declaration CustomDeclaration)], [(Id, Declaration DataType)], [(Id, Declaration TypeSynonym)], [(Id, Declaration AbstractMethod)]) -> NameSupply -> Core.CoreModule -> [Core.CoreDecl] -> [Id] -> Module
fromCoreAfterImports (importedCustoms, importedDatas, importTypes, importedAbstracts) supply mod@(Core.Module name _ _ _) decls dependencies
  | not $ null abstracts = error "fromCore: Abstract method should be an imported declaration, found a definition instead"
  | otherwise = Module name dependencies (map snd $ importedCustoms ++ customs) (map snd importedDatas ++ datas) (map snd importTypes ++ synonyms) (map snd $ importedAbstracts ++ abstracts) (map snd methods)
  where
    coreEnv = Core.typeEnvForModule mod
    datas = decls >>= dataTypeFromCoreDecl consMap
    synonyms = [ Declaration (Core.declName decl) (visibility decl) (origin decl) (Core.declCustoms decl) $ TypeSynonym (Core.declType decl) | decl@Core.DeclTypeSynonym{} <- decls ]
    consMap = foldr dataTypeConFromCoreDecl emptyMap decls
    (methods, abstracts) = partitionEithers $ concat $ mapWithSupply (`fromCoreDecl` env) supply decls
    customs = mapMaybe (customFromCoreDecl name) decls
    env = TypeEnv
      name
      (mapFromList $ map (\(dataName, d) -> (dataName, getConstructors d)) importedDatas ++ map (\d -> (declarationName d, getConstructors d)) datas)
      (unionMap valuesFunctions $ unionMap valuesAbstracts valuesCons {- $ unionMap valuesCons $ mapFromList builtins-})
      Nothing
      coreEnv
    valuesFunctions = mapMapWithId (\fnName (tp, fnType) -> ValueFunction (qualifiedName name fnName) (functionTypeArity fnType) tp CCFast) $ functionsMap coreEnv mod
    valuesAbstracts = mapFromList $ map (\(fnName, Declaration qualified _ _ _ (AbstractMethod arity fnType annotations)) -> (fnName, ValueFunction qualified arity fnType $ callingConvention annotations)) importedAbstracts

    allConsList = map (\(name, Declaration qualified _ _ _ (DataType cons)) -> (name, cons)) importedDatas ++ listFromMap consMap
    valuesCons = mapFromList $ allConsList >>= (\(dataName, cons) -> map (\(Declaration conName _ _ _ (DataTypeConstructorDeclaration tp)) -> (conName, ValueConstructor (DataTypeConstructor conName tp))) cons)

isImported :: Core.CoreDecl -> Bool
isImported decl = case Core.declAccess decl of
  Core.Defined _ -> False
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
customFromCoreDecl moduleName decl@Core.DeclCustom{}
  | not isData = Just (name, Declaration (qualifiedName moduleName name) (visibility decl) (origin decl) (Core.declCustoms decl) $ CustomDeclaration $ Core.declKind decl)
  where
    name = Core.declName decl
    isData = Core.declKind decl == Core.DeclKindCustom (idFromString "data")
customFromCoreDecl _ _ = Nothing

gatherDependencies :: Core.CoreDecl -> IdSet -> IdSet
gatherDependencies decl = case Core.declAccess decl of
  Core.Imported _ mod _ _ _ _ -> insertSet mod
  _ -> id

dataTypeFromCoreDecl :: IdMap [Declaration DataTypeConstructorDeclaration] -> Core.CoreDecl -> [Declaration DataType]
dataTypeFromCoreDecl consMap decl@Core.DeclCustom{}
  | Core.declKind decl == Core.DeclKindCustom (idFromString "data")
    = [Declaration name (visibility decl) (origin decl) (Core.declCustoms decl) $ DataType $ fromMaybe [] $ lookupMap name consMap]
  where
    name = Core.declName decl
dataTypeFromCoreDecl _ _ = []

dataTypeConFromCoreDecl :: Core.CoreDecl -> IdMap [Declaration DataTypeConstructorDeclaration] -> IdMap [Declaration DataTypeConstructorDeclaration]
dataTypeConFromCoreDecl decl@Core.DeclCon{} = case find isDataName (Core.declCustoms decl) of
    Just (Core.CustomLink dataType _) -> insertMapWith dataType [con] (con :)
    Nothing -> id
  where
    isDataName (Core.CustomLink _ (Core.DeclKindCustom name)) = name == idFromString "data"
    isDataName _ = False
    -- When adding strictness annotations to data types, `TypeAny` on the following line should be changed.
    con = Declaration (Core.declName decl) (visibility decl) (origin decl) (Core.declCustoms decl) (DataTypeConstructorDeclaration $ Core.declType decl)
dataTypeConFromCoreDecl _ = id

fromCoreDecl :: NameSupply -> TypeEnv -> Core.CoreDecl -> [Either (Id, Declaration Method) (Id, Declaration AbstractMethod)]
fromCoreDecl supply env decl@Core.DeclValue{} = [Left (name, Declaration (qualifiedName (teModuleName env) name) (visibility decl) (origin decl) (Core.declCustoms decl) method)]
  where
    name = Core.declName decl
    method = toMethod supply env (Core.declName decl) (Core.valueValue decl)

fromCoreDecl _ _ _ = []

idEntry, idMatchAfter, idMatchCase, idMatchDefault :: Id
idEntry = idFromString "entry"
idMatchAfter = idFromString "match_after"
idMatchCase = idFromString "match_case"
idMatchDefault = idFromString "match_default"

toMethod :: NameSupply -> TypeEnv -> Id -> Core.Expr -> Method
toMethod supply env name expr = Method tp args returnType [AnnotateTrampoline] (Block entryName entry) blocks
  where
    (entryName, supply') = freshIdFromId idEntry supply
    (_, arity, tp) = fromMaybe (error "toMethod: could not find function signature") $ resolveFunction env name
    createArgument (Left quantor) _ = Left quantor
    createArgument (Right t) (Right (Core.Variable name _)) = Right $ Local name t
    (args, expr') = consumeLambdas expr
    returnType = Core.typeOfCoreExpression (teCoreEnv env') expr'
    env' = enterFunction name returnType $ expandEnvWithLocals [local | Right local <- args] env
    Partial entry blocks = toInstruction supply' env' CReturn expr'

-- Removes all lambda expression, returns a list of arguments and the remaining expression.
consumeLambdas :: Core.Expr -> ([Either Core.Quantor Local], Core.Expr)
consumeLambdas (Core.Lam (Core.Variable name tp) expr) = (Right (Local name tp) : args, expr')
  where
    (args, expr') = consumeLambdas expr
consumeLambdas (Core.Forall x k expr) = (Left x : args, expr')
  where
    (args, expr') = consumeLambdas expr
consumeLambdas expr = ([], expr)

-- Represents a part of a method. Used during the construction of a method.
data Partial = Partial Instruction [Block]

data Continue = CReturn | CBind (Id -> Partial)

infixr 3 +>
(+>) :: (Instruction -> Instruction) -> Partial -> Partial
f +> (Partial instr blocks) = Partial (f instr) blocks

infixr 2 &>
(&>) :: [Block] -> Partial -> Partial
bs &> (Partial instr blocks) = Partial instr $ bs ++ blocks

ret :: NameSupply -> TypeEnv -> Id -> Continue -> Partial
ret supply env x CReturn = Partial (Return $ VarLocal $ Local x $ Core.typeToStrict retType) []
  where
    retType = teReturnType env
ret _ _ x (CBind next) = next x

toInstruction :: NameSupply -> TypeEnv -> Continue -> Core.Expr -> Partial
toInstruction supply env continue (Core.Forall x k e) = toInstruction supply env continue e
toInstruction supply env continue (Core.ApType e t) = toInstruction supply env continue e
-- Let bindings
toInstruction supply env continue (Core.Let (Core.NonRec b) expr)
  = LetAlloc [letbind]
    +> toInstruction supply2 env' continue expr
  where
    letbind = bind supply1 env b
    (supply1, supply2) = splitNameSupply supply
    env' = expandEnvWithLetAlloc [letbind] env

toInstruction supply env continue (Core.Let (Core.Strict (Core.Bind (Core.Variable x t) val)) expr)
  = toInstruction supply1 env (CBind next) val
  where
    (supply1, supply2) = splitNameSupply supply
    t' = Core.typeToStrict t
    next var = Let x (Var $ VarLocal $ Local var t') +> toInstruction supply2 env' continue expr
      where env' = expandEnvWith (Local x t') env

toInstruction supply env continue (Core.Let (Core.Rec bs) expr)
  = LetAlloc binds
  +> toInstruction supply2 env' continue expr
  where
    (supply1, supply2) = splitNameSupply supply
    binds = mapWithSupply (\s -> bind s env') supply1 bs
    locals = map (coreBindLocal env) bs
    env' = expandEnvWithLocals locals env

-- Match
toInstruction supply env continue match@(Core.Match x alts) =
  blocks &> (case head alts of
    Core.Alt Core.PatDefault expr -> toInstruction supply'' env (head continues) expr
    -- We don't need to create a Case statement for tuples, we only Match on the elements of the tuple.
    Core.Alt (Core.PatCon (Core.ConTuple arity) instantiation fields) expr ->
      let
        locals = zipWith Local fields instantiation
        env' = expandEnvWithLocals locals env
      in
        Match (resolve env x) (MatchTargetTuple arity) instantiation (map Just fields)
        +> toInstruction supply'' env' (head continues) expr
    Core.Alt (Core.PatCon (Core.ConId con) _ _) _ ->
      let ValueConstructor constructor = findMap con (teValues env)
      in transformCaseConstructor supply'' env continues x (constructorDataType constructor) alts
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
      in (Local varName tp, blockName)) supply1 alts
    phiBranches = map (\(loc, block) -> PhiBranch block $ VarLocal loc) jumps
    (blockId, supply') = freshIdFromId idMatchAfter supply2
    (result, supply'') = freshId supply'
    tp = Core.typeOfCoreExpression (teCoreEnv env) match
    blocks = case continue of
      CReturn -> []
      CBind next ->
        let
          Partial cInstr cBlocks = next result
          resultBlock = Block blockId (Let result (Phi phiBranches) cInstr)
        in resultBlock : cBlocks
    continues = case continue of
      CReturn -> repeat CReturn
      CBind _ -> map (altJump blockId tp) jumps

-- Non-branching expressions
toInstruction supply env continue (Core.Lit lit) = Let name expr +> ret supply' env name continue
  where
    (name, supply') = freshId supply
    expr = (Literal $ literal lit)
toInstruction supply env continue (Core.Var var) = case variable of
  VarGlobal (GlobalFunction _ _ _) ->
    let
      bind = Bind name (BindTargetFunction variable) []
    in
      LetAlloc [bind] +> ret supply' env name continue
  _ ->
    Let name (if typeIsStrict (variableType variable) then Var variable else Eval variable) +> ret supply' env name continue
  where
    variable = resolve env var
    (name, supply') = freshId supply
    (nameThunk, supply'') = freshId supply'

toInstruction supply env continue expr = case getApplicationOrConstruction expr [] of
  (Left (Core.ConId con), args) ->
    let
      dataTypeCon@(DataTypeConstructor dataName fntype) = case valueDeclaration env con of
        ValueConstructor c -> c
        _ -> error "toInstruction: Illegal target of allocation, expected a constructor"
      (casted, castInstructions, _) = maybeCasts supply''' env fntype args
    in
      castInstructions
        +> LetAlloc [Bind x (BindTargetConstructor dataTypeCon) casted]
        +> ret supplyRet env x continue
  (Left con@(Core.ConTuple arity), args) ->
    let
      fntype = Core.typeOfCoreExpression (teCoreEnv env) (Core.Con con)
      (args', castInstructions, _) = maybeCasts supply''' env fntype args
    in
      castInstructions
        +> LetAlloc [Bind x (BindTargetTuple arity) args']
        +> ret supplyRet env x continue
  (Right fn, args)
    | all isLeft args && not (isGlobalFunction $ resolve env fn) ->
      Let x (Instantiate (resolve env fn) $ map (fromLeft $ error "FromCore.toInstruction: expected Left") args)
        +> ret supplyRet env x continue
    | otherwise ->
      let argsArity = length $ filter isRight args
      in case resolveFunction env fn of
        Just (qualifiedName, arity, fntype)
          | arity == 0 ->
            -- Function has no arguments, e.g. it is a global variable.
            let
              (args', castInstructions, tp) = maybeCasts supply''' env fntype args
            in
              castInstructions
                +> LetAlloc [Bind y (BindTargetThunk $ VarGlobal $ GlobalVariable qualifiedName fntype) args']
                +> Let z (Eval $ VarLocal $ Local y tp)
                +> ret supplyRet env z continue
          | arity == argsArity ->
            -- Applied the correct number of arguments, compile to a Call.
            let
              (args', castInstructions, _) = maybeCasts supply''' env fntype args
            in
              castInstructions +> Let x (Call (GlobalFunction qualifiedName arity fntype) args') +> ret supplyRet env x continue
          | arity > argsArity ->
            -- Not enough arguments, cannot call the function yet. Compile to a thunk.
            -- The thunk is already in WHNF, as the application does not have enough arguments.
            let
              (args', castInstructions, tp) = maybeCasts supply''' env fntype args
            in
              castInstructions
                +> LetAlloc [Bind x (BindTargetFunction $ VarGlobal $ GlobalFunction qualifiedName arity fntype) args']
                +> ret supplyRet env x continue
          | otherwise ->
            -- Too many arguments. Evaluate the function with the first `length params` arguments,
            -- and build a thunk for the additional arguments. This thunk might need to be
            -- evaluated.
            let
              (supply1, supply2) = splitNameSupply supply'''
              (args1, args2) = paramsTakeValues arity args
              (args1', castInstructions1, tp1) = maybeCasts supply1 env fntype args1
              (args2', castInstructions2, tp2) = maybeCasts supply2 env tp1 args2
            in
              castInstructions1
                +> castInstructions2
                +> Let x (Call (GlobalFunction qualifiedName arity fntype) args1')
                +> LetAlloc [Bind y (BindTargetThunk $ VarLocal $ Local x tp1) args2']
                +> Let z (Eval $ VarLocal $ Local y tp2)
                +> ret supplyRet env z continue
        Nothing ->
          -- Don't know whether some function must be evaluated, so bind it to a thunk
          -- and try to evaluate it.
          let
            (supplyCast1, supplyCast2) = splitNameSupply supply'''
            (args', castInstructions, tp) = maybeCasts supplyCast1 env (variableType var) args
            bind = Bind x (BindTargetThunk var) args'
            var = resolve env fn
          in
            castInstructions
              +> LetAlloc [bind]
              +> Let y (Eval $ VarLocal $ Local x tp)
              +> ret supplyRet env y continue
  where
    (supply1, supplyRet) = splitNameSupply supply
    (x, supply') = freshId supply1
    (y, supply'') = freshId supply'
    (z, supply''') = freshId supply''

isGlobalFunction :: Variable -> Bool
isGlobalFunction (VarGlobal (GlobalFunction _ _ _)) = True

altJump :: Id -> Core.Type -> (Local, Id) -> Continue
altJump toBlock resultType (Local toVar toType, intermediateBlockId) = CBind (\resultVar ->
    let
      intermediateBlock = Block intermediateBlockId
        $ Let toVar (Cast (VarLocal $ Local resultVar resultType) toType)
        $ Jump toBlock
    in
      Partial (Jump intermediateBlockId) [intermediateBlock]
  )

maybeCast :: NameSupply -> TypeEnv -> Id -> Core.Type -> (Variable, Instruction -> Instruction)
maybeCast supply env name expected = maybeCastVariable supply env (resolve env name) expected

maybeCastVariable :: NameSupply -> TypeEnv -> Variable -> Core.Type -> (Variable, Instruction -> Instruction)
maybeCastVariable supply env var expected
  | Core.typeEqual (teCoreEnv env) expected varType && Core.typeIsStrict expected == Core.typeIsStrict varType = (var, id) -- TODO: Remove typeIsStrict when typeEqual understands strictness
  | otherwise = castTo supply env var varType expected
  where
    varType = variableType var

-- A cast should only change the strictness of a type
castTo :: NameSupply -> TypeEnv -> Variable -> Core.Type -> Core.Type -> (Variable, Instruction -> Instruction)
-- A function type with at least one argument is casted using a `letalloc`.
-- A function type with no arguments is handled using a normal `Cast` instruction.
castTo supply env var@(VarGlobal (GlobalFunction _ arity tp)) _ to
  | arity == 0 = error "castTo: Should not use a GlobalFunction for a function with arity 0. Use GlobalVariable instead"
  | otherwise = (newVar, LetAlloc [Bind nameFunc (BindTargetFunction var) []] . instructions)
  where
    (nameFunc, supply') = freshIdFromId (variableName var) supply
    (newVar, instructions) = maybeCastVariable supply' env (VarLocal $ Local nameFunc $ Core.typeToStrict tp) to
castTo supply env var from to
  | not (Core.typeIsStrict from) && Core.typeIsStrict to = (newVar, Let nameWhnf (Eval var) . instructions)
  where
    (nameWhnf, supply') = freshIdFromId (variableName var) supply
    (newVar, instructions) = maybeCastVariable supply' env (VarLocal $ Local nameWhnf (Core.typeToStrict from)) to
castTo supply env var _ to = (VarLocal $ Local casted to, Let casted $ Cast var to)
  where
    (casted, _) = freshIdFromId (variableName var) supply

maybeCasts :: NameSupply -> TypeEnv -> Core.Type -> [Either Core.Type Id] -> ([Either Core.Type Variable], Instruction -> Instruction, Core.Type)
maybeCasts _ _ tp [] = ([], id, tp)
maybeCasts supply env tp args'@(Right name : args) =
  case typeNormalizeHead (teCoreEnv env) tp of
    Core.TStrict tp' -> maybeCasts supply env tp' args'
    Core.TAp (Core.TAp (Core.TCon Core.TConFun) tArg) tReturn ->
      let
        (supply1, supply2) = splitNameSupply supply
        (var, instr) = maybeCast supply1 env name tArg
        (tailVars, tailInstr, returnType) = maybeCasts supply2 env tReturn args
      in
        (Right var : tailVars, instr . tailInstr, returnType)
    _ -> error ("FromCore.maybeCasts: expected function type, got " ++ Core.showType [] tp)
maybeCasts supply env tp (Left tpArg : args) =
  let
    tp' = Core.typeApply tp tpArg
    (tailVars, tailInstr, returnType) = maybeCasts supply env tp' args
  in
    (Left tpArg : tailVars, tailInstr, returnType)

transformCaseInt :: NameSupply -> TypeEnv -> [Continue] -> Id -> [Core.Alt] -> Partial
transformCaseInt supply env continues name alts = Partial (Case var c) $ concat blocks
  where
    (supply1, supply2) = splitNameSupply supply
    var = resolve env name
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

transformAlt :: NameSupply -> TypeEnv -> Continue -> Variable -> DataTypeConstructor -> [Core.Type] -> [Id] -> Core.Expr -> Partial
transformAlt supply env continue var con@(DataTypeConstructor _ tp) instantiation args expr = 
  let
    FunctionType fields _ = extractFunctionTypeNoSynonyms $ Core.typeApplyList tp instantiation
    locals = zipWith (\name (Right t) -> Local name t) args fields
    env' = expandEnvWithLocals locals env
  in
    Match var (MatchTargetConstructor con) instantiation (map Just args)
    +> toInstruction supply env' continue expr

transformCaseConstructor :: NameSupply -> TypeEnv -> [Continue] -> Id -> Id -> [Core.Alt] -> Partial
transformCaseConstructor supply env continues varName dataType alts = Partial (Case var c) blocks
  where
    var = resolve env varName
    (supply1, supply2) = splitNameSupply supply
    c = CaseConstructor alts'
    constructors = findMap dataType (teDataTypes env)
    (alts', blocks) = gatherCaseConstructorAlts supply2 env continues constructors var alts

gatherCaseConstructorAlts :: NameSupply -> TypeEnv -> [Continue] -> [DataTypeConstructor] -> Variable -> [Core.Alt] -> ([(DataTypeConstructor, BlockName)], [Block])
gatherCaseConstructorAlts _ _ _ _ _ [] = ([], [])
gatherCaseConstructorAlts supply env (continue:_) remaining _ (Core.Alt Core.PatDefault expr : _) = (map (\con -> (con, blockName)) remaining, Block blockName instr : blocks)
  where
    (blockName, supply') = freshIdFromId idMatchDefault supply
    Partial instr blocks = toInstruction supply' env continue expr
gatherCaseConstructorAlts supply env (continue:continues) remaining var (Core.Alt (Core.PatCon c instantiation args) expr : alts) = ((con, blockName) : nextAlts, Block blockName instr : blocks ++ nextBlocks)
  where
    ValueConstructor con = valueDeclaration env $ conId c
    remaining' = filter (/= con) remaining
    (blockName, supply') = freshIdFromId idMatchCase supply
    (supply1, supply2) = splitNameSupply supply'
    Partial instr blocks = transformAlt supply1 env continue var con instantiation args expr
    (nextAlts, nextBlocks) = gatherCaseConstructorAlts supply2 env continues remaining' var alts

bind :: NameSupply -> TypeEnv -> Core.Bind -> Bind
bind supply env (Core.Bind (Core.Variable x _) val) = Bind x target $ map toArg args
  where
    (apOrCon, args) = getApplicationOrConstruction val []
    (supply1, supply2) = splitNameSupply supply
    toArg (Left tp) = Left tp
    toArg (Right var) = Right $ resolve env var
    target :: BindTarget
    target = case apOrCon of
      Left (Core.ConId con) ->
        let ValueConstructor constructor = valueDeclaration env con
        in BindTargetConstructor constructor
      Left (Core.ConTuple arity) -> BindTargetTuple arity
      Right fn -> case resolveFunction env fn of
        Just (qualifiedName, arity, fntype) ->
          BindTargetFunction $ VarGlobal $ GlobalFunction qualifiedName arity fntype
        _
          | null args -> error $ "bind: a secondary thunk cannot have zero arguments"
        _ ->
          BindTargetThunk $ resolve env fn

coreBindLocal :: TypeEnv -> Core.Bind -> Local
coreBindLocal env (Core.Bind (Core.Variable name tp) expr) = 
  Local name $ Core.typeSetStrict (coreBindIsStrict env expr) tp
  -- Local name $ coreBindType env expr

coreBindIsStrict :: TypeEnv -> Core.Expr -> Bool
coreBindIsStrict env val = case apOrCon of
  Left _ -> True
  Right fn -> case resolveFunction env fn of
    Just (_, arity, _)
      | length (filter isRight args) >= arity -> False
      | otherwise -> True -- Not all arguments were passed, so the value is already in WHNF
    Nothing -> False
  where
    (apOrCon, args) = getApplicationOrConstruction val []

conId :: Core.Con -> Id
conId (Core.ConId x) = x
conId _ = error "conId: unexpected ConTuple in gatherCaseConstructorAlts"

getApplicationOrConstruction :: Core.Expr -> [Either Core.Type Id] -> (Either Core.Con Id, [Either Core.Type Id])
getApplicationOrConstruction (Core.Var x) accum = (Right x, accum)
getApplicationOrConstruction (Core.Con c) accum = (Left c, accum)
getApplicationOrConstruction (Core.Ap expr (Core.Var arg)) accum = getApplicationOrConstruction expr (Right arg : accum)
getApplicationOrConstruction (Core.ApType expr tp) accum = getApplicationOrConstruction expr (Left tp : accum)
getApplicationOrConstruction e _ = error $ "getApplicationOrConstruction: expression is not properly normalized: " ++ show (pretty e)

literal :: Core.Literal -> Literal
literal (Core.LitInt x _) = LitInt x
literal (Core.LitDouble x) = LitFloat Float64 x
literal (Core.LitBytes x) = LitString $ stringFromBytes x 

resolve :: TypeEnv -> Id -> Variable
resolve env name = case valueDeclaration env name of
  ValueConstructor _ -> error "resolve: Constructor cannot be used as a value."
  ValueFunction qualifiedName 0 fntype _ -> VarGlobal $ GlobalVariable qualifiedName fntype
  ValueFunction qualifiedName arity fntype _ -> VarGlobal $ GlobalFunction qualifiedName arity fntype
  ValueVariable t -> VarLocal $ Local name t

resolveList :: TypeEnv -> [Id] -> [Variable]
resolveList env = map (resolve env)

origin :: Core.CoreDecl -> Maybe Id
origin decl = case Core.declAccess decl of
  (Core.Imported _ mod _ _ _ _) -> Just mod
  _ -> Nothing
