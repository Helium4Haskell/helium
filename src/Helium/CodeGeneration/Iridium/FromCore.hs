{-| Module      :  FromCore
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Converts Core into Iridium.

module Helium.CodeGeneration.Iridium.FromCore where

import Helium.CodeGeneration.Core.Arity(aritiesMap)
import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString, freshIdFromId)
import Lvm.Common.IdMap
import Lvm.Common.Byte(stringFromBytes)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as CoreModule
import Data.List(find, replicate)
import Data.Maybe(fromMaybe)
import Data.Either(partitionEithers)

import Text.PrettyPrint.Leijen (pretty) -- TODO: Remove

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.TypeEnvironment

fromCore :: NameSupply -> Core.CoreModule -> Module
fromCore supply mod@(CoreModule.Module name _ _ decls) = Module name datas abstracts methods
  where
    datas = map (\(dataName, cons) -> DataType dataName cons) $ listFromMap consMap
    consMap = foldr dataTypeFromCoreDecl emptyMap decls
    (methods, abstracts) = partitionEithers $ concat $ mapWithSupply (`fromCoreDecl` env) supply decls
    env = TypeEnv () (unionMap valuesFunctions $ unionMap valuesAbstracts $ unionMap valuesCons $ mapFromList builtins) Nothing
    valuesFunctions = mapMap (\arity -> ValueFunction (FunctionType (replicate arity TypeAny) TypeAnyWHNF)) $ aritiesMap mod
    valuesAbstracts = mapFromList $ map (\(AbstractMethod name fntype) -> (name, ValueFunction fntype)) abstracts
    valuesCons = mapFromList $ listFromMap consMap >>= (\(dataName, cons) -> map (\con@(DataTypeConstructor _ conName _) -> (conName, ValueConstructor con)) cons)

dataTypeFromCoreDecl :: Core.CoreDecl -> IdMap [DataTypeConstructor] -> IdMap [DataTypeConstructor]
dataTypeFromCoreDecl decl@CoreModule.DeclCon{} = case find isDataName (CoreModule.declCustoms decl) of
    Just (CoreModule.CustomLink dataType _) -> insertMapWith dataType [con dataType] (con dataType :)
    Nothing -> id
  where
    isDataName (CoreModule.CustomLink _ (CoreModule.DeclKindCustom name)) = name == idFromString "data"
    isDataName _ = False
    -- When adding strictness annotations to data types, `TypeAny` on the following line should be changed.
    con dataType = DataTypeConstructor dataType (CoreModule.declName decl) (replicate (CoreModule.declArity decl) TypeAny)
dataTypeFromCoreDecl _ = id

fromCoreDecl :: NameSupply -> TypeEnv -> Core.CoreDecl -> [Either Method AbstractMethod]
fromCoreDecl supply env decl@CoreModule.DeclValue{} = [Left $ toMethod supply env (CoreModule.declName decl) (CoreModule.valueValue decl)]
fromCoreDecl supply env decl@CoreModule.DeclAbstract{} = [Right $ AbstractMethod (CoreModule.declName decl) $ FunctionType (replicate (CoreModule.declArity decl) TypeAny) TypeAnyWHNF]
fromCoreDecl _ _ _ = []

idEntry, idMatchAfter :: Id
idEntry = idFromString "entry"
idMatchAfter = idFromString "match_after"
idMatchCase = idFromString "match_case"

toMethod :: NameSupply -> TypeEnv -> Id -> Core.Expr -> Method
toMethod supply env name expr = Method name args' returnType (Block entryName entry) blocks
  where
    (entryName, supply') = freshIdFromId idEntry supply
    fntype@(FunctionType fnArgs returnType) = fromMaybe (error "toMethod: could not find function signature") $ resolveFunction env name
    args' = zipWith Local args fnArgs
    (args, expr') = consumeLambdas expr
    env' = enterFunction name fntype $ expandEnvWithLocals args' env
    Partial entry blocks = toInstruction supply' env' CReturn expr'

-- Removes all lambda expression, returns a list of arguments and the remaining expression.
consumeLambdas :: Core.Expr -> ([Id], Core.Expr)
consumeLambdas (Core.Lam name expr) = (name : args, expr')
  where
    (args, expr') = consumeLambdas expr
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
-- Let bindings
toInstruction supply env continue (Core.Let (Core.NonRec b) expr)
  = castInstr
    +> LetAlloc [letbind]
    +> toInstruction supply2 env' continue expr
  where
    (castInstr, letbind) = bind supply1 env b
    (supply1, supply2) = splitNameSupply supply
    env' = expandEnvWithLetAlloc [letbind] env

toInstruction supply env continue (Core.Let (Core.Strict (Core.Bind x val)) expr)
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
    -- TODO: Is this recursive definition ok?
    (supply1, supply2) = splitNameSupply supply
    (castInstructions, binds) = unzip $ mapWithSupply (`bind` env') supply1 bs
    env' = expandEnvWithLetAlloc binds env

-- Match
toInstruction supply env continue (Core.Match x alts) =
  blocks
    &> transformAlts supply'' env continues x alts
  where
    (supply1, supply2) = splitNameSupply supply
    jumps :: [(Local, Id)] -- Names of intermediate blocks and names of the variables containing the result
    jumps = mapWithSupply (\s _ ->
      let
        (blockName, s') = freshIdFromId idMatchCase s
        (varName, _) = freshId s'
      in (Local varName expectedType, blockName)) supply alts
    phiBranches = map (\(loc, block) -> PhiBranch block $ VarLocal loc) jumps
    (blockId, supply') = freshIdFromId idMatchAfter supply
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
toInstruction supply env continue (Core.Var var) = Let name (Eval $ resolve env var) +> ret supply' env name TypeAnyWHNF continue
  where
    (name, supply') = freshId supply

toInstruction supply env continue expr = case getApplicationOrConstruction expr [] of
  (Left con, args) ->
    let
      dataTypeCon@(DataTypeConstructor dataName _ params) = case valueDeclaration env $ conId con of
        ValueConstructor c -> c
        _ -> error "toInstruction: Illegal target of allocation, expected a constructor"
      (casted, castInstructions) = maybeCasts supply''' env (zip args params)
      bind = Bind x (BindTargetConstructor dataTypeCon) casted
    in
      castInstructions
        +> LetAlloc [bind]
        +> ret supplyRet env x (TypeDataType dataName) continue
  (Right fn, args) ->
    case resolveFunction env fn of
      Just fntype@(FunctionType params returnType)
        | length params == length args ->
          -- Applied the correct number of arguments, compile to a Call.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args params)
          in
            castInstructions +> Let x (Call (Global fn fntype) args') +> ret supplyRet env x returnType continue
        | length params >  length args ->
          -- Not enough arguments, cannot call the function yet. Compile to a thunk.
          -- The thunk is already in WHNF, as the application does not have enough arguments.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args params)
          in
            castInstructions
              +> LetAlloc [Bind x (BindTargetFunction $ resolve env fn) args']
              +> ret supplyRet env x TypeFunction continue
        | otherwise ->
          -- Too many arguments. Evaluate the function with the first `length params` arguments,
          -- and build a thunk for the additional arguments. This thunk might need to be
          -- evaluated.
          let
            (args', castInstructions) = maybeCasts supply''' env (zip args (params ++ repeat TypeAny))
          in
            castInstructions
              +> Let x (Call (Global fn fntype) $ take (length params) args')
              +> LetAlloc [Bind y (BindTargetFunction $ VarLocal $ Local x returnType) $ drop (length params) args']
              +> Let z (Eval $ VarLocal $ Local y TypeAnyThunk)
              +> ret supplyRet env z TypeAnyWHNF continue
      Nothing ->
        -- Don't know whether some function must be evaluated, so bind it to a thunk
        -- and try to evaluate it.
        let
          (supplyCast1, supplyCast2) = splitNameSupply supply'''
          (args', castInstructions) = maybeCasts supplyCast1 env (zip args $ repeat TypeAny)
          (fn', castInstructionFn) = maybeCast supplyCast2 env fn TypeAnyThunk
        in
          castInstructions
            +> castInstructionFn
            +> LetAlloc [Bind x (BindTargetFunction fn') args']
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
castTo supply var TypeAny to = (newVar, Let nameAnyWhnf (Eval var) . instructions)
  where
    (nameAnyWhnf, supply') = freshIdFromId (variableName var) supply
    (newVar, instructions) = maybeCastVariable supply' (VarLocal $ Local nameAnyWhnf TypeAnyWHNF) to
castTo supply var (TypeGlobalFunction _) to = (newVar, LetAlloc [Bind nameFunc (BindTargetFunction var) []] . instructions)
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

transformAlt :: NameSupply -> TypeEnv -> Continue -> Id -> Core.Alt -> Partial
transformAlt supply env continue name (Core.Alt pat expr) = case constructorPattern pat of
  Nothing -> toInstruction supply env continue expr
  Just (_, []) -> toInstruction supply env continue expr
  Just (conId, args) ->
    let
      ValueConstructor con@(DataTypeConstructor _ _ fields) = valueDeclaration env $ conId
      locals = zipWith (\name t -> Local name t) args fields
      env' = expandEnvWithLocals locals env
    in
      Match (resolve env name) con (map Just locals)
      +> toInstruction supply env' continue expr

transformAlts :: NameSupply -> TypeEnv -> [Continue] -> Id -> [Core.Alt] -> Partial
transformAlts supply env (continue : _) name [alt] = transformAlt supply env continue name alt
transformAlts supply env (continue : continues) name (alt@(Core.Alt pat _) : alts) = case pattern env pat of
  Nothing -> transformAlt supply env continue name alt
  Just p ->
    let
      (blockTrue, supply') = freshId supply
      (blockFalse, supply'') = freshId supply'
      (supply1, supply2) = splitNameSupply supply''
      Partial whenTrueInstr whenTrueBlocks = transformAlt supply1 env continue name alt
      Partial whenFalseInstr whenFalseBlocks = transformAlts supply2 env continues name alts
      blocks = Block blockTrue whenTrueInstr : Block blockFalse whenFalseInstr : whenTrueBlocks ++ whenFalseBlocks
    in Partial (If (resolve env name) p blockTrue blockFalse) blocks

bind :: NameSupply -> TypeEnv -> Core.Bind -> (Instruction -> Instruction, Bind)
bind supply env (Core.Bind x val) = (castInstructions, Bind x target args')
  where
    (apOrCon, args) = getApplicationOrConstruction val []
    (args', castInstructions) = maybeCasts supply env (zip args params)
    target :: BindTarget
    params :: [PrimitiveType]
    (target, params) = case apOrCon of
      Left con ->
        let ValueConstructor constructor@(DataTypeConstructor _ _ fields) = valueDeclaration env (conId con)
        in (BindTargetConstructor constructor, fields)
      Right fn ->
        let
          fnVar = resolve env fn
          fields = case fnVar of
            VarLocal _ -> repeat TypeAny
            -- The bind might provide more arguments than the arity of the function, if the function returns another function.
            VarGlobal (Global _ (FunctionType f _)) -> f ++ repeat TypeAny
        in (BindTargetFunction fnVar, fields)

conId :: Core.Con a -> Id
conId (Core.ConId x) = x
conId _ = error "ConTags (tuples?) are not supported yet"

getApplicationOrConstruction :: Core.Expr -> [Id] -> (Either (Core.Con Core.Expr) Id, [Id])
getApplicationOrConstruction (Core.Var x) accum = (Right x, accum)
getApplicationOrConstruction (Core.Con c) accum = (Left c, accum)
getApplicationOrConstruction (Core.Ap expr (Core.Var arg)) accum = getApplicationOrConstruction expr (arg : accum)
getApplicationOrConstruction e _ = error $ "getApplicationOrConstruction: expression is not properly normalized: " ++ show (pretty e)

getApplication :: Core.Expr -> (Id, [Id])
getApplication expr = case getApplicationOrConstruction expr [] of
  (Left _, _) -> error $ "getApplication: expression is not property normalized, found a constructor, expected a function name"
  (Right fn, args) -> (fn, args)

literal :: Core.Literal -> Literal
literal (Core.LitInt x) = LitInt x
literal (Core.LitDouble x) = LitDouble x
literal (Core.LitBytes x) = LitString $ stringFromBytes x -- TODO: LitBytes

pattern :: TypeEnv -> Core.Pat -> Maybe Pattern
pattern _ Core.PatDefault = Nothing
pattern _ (Core.PatLit lit) = Just $ PatternLit $ literal lit
pattern env (Core.PatCon con args) = Just $ PatternCon constructor
  where
    ValueConstructor constructor = valueDeclaration env $ conId con

constructorPattern :: Core.Pat -> Maybe (Id, [Id])
constructorPattern (Core.PatCon con args) = Just (conId con, args)
constructorPattern _ = Nothing

resolve :: TypeEnv -> Id -> Variable
resolve env name = case valueDeclaration env name of
  ValueConstructor _ -> error "resolve: Constructor cannot be used as a value."
  ValueFunction fntype -> VarGlobal $ Global name fntype
  ValueVariable t -> VarLocal $ Local name t

resolveList :: TypeEnv -> [Id] -> [Variable]
resolveList env = map (resolve env)
