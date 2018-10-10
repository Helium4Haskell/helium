{-| Module      :  FromCore
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Converts Core into Iridium.

module Helium.CodeGeneration.Iridium.FromCore where

import Helium.CodeGeneration.Core.Arity(aritiesMap)
import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString)
import Lvm.Common.IdMap
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as CoreModule
import Data.List(find, replicate)
import Data.Maybe(fromMaybe)

import Text.PrettyPrint.Leijen (pretty) -- TODO: Remove

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.TypeEnvironment

fromCore :: NameSupply -> Core.CoreModule -> Module
fromCore supply mod@(CoreModule.Module name _ _ decls) = Module name datas methods
  where
    datas = map (\(dataName, cons) -> DataType dataName cons) $ listFromMap consMap
    consMap = foldr dataTypeFromCoreDecl emptyMap decls
    methods = concat $ mapWithSupply (`fromCoreDecl` env) supply decls
    env = TypeEnv () $ unionMap valuesFunctions valuesCons
    valuesFunctions = mapMap (\arity -> ValueFunction (FunctionType (replicate arity TypeAny) TypeAny)) $ aritiesMap mod
    valuesCons = mapFromList $ listFromMap consMap >>= (\(dataName, cons) -> map (\con@(DataTypeConstructor conName _) -> (conName, ValueConstructor dataName con)) cons)

dataTypeFromCoreDecl :: Core.CoreDecl -> IdMap [DataTypeConstructor] -> IdMap [DataTypeConstructor]
dataTypeFromCoreDecl decl@CoreModule.DeclCon{} = case find isDataName (CoreModule.declCustoms decl) of
    Just (CoreModule.CustomLink dataType _) -> insertMapWith dataType [con] (con :)
    Nothing -> id
  where
    isDataName (CoreModule.CustomLink _ (CoreModule.DeclKindCustom name)) = name == idFromString "data"
    isDataName _ = False
    -- When adding strictness annotations to data types, `TypeAny` on the following line should be changed.
    con = DataTypeConstructor (CoreModule.declName decl) (replicate (CoreModule.declArity decl) TypeAny)
dataTypeFromCoreDecl _ = id

fromCoreDecl :: NameSupply -> TypeEnv -> Core.CoreDecl -> [Method]
fromCoreDecl supply env decl@CoreModule.DeclValue{} = [toMethod supply env (CoreModule.declName decl) (CoreModule.valueValue decl)]
fromCoreDecl _ _ _ = []

toMethod :: NameSupply -> TypeEnv -> Id -> Core.Expr -> Method
toMethod supply env name expr = Method name TypeAnyWHNF (Block entryName entryArgs entry) blocks
  where
    (entryName, supply') = freshId supply
    entryArgs = zipWith Argument args $ fromMaybe (error "toMethod: could not find function signature") $ argumentsOf env name
    (args, expr') = consumeLambdas expr
    env' = expandEnvWithArguments entryArgs env
    Partial entry blocks = toInstruction supply' env' args CReturn expr'

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

ret :: Id -> PrimitiveType -> Continue -> Partial
ret x _ CReturn = Partial (Return x) []
ret x t (CBind next) = next x t

toInstruction :: NameSupply -> TypeEnv -> [Id] -> Continue -> Core.Expr -> Partial
-- Let bindings
toInstruction supply env scope continue (Core.Let (Core.NonRec b) expr)
  = LetThunk binds
    +> toInstruction supply env' (boundVar b : scope) continue expr
  where
    binds = [bind b]
    env' = expandEnvWithLetThunk binds env

toInstruction supply env scope continue (Core.Let (Core.Strict (Core.Bind x val)) expr)
  = toInstruction supply1 env scope (CBind next) val
  where
    (supply1, supply2) = splitNameSupply supply
    next var t = Let x (Var var) +> toInstruction supply2 env' (x : scope) continue expr
      where env' = expandEnvWith x t env

toInstruction supply env scope continue (Core.Let (Core.Rec bs) expr)
  = LetThunk binds
  +> toInstruction supply env' (map boundVar bs ++ scope) continue expr
  where
    binds = map bind bs
    env' = expandEnvWithLetThunk binds env

-- Match
toInstruction supply env scope continue (Core.Match x alts) =
  blocks
    &> (Let name (Eval x)
    +> transformAlts supply''' env scope continue' name alts)
  where
    (name, supply') = freshId supply
    (blockId, supply'') = freshId supply'
    (result, supply''') = freshId supply''
    blocks = case continue of
      CReturn -> []
      CBind next ->
        -- TODO: Replace TypeAnyWHNF with correct type
        let Partial cInstr cBlocks = next result TypeAnyWHNF
        in Block blockId (map (\var -> Argument var (typeOf env var)) scope) (cInstr) : cBlocks
    continue' = case continue of
      CReturn -> CReturn
      CBind _ -> CBind (\res t -> Partial (Jump blockId (res : scope)) [])

-- Non-branching expressions
toInstruction supply env scope continue (Core.Lit lit) = Let name expr +> ret name (typeOfExpr env expr) continue
  where
    (name, _) = freshId supply
    expr = (Literal $ literal lit)
toInstruction supply env scope continue (Core.Var var) = Let name (Eval var) +> ret name (typeOf env var) continue
  where
    (name, _) = freshId supply
toInstruction supply env scope continue expr = case getApplicationOrConstruction expr [] of
  (Left con, args) ->
    let
      expr = (Alloc (conId con) args)
    in
      Let x expr
        +> ret x (typeOfExpr env expr) continue
  (Right fn, args) ->
    case argumentsOf env fn of
      Just params
        | length params == length args ->
          -- Applied the correct number of arguments, compile to a Call.
          Let x (Call fn args) +> ret x TypeAnyWHNF continue -- TODO: Replace TypeAnyWHNF with return type of function
        | length params >  length args ->
          -- Not enough arguments, cannot call the function yet. Compile to a thunk.
          -- The thunk is already in WHNF, as the application does not have enough arguments.
          LetThunk [BindThunk x fn args] +> ret x TypeFunction continue
        | otherwise ->
          -- Too many arguments. Evaluate the function with the first `length params` arguments,
          -- and build a thunk for the additional arguments. This thunk might need to be
          -- evaluated.
          Let x (Call fn $ take (length params) args)
            +> LetThunk [BindThunk y x $ drop (length params) args]
            +> Let z (Eval y)
            +> ret z TypeAnyWHNF continue
      Nothing ->
        -- Don't know whether some function must be evaluated, so bind it to a thunk
        -- and try to evaluate it.
        LetThunk [BindThunk x fn args]
          +> Let y (Eval x)
          +> ret y TypeAnyWHNF continue
  where
    (fn, args) = getApplication expr
    (x, supply') = freshId supply
    (y, supply'') = freshId supply'
    (z, supply''') = freshId supply''

transformAlt :: NameSupply -> TypeEnv -> [Id] -> Continue -> Id -> Core.Alt -> Partial
transformAlt supply env scope continue name (Core.Alt pat expr) = case constructorPattern pat of
  Nothing -> toInstruction supply env scope continue expr
  Just (con, args) ->
    let env' = expandEnvWithMatch con args env
    in
      Match name con args
      +> toInstruction supply env' (args ++ scope) continue expr

transformAlts :: NameSupply -> TypeEnv -> [Id] -> Continue -> Id -> [Core.Alt] -> Partial
transformAlts supply env scope continue name [alt] = transformAlt supply env scope continue name alt
transformAlts supply env scope continue name (alt@(Core.Alt pat _) : alts) = case pattern pat of
  Nothing -> transformAlt supply env scope continue name alt
  Just p ->
    let
      (blockTrue, supply') = freshId supply
      (blockFalse, supply'') = freshId supply'
      (supply1, supply2) = splitNameSupply supply''
      Partial whenTrueInstr whenTrueBlocks = transformAlt supply1 env scope continue name alt
      Partial whenFalseInstr whenFalseBlocks = transformAlts supply2 env scope continue name alts
      blocks = Block blockTrue blockArgs whenTrueInstr : Block blockFalse blockArgs whenFalseInstr : whenTrueBlocks ++ whenFalseBlocks
      blockArgs = map (\arg -> Argument arg (typeOf env arg)) scope
    in Partial (If name p blockTrue blockFalse) blocks

bind :: Core.Bind -> BindThunk
bind (Core.Bind x val) = BindThunk x fn args
  where
    (fn, args) = getApplication val

boundVar :: Core.Bind -> Id
boundVar (Core.Bind x _) = x

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
literal (Core.LitBytes x) = LitInt 0 -- TODO: LitBytes

pattern :: Core.Pat -> Maybe Pattern
pattern Core.PatDefault = Nothing
pattern (Core.PatLit lit) = Just $ PatternLit $ literal lit
pattern (Core.PatCon con args) = Just $ PatternCon (conId con)

constructorPattern :: Core.Pat -> Maybe (Id, [Id])
constructorPattern (Core.PatCon con args) = Just (conId con, args)
constructorPattern _ = Nothing
