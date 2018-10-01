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

import Text.PrettyPrint.Leijen (pretty) -- TODO: Remove

import Helium.CodeGeneration.Iridium.Data

data Analyses = Analyses { arities :: IdMap CoreModule.Arity }

fromCore :: NameSupply -> Core.CoreModule -> Module
fromCore supply mod@(CoreModule.Module name _ _ decls) = Module name datas methods
  where
    datas = map (\(dataName, cons) -> DataType dataName cons) $ listFromMap consMap
    consMap = foldr dataTypeFromCoreDecl emptyMap decls
    methods = concat $ mapWithSupply (`fromCoreDecl` analyses) supply decls
    analyses = Analyses (aritiesMap mod)

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

fromCoreDecl :: NameSupply -> Analyses -> Core.CoreDecl -> [Method]
fromCoreDecl supply analyses decl@CoreModule.DeclValue{} = [toMethod supply analyses (CoreModule.declName decl) (CoreModule.valueValue decl)]
fromCoreDecl _ _ _ = []

toMethod :: NameSupply -> Analyses -> Id -> Core.Expr -> Method
toMethod supply analyses name expr = Method name (Block entryName args entry) blocks
  where
    (entryName, supply') = freshId supply
    (args, expr') = consumeLambdas expr
    Partial entry blocks = toInstruction supply' analyses args CReturn expr'

-- Removes all lambda expression, returns a list of arguments and the remaining expression.
consumeLambdas :: Core.Expr -> ([Id], Core.Expr)
consumeLambdas (Core.Lam name expr) = (name : args, expr')
  where
    (args, expr') = consumeLambdas expr
consumeLambdas expr = ([], expr)

-- Represents a part of a method. Used during the construction of a method.
data Partial = Partial Instruction [Block]

data Continue = CReturn | CBind (Id -> Instruction) [Block] 

infixr 3 +>
(+>) :: (Instruction -> Instruction) -> Partial -> Partial
f +> (Partial instr blocks) = Partial (f instr) blocks

infixr 2 &>
(&>) :: [Block] -> Partial -> Partial
bs &> (Partial instr blocks) = Partial instr $ bs ++ blocks

ret :: Id -> Continue -> Partial
ret x CReturn = Partial (Return x) []
ret x (CBind instr blocks) = Partial (instr x) blocks

toInstruction :: NameSupply -> Analyses -> [Id] -> Continue -> Core.Expr -> Partial
-- Let bindings
toInstruction supply analyses scope continue (Core.Let (Core.NonRec b) expr)
  = LetThunk [bind b]
    +> toInstruction supply analyses (boundVar b : scope) continue expr
  where
toInstruction supply analyses scope continue (Core.Let (Core.Strict (Core.Bind x val)) expr)
  = toInstruction supply1 analyses scope (CBind next blocks) val
  where
    (supply1, supply2) = splitNameSupply supply
    Partial instr blocks = toInstruction supply2 analyses (x : scope) continue expr
    next var = Let x (Var var) instr
toInstruction supply analyses scope continue (Core.Let (Core.Rec bs) expr)
  = LetThunk (map bind bs)
  +> toInstruction supply analyses (map boundVar bs ++ scope) continue expr

-- Match
-- TODO: Match with a single Alt can be transformed into a Match instruction, without any branching.
{- toInstruction supply scope continue (Core.Match x [Core.Alt pat expr]) = case pattern pat of
  Nothing -> -- `case x of _ -> expr` === expr
    toInstruction supply scope continue expr
  Just p ->
    Let name (Eval x)
    +> Match name p
    +> toInstruction supply (map declaredVarsInPattern bs ++ scope) continue expr
  where
    (name, supply') = freshId -}
toInstruction supply analyses scope continue (Core.Match x alts) =
  blocks
    &> (Let name (Eval x)
    +> transformAlts supply''' analyses scope continue' name alts)
  where
    (name, supply') = freshId supply
    (blockId, supply'') = freshId supply'
    (result, supply''') = freshId supply''
    blocks = case continue of
      CReturn -> []
      CBind cInstr cBlocks ->
        Block blockId (result : scope) (cInstr result)
        : blocks
    continue' = case continue of
      CReturn -> CReturn
      CBind _ _ -> CBind (\res -> (Jump blockId (res : scope))) []

-- Non-branching expressions
toInstruction supply analyses scope continue (Core.Lit lit) = Let name (Literal $ literal lit) +> ret name continue
  where
    (name, _) = freshId supply
toInstruction supply analyses scope continue (Core.Var var) = Let name (Eval var) +> ret name continue
  where
    (name, _) = freshId supply
toInstruction supply analyses scope continue expr = case getApplicationOrConstruction expr [] of
  (Left con, args) ->
    Let x (Alloc (conId con) args)
      +> ret x continue
  (Right fn, args) ->
    case lookupMap fn (arities analyses) of
      Just arity
        | arity == length args ->
          -- Applied the correct number of arguments, compile to a Call.
          Let x (Call fn args) +> ret x continue
        | arity >  length args ->
          -- Not enough arguments, cannot call the function yet. Compile to a thunk.
          -- The thunk is already in WHNF, as the application does not have enough arguments.
          LetThunk [BindThunk x fn args] +> ret x continue
        | otherwise ->
          -- Too many arguments. Evaluate the function with the first `arity` arguments,
          -- and build a thunk for the additional arguments. This thunk might need to be
          -- evaluated.
          Let x (Call fn $ take arity args)
            +> LetThunk [BindThunk y x $ drop arity args]
            +> Let z (Eval y)
            +> ret z continue
      Nothing ->
        -- Don't know whether some function must be evaluated, so bind it to a thunk
        -- and try to evaluate it.
        LetThunk [BindThunk x fn args]
          +> Let y (Eval x)
          +> ret y continue
  where
    (fn, args) = getApplication expr
    (x, supply') = freshId supply
    (y, supply'') = freshId supply'
    (z, supply''') = freshId supply''

transformAlts :: NameSupply -> Analyses -> [Id] -> Continue -> Id -> [Core.Alt] -> Partial
transformAlts supply analyses scope continue name [Core.Alt pat expr] = case pattern pat of
  Nothing ->
    toInstruction supply analyses scope continue expr
  Just p ->
    Match name p
    +> toInstruction supply analyses (declaredVarsInPattern p ++ scope) continue expr
transformAlts supply analyses scope continue name (alt@(Core.Alt pat expr) : alts) = case pattern pat of
  Nothing -> transformAlts supply analyses scope continue name [alt]
  Just p ->
    let
      (blockId, supply') = freshId supply
      blockArgs = declaredVarsInPattern p ++ scope
      Partial exprInstr exprBlocks = toInstruction supply analyses scope continue expr
    in Block blockId blockArgs exprInstr : exprBlocks
      &> IfMatch name p blockId blockArgs
      +> transformAlts supply' analyses scope continue name alts

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
pattern (Core.PatCon con args) = Just $ PatternCon (conId con) args
