{-| Module      :  FromCore
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Converts Core into Iridium.

module Helium.CodeGeneration.Iridium.FromCore where

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString)
import Lvm.Common.IdMap
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as CoreModule
import Data.List(find, replicate)

import Text.PrettyPrint.Leijen (pretty) -- TODO: Remove

import Helium.CodeGeneration.Iridium.Data

fromCore :: NameSupply -> Core.CoreModule -> Module
fromCore supply (CoreModule.Module name _ _ decls) = Module name datas methods
  where
    datas = map (\(dataName, cons) -> DataType dataName cons) $ listFromMap consMap
    consMap = foldr dataTypeFromCoreDecl emptyMap decls
    methods = concat $ mapWithSupply fromCoreDecl supply decls

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

fromCoreDecl :: NameSupply -> Core.CoreDecl -> [Method]
fromCoreDecl supply decl@CoreModule.DeclValue{} = [toMethod supply (CoreModule.declName decl) (CoreModule.valueValue decl)]
fromCoreDecl _ _ = []

toMethod :: NameSupply -> Id -> Core.Expr -> Method
toMethod supply name expr = Method name (Block entryName args entry) blocks
  where
    (entryName, supply') = freshId supply
    (args, expr') = consumeLambdas expr
    Partial entry blocks = toInstruction supply' args CReturn expr'

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

toInstruction :: NameSupply -> [Id] -> Continue -> Core.Expr -> Partial
-- Let bindings
toInstruction supply scope continue (Core.Let (Core.NonRec b) expr)
  = LetThunk [bind b]
    +> toInstruction supply (boundVar b : scope) continue expr
  where
toInstruction supply scope continue (Core.Let (Core.Strict (Core.Bind x val)) expr)
  = toInstruction supply1 scope (CBind next blocks) val
  where
    (supply1, supply2) = splitNameSupply supply
    Partial instr blocks = toInstruction supply2 (x : scope) continue expr
    next var = Let x (Var var) instr
toInstruction supply scope continue (Core.Let (Core.Rec bs) expr)
  = LetThunk (map bind bs)
  +> toInstruction supply (map boundVar bs ++ scope) continue expr

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
toInstruction supply scope continue (Core.Match x alts) =
  blocks
    &> (Let name (Eval x)
    +> transformAlts supply''' scope continue' name alts)
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
toInstruction supply scope continue (Core.Lit lit) = Let name (Literal $ literal lit) +> ret name continue
  where
    (name, _) = freshId supply
toInstruction supply scope continue (Core.Var var) = Let name (Eval var) +> ret name continue
  where
    (name, _) = freshId supply
toInstruction supply scope continue expr = case getApplicationOrConstruction expr [] of
  (Left con, args) ->
    Let x (Alloc (conId con) args)
      +> ret x continue
  (Right fn, args) -> 
    LetThunk [BindThunk x fn args]
      +> Let y (Eval x)
      +> ret y continue
  where
    (fn, args) = getApplication expr
    (x, supply') = freshId supply
    (y, _) = freshId supply'

transformAlts :: NameSupply -> [Id] -> Continue -> Id -> [Core.Alt] -> Partial
transformAlts supply scope continue name [Core.Alt pat expr] = case pattern pat of
  Nothing ->
    toInstruction supply scope continue expr
  Just p ->
    Match name p
    +> toInstruction supply (declaredVarsInPattern p ++ scope) continue expr
transformAlts supply scope continue name (alt@(Core.Alt pat expr) : alts) = case pattern pat of
  Nothing -> transformAlts supply scope continue name [alt]
  Just p ->
    let
      (blockId, supply') = freshId supply
      blockArgs = declaredVarsInPattern p ++ scope
      Partial exprInstr exprBlocks = toInstruction supply scope continue expr
    in Block blockId blockArgs exprInstr : exprBlocks
      &> IfMatch name p blockId blockArgs
      +> transformAlts supply' scope continue name alts

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
