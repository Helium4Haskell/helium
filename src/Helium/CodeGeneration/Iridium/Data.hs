{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Iridium is the intermediate representation (IR) that we use between Core and LLVM. It is an imperative
-- strict language. It features pattern matching.
--
-- A method consists of blocks. The first block of a method is the entry block. Each block takes arguments,
-- the entry block describes the arguments of the method.

module Helium.CodeGeneration.Iridium.Data where

import Lvm.Common.Id(Id)
import Data.List(intercalate)

import Helium.CodeGeneration.Iridium.Type

type BlockName = Id

data Module = Module
  { moduleName :: Id
  , moduleDataTypes :: [DataType]
  , moduleMethods :: [Method]
  }

data Method = Method Id [Variable] PrimitiveType Block [Block]
  deriving (Eq, Ord)

-- TODO: Annotations on methods
data MethodAnnotation
  = MAThunk -- ^ This method can be put in a thunk
  deriving (Eq, Ord)

data Variable = Variable { variableName :: Id, variableType :: PrimitiveType }
  deriving (Eq, Ord)

data Block = Block BlockName Instruction
  deriving (Eq, Ord)

data Pattern
  = PatternCon Id
  | PatternLit Literal
  deriving (Eq, Ord)

data Instruction
  = Let Id Expr Instruction
  | LetThunk [BindThunk] Instruction
  | Jump BlockName
  -- * Asserts that the variable matches with the specified constructor. If they do not match, the behaviour is undefined.
  | Match Variable Id [Id] Instruction
  | If Variable Pattern BlockName BlockName
  | Return Variable
  deriving (Eq, Ord)

data BindThunk = BindThunk { bindThunkVar :: Id, bindThunkFunction :: Variable, bindThunkVariables :: [Variable] }
  deriving (Eq, Ord)

data Expr
  = Literal Literal
  | Call Id [Variable]
  | Eval Variable
  | Alloc Id [Id]
  | Var Variable
  | Cast Variable PrimitiveType
  | Phi [(Variable, Id)]
  deriving (Eq, Ord)

data Literal
  = LitInt Int
  | LitChar Char
  | LitDouble Double
  deriving (Eq, Ord)

instance Show Literal where
  show (LitInt x) = show x
  show (LitChar x) = show x
  show (LitDouble x) = show x

instance Show Pattern where
  show (PatternCon con) = show con
  show (PatternLit lit) = show lit

instance Show Expr where
  show (Literal lit) = show lit
  show (Call fn args) = "call " ++ show fn ++ showArguments args
  show (Eval var) = "eval " ++ show var
  show (Alloc con args) = "alloc " ++ show con ++ showArguments args
  show (Var var) = "var " ++ show var
  show (Cast var t) = "cast " ++ show var ++ " as " ++ show t

instructionIndent :: String
instructionIndent = "    "

instance Show BindThunk where
  show (BindThunk var fn args) = show var ++ " = " ++ show fn ++ showArguments args

instance Show Instruction where
  show (Let var expr next) = instructionIndent ++ "let " ++ show var ++ " = " ++ show expr ++ "\n" ++ show next
  show (LetThunk binds next) = instructionIndent ++ "letthunk " ++ intercalate ", " (map show binds) ++ "\n" ++ show next
  show (Jump to) = instructionIndent ++ "jump " ++ show to
  show (Match var conId args next) = instructionIndent ++ "match " ++ show var ++ " on " ++ show conId ++ showArguments args ++ "\n" ++ show next
  show (If var pat whenTrue whenFalse) = instructionIndent ++ "if " ++ show var ++ " instanceof " ++ show pat ++ " then jump " ++ show whenTrue ++ " else " ++ show whenFalse
  show (Return var) = instructionIndent ++ "ret " ++ show var

instance Show Variable where
  show (Variable name t) = show name ++ ": " ++ show t

instance Show Block where
  show (Block name instruction) = "  " ++ show name ++ ":\n" ++ show instruction

instance Show Method where
  show (Method name args rettype entry blocks) = "fn " ++ show name ++ showArguments args ++ ": " ++ show rettype ++ "\n" ++ show entry ++ (blocks >>= ('\n' :) . show) ++ "\n"

instance Show Module where
  show (Module name decls methods) = "module " ++ show name ++ "\n" ++ (decls >>= ('\n' :) . show) ++ (methods >>= ('\n' :) . show)

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name datas methods) = Module name datas $ map fnMethod methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method name args rettype entry blocks) = Method name args rettype (fnBlock entry) $ map fnBlock blocks
    fnBlock :: Block -> Block
    fnBlock (Block name instr) = Block name $ fn instr
