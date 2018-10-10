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

data Method = Method Id PrimitiveType Block [Block]
  deriving (Eq, Ord)

-- TODO: Annotations on methods
data MethodAnnotation
  = MAThunk -- ^ This method can be put in a thunk
  deriving (Eq, Ord)

data Argument = Argument { argumentName :: Id, argumentType :: PrimitiveType }
  deriving (Eq, Ord)

data Block = Block BlockName [Argument] Instruction
  deriving (Eq, Ord)

data Pattern
  = PatternCon Id [Id]
  | PatternLit Literal
  deriving (Eq, Ord)

data Instruction
  = Let Id Expr Instruction
  | LetThunk [BindThunk] Instruction
  | Jump BlockName [Id]
  -- * Asserts that the variable matches with the pattern. If they do not match, the behaviour is undefined.
  | Match Id Pattern Instruction
  | IfMatch Id Pattern BlockName [Id] Instruction
  | Return Id
  deriving (Eq, Ord)

data BindThunk = BindThunk { bindThunkVar :: Id, bindThunkFunction :: Id, bindThunkArguments :: [Id] }
  deriving (Eq, Ord)

data Expr
  = Literal Literal
  | Call Id [Id]
  | Eval Id
  | Alloc Id [Id]
  | Var Id
  | Cast Id PrimitiveType
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
  show (PatternCon con args) = show con ++ showArguments args
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

declaredVarsInPattern :: Pattern -> [Id]
declaredVarsInPattern (PatternCon _ args) = args
declaredVarsInPattern (PatternLit _) = []

instance Show BindThunk where
  show (BindThunk var fn args) = show var ++ " = " ++ show fn ++ showArguments args

instance Show Instruction where
  show (Let var expr next) = instructionIndent ++ "let " ++ show var ++ " = " ++ show expr ++ "\n" ++ show next
  show (LetThunk binds next) = instructionIndent ++ "letthunk " ++ intercalate ", " (map show binds) ++ "\n" ++ show next
  show (Jump to args) = instructionIndent ++ "jump " ++ show to ++ showArguments args
  show (Match var pat next) = instructionIndent ++ "match " ++ show var ++ " on " ++ show pat ++ "\n" ++ show next
  show (IfMatch var pat to toArgs next) = instructionIndent ++ "ifmatch " ++ show var ++ " on " ++ show pat ++ " to " ++ show to ++ showArguments toArgs ++ "\n" ++ show next
  show (Return var) = instructionIndent ++ "ret " ++ show var

instance Show Argument where
  show (Argument name t) = show name ++ ": " ++ show t

instance Show Block where
  show (Block name args instruction) = "  " ++ show name ++ showArguments args ++ ":\n" ++ show instruction

instance Show Method where
  show (Method name rettype entry blocks) = "fn " ++ show name ++ ": " ++ show rettype ++ "\n" ++ show entry ++ (blocks >>= ('\n' :) . show) ++ "\n"

instance Show Module where
  show (Module name decls methods) = "module " ++ show name ++ "\n" ++ (decls >>= ('\n' :) . show) ++ (methods >>= ('\n' :) . show)

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name datas methods) = Module name datas $ map fnMethod methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method name rettype entry blocks) = Method name rettype (fnBlock entry) $ map fnBlock blocks
    fnBlock :: Block -> Block
    fnBlock (Block name args instr) = Block name args $ fn instr
