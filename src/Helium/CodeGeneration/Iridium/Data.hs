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

import Lvm.Common.Id(Id, stringFromId, idFromString)
import Data.List(intercalate)

import Helium.CodeGeneration.Iridium.Type

type BlockName = Id

data Module = Module
  { moduleName :: Id
  , moduleDataTypes :: [DataType]
  , moduleMethods :: [Method]
  }

data Method = Method Id [Local] PrimitiveType Block [Block]
  deriving (Eq, Ord)

-- TODO: Annotations on methods
data MethodAnnotation
  = MAThunk -- ^ This method can be put in a thunk
  deriving (Eq, Ord)

data Local = Local { localName :: Id, localType :: PrimitiveType }
  deriving (Eq, Ord)

data Global = Global Id FunctionType
  deriving (Eq, Ord)

data Variable
  = VarLocal Local
  | VarGlobal Global
  deriving (Eq, Ord)

data Block = Block BlockName Instruction
  deriving (Eq, Ord)

data Pattern
  = PatternCon DataTypeConstructor
  | PatternLit Literal
  deriving (Eq, Ord)

data Instruction
  = Let Id Expr Instruction
  | LetAlloc [Bind] Instruction
  | Jump BlockName
  -- * Asserts that the variable matches with the specified constructor. If they do not match, the behaviour is undefined.
  | Match Variable DataTypeConstructor [Maybe Local] Instruction -- TODO: For consistency, Maybe Local should be replaced with Maybe Id, as we also don't use Local for Let and LetAlloc
  | If Variable Pattern BlockName BlockName
  | Return Variable
  deriving (Eq, Ord)

data Bind = Bind { bindVar :: Id, bindTarget :: BindTarget, bindArguments :: [Variable] }
  deriving (Eq, Ord)

data BindTarget
  = BindTargetFunction Variable
  | BindTargetConstructor DataTypeConstructor
  deriving (Eq, Ord)

bindType :: Bind -> PrimitiveType
bindType (Bind _ (BindTargetConstructor (DataTypeConstructor dataName _ _)) _) = TypeDataType dataName
bindType (Bind _ (BindTargetFunction (VarGlobal (Global fn (FunctionType fnargs _)))) args)
  | length args == length fnargs = TypeAnyThunk
  | otherwise = TypeFunction
bindType _ = TypeAnyThunk

bindLocal :: Bind -> Local
bindLocal b@(Bind var _ _) = Local var $ bindType b

data Expr
  = Literal Literal
  | Call Global [Variable]
  | Eval Variable
  | Var Variable
  | Cast Variable PrimitiveType
  | Phi [PhiBranch]
  deriving (Eq, Ord)

data PhiBranch = PhiBranch BlockName Variable
  deriving (Eq, Ord)

data Literal
  = LitInt Int
  | LitDouble Double
  | LitString String
  deriving (Eq, Ord)

instance Show Literal where
  show (LitInt x) = "int " ++ show x
  show (LitDouble x) = "float " ++ show x
  show (LitString x) = "str " ++ show x

instance Show Pattern where
  show (PatternCon con) = show con
  show (PatternLit lit) = show lit

instance Show Expr where
  show (Literal lit) = show lit
  show (Call fn args) = "call " ++ show fn ++ " $ " ++ showArguments args
  show (Eval var) = "eval " ++ show var
  show (Var var) = "var " ++ show var
  show (Cast var t) = "cast " ++ show var ++ " as " ++ show t
  show (Phi branches) = "phi " ++ showArguments branches

instance Show PhiBranch where
  show (PhiBranch branch var) = stringFromId branch ++ " => " ++ show var

instructionIndent :: String
instructionIndent = "  "

instance Show Bind where
  show b@(Bind _ target args) = show (bindLocal b) ++ " = " ++ show target ++ " $ " ++ showArguments args

instance Show BindTarget where
  show (BindTargetFunction global) = show global
  show (BindTargetConstructor con) = show con

instance Show Instruction where
  show (Let var expr next) = instructionIndent ++ "let " ++ show (Local var $ typeOfExpr expr) ++ " = " ++ show expr ++ "\n" ++ show next
  show (LetAlloc binds next) = instructionIndent ++ "letalloc " ++ intercalate ", " (map show binds) ++ "\n" ++ show next
  show (Jump to) = instructionIndent ++ "jump " ++ show to
  show (Match var conId args next) = instructionIndent ++ "match " ++ show var ++ " on " ++ show conId ++ showArguments' showField args ++ "\n" ++ show next
    where
      showField Nothing = "_"
      showField (Just l) = show l
  show (If var pat whenTrue whenFalse) = instructionIndent ++ "if " ++ show var ++ " matches " ++ show pat ++ " then jump " ++ stringFromId whenTrue ++ " else " ++ stringFromId whenFalse
  show (Return var) = instructionIndent ++ "ret " ++ show var

instance Show Local where
  show (Local name t) = "%" ++ stringFromId name ++ ": " ++ show t

instance Show Global where
  show (Global name fntype) = "@" ++ stringFromId name ++ ": " ++ show fntype

instance Show Variable where
  show (VarLocal local) = show local
  show (VarGlobal global) = show global

instance Show Block where
  show (Block name instruction) = stringFromId name ++ ":\n" ++ show instruction

instance Show Method where
  show (Method name args rettype entry blocks) = "define @" ++ stringFromId name ++ showArguments args ++ ": " ++ show rettype ++ " {\n" ++ show entry ++ (blocks >>= ('\n' :) . show) ++ "\n}\n"

instance Show Module where
  show (Module name decls methods) = "module " ++ show name ++ "\n" ++ (decls >>= ('\n' :) . show) ++ (methods >>= ('\n' :) . show)

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name datas methods) = Module name datas $ map fnMethod methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method name args rettype entry blocks) = Method name args rettype (fnBlock entry) $ map fnBlock blocks
    fnBlock :: Block -> Block
    fnBlock (Block name instr) = Block name $ fn instr

typeOfExpr :: Expr -> PrimitiveType
typeOfExpr (Literal (LitDouble _)) = TypeDouble
typeOfExpr (Literal (LitString _)) = TypeDataType (idFromString "[]")
typeOfExpr (Literal _) = TypeInt
typeOfExpr (Call (Global _ (FunctionType _ ret)) _) = ret
typeOfExpr (Eval _) = TypeAnyWHNF
typeOfExpr (Var v) = variableType v
typeOfExpr (Cast _ t) = t
typeOfExpr (Phi []) = error "typeOfExpr: Empty phi node. A phi expression should have at least 1 branch."
typeOfExpr (Phi (PhiBranch _ var : _)) = variableType var

variableType :: Variable -> PrimitiveType
variableType (VarLocal (Local _ t)) = t
variableType (VarGlobal (Global _ (FunctionType _ _))) = TypeFunction

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (Global x _)) = x
