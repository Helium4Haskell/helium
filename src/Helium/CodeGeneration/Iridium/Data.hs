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
import Lvm.Core.Module(Custom(..), DeclKind)
import Data.List(intercalate)

import Helium.CodeGeneration.Iridium.Type

type BlockName = Id

data Module = Module
  { moduleName :: !Id
  , moduleDependencies :: ![Id]
  , moduleCustoms :: ![Declaration CustomDeclaration]
  , moduleDataTypes :: ![Declaration DataType]
  , moduleAbstractMethods :: ![Declaration AbstractMethod]
  , moduleMethods :: ![Declaration Method]
  }

data DataType = DataType ![Declaration DataTypeConstructorDeclaration]

data DataTypeConstructorDeclaration = DataTypeConstructorDeclaration ![PrimitiveType]

data DataTypeConstructor = DataTypeConstructor { constructorDataType :: !Id, constructorName :: !Id, constructorFields :: ![PrimitiveType] }
  deriving (Eq, Ord)

getConstructors :: Declaration DataType -> [DataTypeConstructor]
getConstructors (Declaration dataName _ _ (DataType cons)) = map (\(Declaration conId _ _ (DataTypeConstructorDeclaration fields)) -> DataTypeConstructor dataName conId fields) cons

data Visibility = Exported | Private deriving (Eq, Ord)
data Declaration a = Declaration
  { declarationName :: !Id
  , declarationVisibilitiy :: !Visibility
  , declarationCustom :: ![Custom]
  , declarationValue :: !a
  }

data CustomDeclaration = CustomDeclaration !DeclKind

instance Functor Declaration where
  fmap f (Declaration name visibility customs a) = Declaration name visibility customs $ f a

-- Imported method, eg a method without a definition. The implementation is in some other file.
data AbstractMethod = AbstractMethod !FunctionType
  deriving (Eq, Ord)

data Method = Method ![Local] !PrimitiveType !Block ![Block]
  deriving (Eq, Ord)

-- TODO: Annotations on methods
data MethodAnnotation
  = MAThunk -- ^ This method can be put in a thunk
  deriving (Eq, Ord)

data Local = Local { localName :: !Id, localType :: !PrimitiveType }
  deriving (Eq, Ord)

data Global = Global Id FunctionType
  deriving (Eq, Ord)

data Variable
  = VarLocal !Local
  | VarGlobal !Global
  deriving (Eq, Ord)

data Block = Block BlockName Instruction
  deriving (Eq, Ord)

data Pattern
  = PatternCon !DataTypeConstructor
  | PatternLit !Literal
  deriving (Eq, Ord)

data Case
  = CaseConstructor [(DataTypeConstructor, BlockName)]
  | CaseLiteral [(Literal, BlockName)] BlockName
  deriving (Eq, Ord)

data Instruction
  = Let !Id !Expr !Instruction
  | LetAlloc ![Bind] !Instruction
  | Jump !BlockName
  -- * Asserts that the variable matches with the specified constructor. If they do not match, the behaviour is undefined.
  | Match !Variable !DataTypeConstructor ![Maybe Local] !Instruction -- TODO: For consistency, Maybe Local should be replaced with Maybe Id, as we also don't use Local for Let and LetAlloc
  | Case !Variable Case
  | Return !Variable
  deriving (Eq, Ord)

data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Variable] }
  deriving (Eq, Ord)

data BindTarget
  = BindTargetFunction !Variable
  | BindTargetConstructor !DataTypeConstructor
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
  = Literal !Literal
  | Call !Global ![Variable]
  | Eval !Variable
  | Var !Variable
  | Cast !Variable !PrimitiveType
  | Phi ![PhiBranch]
  deriving (Eq, Ord)

data PhiBranch = PhiBranch !BlockName !Variable
  deriving (Eq, Ord)

data Literal
  = LitInt !Int
  | LitDouble !Double
  | LitString !String
  deriving (Eq, Ord)

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name dependencies customs datas abstracts methods) = Module name dependencies customs datas abstracts $ map (fmap fnMethod) methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method args rettype entry blocks) = Method args rettype (fnBlock entry) $ map fnBlock blocks
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
variableType (VarGlobal (Global _ fntype)) = TypeGlobalFunction fntype

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (Global x _)) = x
