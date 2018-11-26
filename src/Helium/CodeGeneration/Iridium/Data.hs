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
import Lvm.Core.Module(Custom(..), DeclKind, Arity)
import Data.List(intercalate)

import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Primitive(findPrimitive, primReturn)

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
getConstructors (Declaration dataName _ _ _ (DataType cons)) = map (\(Declaration conId _ _ _ (DataTypeConstructorDeclaration fields)) -> DataTypeConstructor dataName conId fields) cons

data Visibility = Exported | Private deriving (Eq, Ord)
data Declaration a = Declaration
  { declarationName :: !Id
  , declarationVisibilitiy :: !Visibility
  , declarationModule :: Maybe Id
  , declarationCustom :: ![Custom]
  , declarationValue :: !a
  }

data CustomDeclaration = CustomDeclaration !DeclKind

instance Functor Declaration where
  fmap f (Declaration name visibility mod customs a) = Declaration name visibility mod customs $ f a

-- Imported method, eg a method without a definition. The implementation is in some other file.
data AbstractMethod = AbstractMethod !FunctionType ![Annotation]
  deriving (Eq, Ord)

data Method = Method ![Local] !PrimitiveType ![Annotation] !Block ![Block]
  deriving (Eq, Ord)

-- Annotations on methods
data Annotation
  -- * This method can be put in a thunk. An additional trampoline function is generated. We store a pointer to the trampoline in the thunk.
  = AnnotateTrampoline
  | AnnotateCallConvention !CallingConvention
  deriving (Eq, Ord)

data CallingConvention
  = CCC -- C calling convention
  | CCFast -- Fast calling convention of LLVM
  -- * Preserves most registers. Created for runtime functions that have a hot path that doesn't use many registers,
  -- and a cold path that might call other functions.
  | CCPreserveMost
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
  | CaseInt [(Int, BlockName)] BlockName
  deriving (Eq, Ord)

data Instruction
  = Let !Id !Expr !Instruction
  | LetAlloc ![Bind] !Instruction
  | Jump !BlockName
  -- * Asserts that the variable matches with the specified constructor. If they do not match, the behaviour is undefined.
  | Match !Variable !MatchTarget ![Maybe Id] !Instruction
  | Case !Variable Case
  | Return !Variable
  | Unreachable
  deriving (Eq, Ord)

data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Variable] }
  deriving (Eq, Ord)

data BindTarget
  = BindTargetFunction !Variable
  | BindTargetThunk !Variable
  | BindTargetConstructor !DataTypeConstructor
  | BindTargetTuple !Arity
  deriving (Eq, Ord)

data MatchTarget
  = MatchTargetConstructor !DataTypeConstructor
  | MatchTargetThunk !Arity
  | MatchTargetTuple !Arity
  deriving (Eq, Ord)

bindType :: Bind -> PrimitiveType
bindType (Bind _ (BindTargetConstructor (DataTypeConstructor dataName _ _)) _) = TypeDataType dataName
bindType (Bind _ (BindTargetTuple _) args) = TypeTuple $ length args
bindType (Bind _ (BindTargetFunction (VarGlobal (Global fn (FunctionType fnargs _)))) args)
  | length args >= length fnargs = TypeAnyThunk
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
  | PrimitiveExpr !Id ![Variable]
  deriving (Eq, Ord)

data PhiBranch = PhiBranch !BlockName !Variable
  deriving (Eq, Ord)

data Literal
  = LitInt !Int
  | LitDouble !Double
  | LitString !String
  deriving (Eq, Ord)

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
typeOfExpr (PrimitiveExpr name _) = primReturn $ findPrimitive name

variableType :: Variable -> PrimitiveType
variableType (VarLocal (Local _ t)) = t
variableType (VarGlobal (Global _ fntype)) = TypeGlobalFunction fntype

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (Global x _)) = x

callingConvention :: [Annotation] -> CallingConvention
callingConvention [] = CCFast -- Default
callingConvention (AnnotateCallConvention c : _) = c
callingConvention (_ : as) = callingConvention as

-- Checks whether this module has a declaration or definition for this function
declaresFunction :: Module -> Id -> Bool
declaresFunction (Module _ _ _ _ abstracts methods) name = any ((== name) . declarationName) abstracts || any ((== name) . declarationName) methods
