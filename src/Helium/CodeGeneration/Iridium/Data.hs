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
  -- * Marks that this function uses a custom calling convention. When none is given, it is assumed to use CCFast
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

data Global
  = GlobalFunction !Id !FunctionType
  | GlobalVariable !Id !PrimitiveType
  deriving (Eq, Ord)

data Variable
  = VarLocal !Local
  | VarGlobal !Global
  deriving (Eq, Ord)

data Block = Block BlockName Instruction
  deriving (Eq, Ord)

-- * The branches of a 'case' instuction.
data Case
  -- * Each branch is marked with a constructor. All constructors should be of the same data type.
  --  It is not required that all constructors of the data type should be present. However,
  -- the behavior is undefined if no constructor matches.
  = CaseConstructor [(DataTypeConstructor, BlockName)]
  -- * For a case instruction on ints, the branches are marked with integers and there is a default branch,
  -- which is executed if the given numbers do not match.
  | CaseInt [(Int, BlockName)] BlockName
  deriving (Eq, Ord)

data Instruction
  -- * Computes an expression and assigns the value to the given variable name.
  = Let !Id !Expr !Instruction
  -- * Allocates thunks or constructors. Those binds may be recursive.
  | LetAlloc ![Bind] !Instruction
  -- * Uncoditionally jumps to a block
  | Jump !BlockName
  -- * Asserts that the variable matches with the specified MatchTarget. Can be used to match on constructors,
  -- tuples and thunks. Pattern matching on thunks is not possible from Haskell code, but is used to write the
  -- runtime library. If the variable does not match with the specified MatchTarget, the behaviour is undefined.
  -- Extracts fields out of the object.
  | Match !Variable !MatchTarget ![Maybe Id] !Instruction
  -- * Conditionally jumps to a block, depending on the value of the variable. Can be used to distinguish
  -- different constructors of a data type, or on integers.
  | Case !Variable Case
  -- * Returns a value from the function. The type of the variable should match with the return type of the
  -- containing method.
  | Return !Variable
  -- * Denotes that the current location is unreachable. Can be used after a call to a diverging function like 'error'.
  -- No semantics are defined for this instruction.
  | Unreachable
  deriving (Eq, Ord)

-- * A bind describes the construction of an object in a 'letalloc' instruction. It consists of the
-- variable to which the object is bound, the target and argument. A target represents what kind of object
-- is created.
data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Variable] }
  deriving (Eq, Ord)

-- * A bind can either construct a thunk, a constructor or a tuple. For thunks, we distinguish
-- primary thunks, which contain a function pointer, and secondary thunks, which point to other thunks.
data BindTarget
  -- * The object points at a function. The object is thus a primary thunk.
  = BindTargetFunction !Variable
  -- * The object points at another thunk and is thus a secondary thunk.
  | BindTargetThunk !Variable
  -- * The bind represents a constructor invocation.
  | BindTargetConstructor !DataTypeConstructor
  -- * The bind represents the construction of a tuple.
  | BindTargetTuple !Arity
  deriving (Eq, Ord)

-- * A 'match' instruction can pattern match on constructors, tuples or thunks. The latter
-- is not possible from Haskell code and is only used to write the runtime library.
data MatchTarget
  -- * Match on a constructor.
  = MatchTargetConstructor !DataTypeConstructor
  -- * Match on a thunk (either primary or secondary) with a given number of arguments.
  | MatchTargetThunk !Arity
  -- * Match on a tuple with a given number of fields.
  | MatchTargetTuple !Arity
  deriving (Eq, Ord)

-- * Find the type of the constructed object in a Bind
bindType :: Bind -> PrimitiveType
-- In case of a constructor application, we get a value in WHNF of the related data type.
bindType (Bind _ (BindTargetConstructor (DataTypeConstructor dataName _ _)) _) = TypeDataType dataName
-- For a tuple, we get a value in WHNF of the given tuple size.
bindType (Bind _ (BindTargetTuple _) args) = TypeTuple $ length args
-- When binding to a global function, we get a thunk in WHNF (TypeFunction) if not enough arguments were passed,
-- or TypeAnyThunk (not in WHNF) otherwise.
bindType (Bind _ (BindTargetFunction (VarGlobal (GlobalFunction fn (FunctionType fnargs _)))) args)
  | length args >= length fnargs = TypeAnyThunk
  | otherwise = TypeFunction
bindType _ = TypeAnyThunk

bindLocal :: Bind -> Local
bindLocal b@(Bind var _ _) = Local var $ bindType b

bindTargetArgumentTypes :: BindTarget -> [PrimitiveType]
bindTargetArgumentTypes (BindTargetConstructor (DataTypeConstructor _ _ args)) = args
bindTargetArgumentTypes (BindTargetTuple arity) = replicate arity TypeAny
bindTargetArgumentTypes (BindTargetFunction (VarGlobal (GlobalFunction _ (FunctionType fnargs _)))) = fnargs
bindTargetArgumentTypes _ = repeat TypeAny

-- * Expressions are used to bind values to variables in 'let' instructions.
-- Those binds cannot be recursive.
data Expr
  -- A literal value. Note that strings are allocated, integers and floats not.
  = Literal !Literal
  -- Calls a function. The number of arguments should be equal to the number of parameters of the specified function.
  | Call !Global ![Variable]
  -- Evaluates a value to WHNF or returns the value if it is already in WHNF.
  | Eval !Variable
  -- Gets the value of a variable. Does not evaluate the variable.
  | Var !Variable
  -- Casts a variable to a (possibly) different type.
  | Cast !Variable !PrimitiveType
  -- Represents a phi node in the control flow of the method. Gets a value, based on the previous block.
  | Phi ![PhiBranch]
  -- Calls a primitive instruction, like integer addition. The number of arguments should be equal to the number of parameters
  -- that the primitive expects.
  | PrimitiveExpr !Id ![Variable]
  -- Denotes an undefined value, not the Haskell function 'undefined'. This expression does not throw, but just has some unknown value.
  -- This can be used for a value which is not used.
  | Undefined !PrimitiveType
  -- `%c = seq %a %b` marks a dependency between variables %a and %b. Assigns %b to %c and ignores the value of %a. 
  -- Prevents that variable %a is removed by dead code removal. Can be used to compile the Haskell functions `seq` and `pseq`.
  | Seq !Variable !Variable
  deriving (Eq, Ord)

data PhiBranch = PhiBranch { phiBlock :: !BlockName, phiVariable :: !Variable }
  deriving (Eq, Ord)

data Literal
  = LitInt !Int
  | LitFloat !FloatPrecision !Double
  | LitString !String
  deriving (Eq, Ord)

typeOfExpr :: Expr -> PrimitiveType
typeOfExpr (Literal (LitFloat precision _)) = TypeFloat precision
typeOfExpr (Literal (LitString _)) = TypeDataType (idFromString "[]")
typeOfExpr (Literal _) = TypeInt
typeOfExpr (Call (GlobalFunction _ (FunctionType _ ret)) _) = ret
typeOfExpr (Eval _) = TypeAnyWHNF
typeOfExpr (Var v) = variableType v
typeOfExpr (Cast _ t) = t
typeOfExpr (Phi []) = error "typeOfExpr: Empty phi node. A phi expression should have at least 1 branch."
typeOfExpr (Phi (PhiBranch _ var : _)) = variableType var
typeOfExpr (PrimitiveExpr name _) = primReturn $ findPrimitive name
typeOfExpr (Undefined t) = t
typeOfExpr (Seq _ v) = variableType v

dependenciesOfExpr :: Expr -> [Variable]
dependenciesOfExpr (Literal _) = []
dependenciesOfExpr (Call g args) = VarGlobal g : args
dependenciesOfExpr (Eval var) = [var]
dependenciesOfExpr (Var var) = [var]
dependenciesOfExpr (Cast var _) = [var]
dependenciesOfExpr (Phi branches) = map (phiVariable) branches
dependenciesOfExpr (PrimitiveExpr _ args) = args
dependenciesOfExpr (Undefined _) = []
dependenciesOfExpr (Seq v1 v2) = [v1, v2]

variableType :: Variable -> PrimitiveType
variableType (VarLocal (Local _ t)) = t
variableType (VarGlobal (GlobalFunction _ fntype)) = TypeGlobalFunction fntype
variableType (VarGlobal (GlobalVariable _ t)) = t

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (GlobalFunction x _)) = x
variableName (VarGlobal (GlobalVariable x _)) = x

callingConvention :: [Annotation] -> CallingConvention
callingConvention [] = CCFast -- Default
callingConvention (AnnotateCallConvention c : _) = c
callingConvention (_ : as) = callingConvention as

-- Checks whether this module has a declaration or definition for this function
declaresFunction :: Module -> Id -> Bool
declaresFunction (Module _ _ _ _ abstracts methods) name = any ((== name) . declarationName) abstracts || any ((== name) . declarationName) methods
