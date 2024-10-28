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

import Helium.Lvm.Common.Id(Id, stringFromId, idFromString)
import Helium.Lvm.Common.IdMap(mapFromList, emptyMap)
import Helium.Lvm.Core.Module(Custom(..), DeclKind, Arity, Field)
import Helium.Lvm.Core.Type
import Data.List(intercalate)
import Data.Either (isLeft, isRight)

import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Primitive(findPrimitive, primType)

type BlockName = Id

data Module = Module
  { moduleName :: !Id
  , moduleDependencies :: ![Id]
  , moduleCustoms :: ![Declaration CustomDeclaration]
  , moduleDataTypes :: ![Declaration DataType]
  , moduleTypeSynonyms :: ![Declaration TypeSynonym]
  , moduleAbstractMethods :: ![Declaration AbstractMethod]
  , moduleMethods :: ![Declaration Method]
  }

data DataType = DataType ![Declaration DataTypeConstructorDeclaration]

data DataTypeConstructorDeclaration = DataTypeConstructorDeclaration !Type ![Field]

data DataTypeConstructor = DataTypeConstructor { constructorName :: !Id, constructorType :: !Type }
  deriving (Eq, Ord)

constructorDataType :: DataTypeConstructor -> Id
constructorDataType cons = findName $ findReturn $ constructorType cons
  where
    findReturn :: Type -> Type
    findReturn (TForall _ _ t) = findReturn t
    findReturn (TAp (TAp (TCon TConFun) _) t) = findReturn t
    findReturn t = t
    findName :: Type -> Id
    findName (TAp t _) = findName t
    findName (TCon (TConDataType name)) = name
    findName (TCon (TConTypeClassDictionary name)) = idFromString $ ("Dict$" ++ stringFromId name)
    findName t = error ("constructorDataType: Could not find data type name in type " ++ showType [] t)

getConstructors :: Declaration DataType -> [DataTypeConstructor]
getConstructors (Declaration dataName _ _ _ (DataType cons)) = map (\(Declaration conId _ _ _ (DataTypeConstructorDeclaration tp _)) -> DataTypeConstructor conId tp) cons

data Visibility = ExportedAs !Id | Private deriving (Eq, Ord)

data Declaration a = Declaration
  { declarationName :: !Id
  , declarationVisibility :: !Visibility
  , declarationModule :: Maybe Id
  , declarationCustom :: ![Custom]
  , declarationValue :: !a
  }

data CustomDeclaration = CustomDeclaration !DeclKind

instance Functor Declaration where
  fmap f (Declaration name visibility mod customs a) = Declaration name visibility mod customs $ f a

-- Imported method, eg a method without a definition. The implementation is in some other file.
data AbstractMethod = AbstractMethod !Type !FunctionType ![Annotation]
  deriving (Eq, Ord)

abstractFunctionType :: AbstractMethod -> FunctionType
abstractFunctionType (AbstractMethod _ tp _) = tp

abstractType :: AbstractMethod -> Type
abstractType method = typeFromFunctionType $ abstractFunctionType method

abstractSourceType :: AbstractMethod -> Type
abstractSourceType (AbstractMethod tp _ _) = tp

data Method = Method !Type ![Either Quantor Local] !Type ![Annotation] !Block ![Block]
  deriving (Eq, Ord)

methodFunctionType :: Method -> FunctionType
methodFunctionType (Method _ args returnType _ _ _) = FunctionType (map arg args) returnType
  where
    arg (Left quantor) = Left quantor
    arg (Right (Local _ tp)) = Right tp

methodType :: Method -> Type
methodType method = typeFromFunctionType $ methodFunctionType method

-- The original type of the function in Haskell, excluding strictness annotations
methodSourceType :: Method -> Type
methodSourceType (Method tp _ _ _ _ _) = tp

methodArity :: Method -> Int
methodArity (Method _ args _ _ _ _) = length $ filter isRight args

-- Annotations on methods
data Annotation
  -- * This method can be put in a thunk. An additional trampoline function is generated. We store a pointer to the trampoline in the thunk.
  = AnnotateTrampoline
  -- * Marks that this function uses a custom calling convention. When none is given, it is assumed to use CCFast
  | AnnotateCallConvention !CallingConvention
  -- * The type of the method ends in RealWorld -> IORes, but in reality the fuction does not take RealWorld as an argument and only produces
  -- the value in the IORes object (not the 'next' real world). This is used to declare extern functions like putchar and getchar.
  -- We currently assume that the return type of the function is 'int'.
  -- Cannot be used in combination with 'AnnotateTrampoline'.
  | AnnotateImplicitIO
  deriving (Eq, Ord)

data CallingConvention
  = CCC -- C calling convention
  | CCFast -- Fast calling convention of LLVM
  -- * Preserves most registers. Created for runtime functions that have a hot path that doesn't use many registers,
  -- and a cold path that might call other functions.
  | CCPreserveMost
  deriving (Eq, Ord)

data TypeSynonym = TypeSynonym !TypeSynonymCoercions !Type

data TypeSynonymCoercions
  = TypeSynonymAlias   -- Implicit coercions in Haskell and Iridium
  | TypeSynonymNewtype !Visibility !Visibility -- Explicit coercions in Haskell with the specified constructor name and optionally destructor name, implicit in Iridium

newtypeConstructorType :: Declaration TypeSynonym -> (Type, Type)
newtypeConstructorType (Declaration name _ _ _ (TypeSynonym _ tp))
  = ( addForalls tp $ typeFunction [TStrict tpRight] tpLeft -- Constructor type
    , addForalls tp $ typeFunction [TStrict tpLeft] tpRight -- Destructur type
    )
  where
    (forallCount, tpRight) = skipForalls 0 tp
    tpLeft = foldl (\t v -> TAp t (TVar v)) (TCon $ TConDataType name) [forallCount - 1, forallCount - 2 .. 0]

    skipForalls :: Int -> Type -> (Int, Type)
    skipForalls count (TForall _ _ t) = skipForalls (count + 1) t
    skipForalls count t = (count, t)

    addForalls :: Type -> Type -> Type
    addForalls (TForall q k t1) t2 = TForall q k $ addForalls t1 t2
    addForalls _ t2 = t2

data Local = Local { localName :: !Id, localType :: !Type }
  deriving (Eq, Ord)

data Global
  = GlobalVariable !Id !Type
  deriving (Eq, Ord)

data GlobalFunction = GlobalFunction
  { globalFunctionName :: !Id
  , globalFunctionArity :: !Arity
  , globalFunctionType :: !Type
  }
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
  | Match !Variable !MatchTarget ![Type] ![Maybe Id] !Instruction
  -- * Conditionally jumps to a block, depending on the value of the variable. Can be used to distinguish
  -- different constructors of a data type, or on integers.
  | Case !Variable Case
  -- * Returns a value from the function. The type of the variable should match with the return type of the
  -- containing method.
  | Return !Variable
  -- * Denotes that the current location is unreachable. Can be used after a call to a diverging function like 'error'.
  -- The control flow or the argument should guarantee that this location is unreachable. In the case of calling 'error',
  -- the argument should be the returned value of 'error'.
  | Unreachable !(Maybe Variable)
  deriving (Eq, Ord)

-- * A bind describes the construction of an object in a 'letalloc' instruction. It consists of the
-- variable to which the object is bound, the target and argument. A target represents what kind of object
-- is created.
data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Either Type Variable] }
  deriving (Eq, Ord)

-- * A bind can either construct a thunk, a constructor or a tuple. For thunks, we distinguish
-- primary thunks, which contain a function pointer, and secondary thunks, which point to other thunks.
data BindTarget
  -- * The object points at a function. The object is thus a primary thunk.
  = BindTargetFunction !GlobalFunction
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
  -- * Match on a tuple with a given number of fields.
  | MatchTargetTuple !Arity
  deriving (Eq, Ord)

matchArgumentType :: MatchTarget -> [Type] -> Type
matchArgumentType (MatchTargetConstructor (DataTypeConstructor _ tp)) instantiation = typeToStrict ret
  where
    FunctionType _ ret = extractFunctionTypeNoSynonyms $ typeApplyList tp instantiation
matchArgumentType (MatchTargetTuple arity) instantiation = typeToStrict $ foldl TAp (TCon $ TConTuple arity) instantiation

matchFieldTypes :: MatchTarget -> [Type] -> [Type]
matchFieldTypes (MatchTargetConstructor (DataTypeConstructor _ tp)) instantiation =
  [ arg | Right arg <- args ]
  where
    FunctionType args _ = extractFunctionTypeNoSynonyms $ typeApplyList tp instantiation
matchFieldTypes (MatchTargetTuple _) instantiation = instantiation

typeApplyArguments :: TypeEnvironment -> Type -> [Either Type Variable] -> Type
typeApplyArguments env t1@(TForall _ _ _) (Left t2 : args) = typeApplyArguments env t1' args
  where
    t1' = typeApply t1 t2
typeApplyArguments env (TAp (TAp (TCon TConFun) _) tReturn) (Right _ : args) = typeApplyArguments env tReturn args
typeApplyArguments env tp [] = tp
typeApplyArguments env tp args = case tp' of
  TForall _ _ _
    | isLeft $ head args -> typeApplyArguments env tp' args
  TAp (TAp (TCon TConFun) _) _
    | isRight $ head args -> typeApplyArguments env tp' args
  _
    | isRight $ head args -> error ("typeApplyArguments: expected a function type, got " ++ showType [] tp')
    | otherwise -> error ("typeApplyArguments: expected a forall type, got " ++ showType [] tp')
  where
    tp' = case typeNormalizeHead env tp of
      TStrict tp' -> tp'
      tp' -> tp'

-- * Find the type of the constructed object in a Bind
bindType :: TypeEnvironment -> Bind -> Type
-- In case of a constructor application, we get a value in WHNF of the related data type.
bindType env (Bind _ (BindTargetConstructor cons) args) = typeToStrict $ typeApplyArguments env (constructorType cons) args
-- For a tuple, we get a value in WHNF of the given tuple size.
bindType env (Bind _ (BindTargetTuple arity) args) = typeToStrict $ foldl ap (TCon $ TConTuple arity) args
  where
    ap t1 (Right _) = t1
    ap t1 (Left t2) = t1 `TAp` t2
-- When binding to a global function, we get a thunk in WHNF (TypeFunction) if not enough arguments were passed,
-- or TypeAnyThunk (not in WHNF) otherwise.
bindType env (Bind _ (BindTargetFunction (GlobalFunction fn arity fntype)) args)
  | arity > valueArgCount = typeToStrict $ tp
  | otherwise = tp
  where
    tp = typeRemoveArgumentStrictness $ typeApplyArguments env fntype args
    valueArgCount = length $ filter isRight args
bindType env (Bind _ (BindTargetThunk fn) args) = typeApplyArguments env (variableType fn) args

bindLocal :: TypeEnvironment -> Bind -> Local
bindLocal env b@(Bind var _ _) = Local var $ bindType env b

-- * Expressions are used to bind values to variables in 'let' instructions.
-- Those binds cannot be recursive.
data Expr
  -- A literal value. Note that strings are allocated, integers and floats not.
  = Literal !Literal
  -- Calls a function. The number of arguments should be equal to the number of parameters of the specified function.
  | Call !GlobalFunction ![Either Type Variable]
  | Instantiate !Variable ![Type]
  -- Evaluates a value to WHNF or returns the value if it is already in WHNF.
  | Eval !Variable
  -- Gets the value of a variable. Does not evaluate the variable.
  | Var !Variable
  -- Casts a variable to a (possibly) different type.
  | Cast !Variable !Type
  -- Casts type `!a` to `a`
  | CastThunk !Variable
  -- Represents a phi node in the control flow of the method. Gets a value, based on the previous block.
  | Phi ![PhiBranch]
  -- Calls a primitive instruction, like integer addition. The number of arguments should be equal to the number of parameters
  -- that the primitive expects.
  | PrimitiveExpr !Id ![Either Type Variable]
  -- Denotes an undefined value, not the Haskell function 'undefined'. This expression does not throw, but just has some unknown value.
  -- This can be used for a value which is not used.
  | Undefined !Type
  -- `%c = seq %a %b` marks a dependency between variables %a and %b. Assigns %b to %c and ignores the value of %a. 
  -- Prevents that variable %a is removed by dead code removal. Can be used to compile the Haskell functions `seq` and `pseq`.
  | Seq !Variable !Variable
  deriving (Eq, Ord)

data PhiBranch = PhiBranch { phiBlock :: !BlockName, phiVariable :: !Variable }
  deriving (Eq, Ord)

data Literal
  = LitInt !IntType !Int
  | LitFloat !FloatPrecision !Double
  | LitString !String
  deriving (Eq, Ord)

typeOfExpr :: TypeEnvironment -> Expr -> Type
typeOfExpr _ (Literal (LitFloat precision _)) = TStrict $ TCon $ TConDataType $ idFromString "Float" -- TODO: Precision
typeOfExpr _ (Literal (LitString _)) = TStrict $ TAp (TCon $ TConDataType $ idFromString "[]") $ TCon $ TConDataType $ idFromString "Char"
typeOfExpr _ (Literal (LitInt tp _)) = TStrict $ TCon $ TConDataType $ idFromString $ show tp
typeOfExpr env (Call (GlobalFunction _ _ t) args) = typeToStrict $ typeApplyArguments env t args
typeOfExpr env (Instantiate v args) = typeNormalizeHead env $ typeApplyList (variableType v) args
typeOfExpr _ (Eval v) = typeToStrict $ variableType v
typeOfExpr _ (Var v) = variableType v
typeOfExpr _ (Cast _ t) = t
typeOfExpr _ (CastThunk var) = typeNotStrict $ variableType var
typeOfExpr _ (Phi []) = error "typeOfExpr: Empty phi node. A phi expression should have at least 1 branch."
typeOfExpr _ (Phi (PhiBranch _ var : _)) = variableType var
typeOfExpr env (PrimitiveExpr name args) = typeApplyArguments env (typeFromFunctionType $ primType $ findPrimitive name) args
typeOfExpr _ (Undefined t) = t
typeOfExpr _ (Seq _ v) = variableType v

dependenciesOfExpr :: Expr -> [Variable]
dependenciesOfExpr (Literal _) = []
dependenciesOfExpr (Call g args) = [arg | Right arg <- args]
dependenciesOfExpr (Instantiate var _) = [var]
dependenciesOfExpr (Eval var) = [var]
dependenciesOfExpr (Var var) = [var]
dependenciesOfExpr (Cast var _) = [var]
dependenciesOfExpr (CastThunk var) = [var]
dependenciesOfExpr (Phi branches) = map phiVariable branches
dependenciesOfExpr (PrimitiveExpr _ args) = [arg | Right arg <- args]
dependenciesOfExpr (Undefined _) = []
dependenciesOfExpr (Seq v1 v2) = [v1, v2]

variableType :: Variable -> Type
variableType (VarLocal (Local _ t)) = t
variableType (VarGlobal (GlobalVariable _ t)) = t

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (GlobalVariable x _)) = x

callingConvention :: [Annotation] -> CallingConvention
callingConvention [] = CCFast -- Default
callingConvention (AnnotateCallConvention c : _) = c
callingConvention (_ : as) = callingConvention as

-- Checks whether this module has a declaration or definition for this function
declaresFunction :: Module -> Id -> Bool
declaresFunction (Module _ _ _ _ _ abstracts methods) name = any ((== name) . declarationName) abstracts || any ((== name) . declarationName) methods

envWithSynonyms :: Module -> TypeEnvironment
envWithSynonyms (Module _ _ _ _ synonyms _ _) = TypeEnvironment (mapFromList synonymsList) emptyMap emptyMap
  where
    synonymsList = map (\(Declaration name _ _ _ (TypeSynonym _ tp)) -> (name, tp)) synonyms
