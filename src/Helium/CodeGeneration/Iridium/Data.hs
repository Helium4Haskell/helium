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

{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.Data
  (module Helium.CodeGeneration.Iridium.Data, module RegionSort, module RegionVar) where

import Lvm.Common.Id (Id, stringFromId, idFromString)
import Lvm.Common.IdMap (mapFromList, emptyMap)
import Lvm.Core.Module (Custom(..), DeclKind, Arity, Field)
import Lvm.Core.Type
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Data.Either (isLeft, isRight, lefts, rights)

import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Primitive (findPrimitive, primType)

import Helium.CodeGeneration.Iridium.Region.Sort as RegionSort
  ( RegionSort(..), pattern RegionSortUnit, showRegionSortWithVariables, showRegionSort)
import Helium.CodeGeneration.Iridium.Region.RegionVar as RegionVar
  ( RegionVar, RegionVars(..), pattern RegionLocal, pattern RegionGlobal, pattern RegionBottom, showRegionVarsWith )

import qualified Helium.CodeGeneration.Iridium.Region.Annotation as Region
import qualified Helium.CodeGeneration.Iridium.RegionSize.Annotation as RegionSize

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

dataTypeQuantors :: DataType -> [Quantor]
dataTypeQuantors (DataType []) = []
dataTypeQuantors (DataType (Declaration _ _ _ _ (DataTypeConstructorDeclaration tp _) : _)) = lefts args
  where
    FunctionType args _ = extractFunctionTypeNoSynonyms tp

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
data AbstractMethod = AbstractMethod !Type !RegionSort !FunctionType ![MethodAnnotation]
  deriving (Eq, Ord)

abstractFunctionType :: AbstractMethod -> FunctionType
abstractFunctionType (AbstractMethod _ _ tp _) = tp

abstractType :: AbstractMethod -> Type
abstractType method = typeFromFunctionType $ abstractFunctionType method

abstractSourceType :: AbstractMethod -> Type
abstractSourceType (AbstractMethod tp _ _ _) = tp

data Method = Method !Type !RegionVars ![Either Quantor Local] !Type !RegionVars ![MethodAnnotation] !Block ![Block]
  deriving (Eq, Ord)

methodFunctionType :: Method -> FunctionType
methodFunctionType (Method _ _ args returnType _ _ _ _) = FunctionType (map arg args) returnType
  where
    arg (Left quantor) = Left quantor
    arg (Right (Local _ tp)) = Right tp

methodType :: Method -> Type
methodType method = typeFromFunctionType $ methodFunctionType method

-- The additional regions of a method
methodAdditionRegions :: Method -> RegionVars
methodAdditionRegions (Method _ aRegs _ _ _ _ _ _) = aRegs

-- The original type of the function in Haskell, excluding strictness annotations
methodSourceType :: Method -> Type
methodSourceType (Method tp _ _ _ _ _ _ _) = tp

-- The number of non-type variable argument of the method.
methodArity :: Method -> Int
methodArity = length . filter isRight . methodArguments

-- The arguments of a method
methodArguments :: Method -> [Either Quantor Local]
methodArguments (Method _ _ args _ _ _ _ _) = args

-- Add an annotation to a method
methodAddAnnotation :: MethodAnnotation -> Method -> Method
methodAddAnnotation ann (Method a b c d e anns f g) = Method a b c d e (ann:anns) f g

-- Annotations on methods
data MethodAnnotation
  -- * This method can be put in a thunk. An additional trampoline function is generated. We store a pointer to the trampoline in the thunk.
  = MethodAnnotateTrampoline
  -- * Marks that this function uses a custom calling convention. When none is given, it is assumed to use CCFast
  | MethodAnnotateCallConvention !CallingConvention
  -- * The type of the method ends in RealWorld -> IORes, but in reality the fuction does not take RealWorld as an argument and only produces
  -- the value in the IORes object (not the 'next' real world). This is used to declare extern functions like putchar and getchar.
  -- We currently assume that the return type of the function is 'int'.
  -- Cannot be used in combination with 'MethodAnnotateTrampoline'.
  | MethodAnnotateImplicitIO
  | MethodAnnotateRegion !Region.Annotation
  | MethodAnnotateRegionSize !RegionSize.Annotation
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
  -- * Creates and allocates a new region. When annotated with a size bound, it may allocate the region
  -- on the stack.
  | NewRegion !RegionVar !(Maybe Int) !Instruction
  -- * Releases a region
  | ReleaseRegion !RegionVar !Instruction
  -- * Uncoditionally jumps to a block
  | Jump !BlockName
  -- * Asserts that the variable matches with the specified MatchTarget. Can be used to match on constructors,
  -- tuples and thunks. Pattern matching on thunks is not possible from Haskell code, but is used to write the
  -- runtime library. If the variable does not match with the specified MatchTarget, the behaviour is undefined.
  -- Extracts fields out of the object.
  | Match !Local !MatchTarget ![Type] ![Maybe Id] !Instruction
  -- * Conditionally jumps to a block, depending on the value of the variable. Can be used to distinguish
  -- different constructors of a data type, or on integers.
  | Case !Local Case
  -- * Returns a value from the function. The type of the variable should match with the return type of the
  -- containing method.
  | Return !Local
  -- * Denotes that the current location is unreachable. Can be used after a call to a diverging function like 'error'.
  -- The control flow or the argument should guarantee that this location is unreachable. In the case of calling 'error',
  -- the argument should be the returned value of 'error'.
  | Unreachable !(Maybe Local)
  deriving (Eq, Ord)

-- * A bind describes the construction of an object in a 'letalloc' instruction. It consists of the
-- variable to which the object is bound, the target and argument. A target represents what kind of object
-- is created.
data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Either Type Local], bindDestination :: !RegionVar }
  deriving (Eq, Ord)

-- * A bind can either construct a thunk, a constructor or a tuple. For thunks, we distinguish
-- primary thunks, which contain a function pointer, and secondary thunks, which point to other thunks.
data BindTarget
  -- * The object points at a function. The object is thus a primary thunk.
  = BindTargetFunction !GlobalFunction !RegionVars !BindThunkRegions -- additional region variables, and region variables for intermediate thunks and resulting value
  -- * The object points at another thunk and is thus a secondary thunk.
  | BindTargetThunk !Variable !BindThunkRegions
  -- * The bind represents a constructor invocation.
  | BindTargetConstructor !DataTypeConstructor
  -- * The bind represents the construction of a tuple.
  | BindTargetTuple !Arity
  deriving (Eq, Ord)

data BindThunkRegions = BindThunkRegions
  { bindThunkIntermediate :: !RegionVars
  , bindThunkValue :: !RegionVars
  } deriving (Eq, Ord)

-- * A 'match' instruction can pattern match on constructors, tuples.
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

matchFieldLocals :: MatchTarget -> [Type] -> [Maybe Id] -> [Maybe Local]
matchFieldLocals target instantiation fields = zipWith f fields $ matchFieldTypes target instantiation
  where
    f Nothing _ = Nothing
    f (Just name) tp = Just $ Local name tp

typeApplyArguments :: TypeEnvironment -> Type -> [Either Type Local] -> Type
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
bindType env (Bind _ (BindTargetConstructor cons) args _) = typeToStrict $ typeApplyArguments env (constructorType cons) args
-- For a tuple, we get a value in WHNF of the given tuple size.
bindType env (Bind _ (BindTargetTuple arity) args _) = typeToStrict $ foldl ap (TCon $ TConTuple arity) args
  where
    ap t1 (Right _) = t1
    ap t1 (Left t2) = t1 `TAp` t2
-- When binding to a global function, we get a thunk in WHNF (TypeFunction) if not enough arguments were passed,
-- or TypeAnyThunk (not in WHNF) otherwise.
bindType env (Bind _ (BindTargetFunction (GlobalFunction fn arity fntype) _ _) args _)
  | arity > valueArgCount = typeToStrict $ tp
  | otherwise = tp
  where
    tp = typeRemoveArgumentStrictness $ typeApplyArguments env fntype args
    valueArgCount = length $ filter isRight args
bindType env (Bind _ (BindTargetThunk fn _) args _) = typeApplyArguments env (variableType fn) args

bindLocal :: TypeEnvironment -> Bind -> Local
bindLocal env b@(Bind var _ _ _) = Local var $ bindType env b

-- * Expressions are used to bind values to variables in 'let' instructions.
-- Those binds cannot be recursive.
data Expr
  -- A literal value. Note that strings are allocated, integers and floats not.
  = Literal !Literal
  -- Calls a function. The number of arguments should be equal to the number of parameters of the specified function.
  -- The call provides additional region variables and regions used for the return value.
  | Call !GlobalFunction !RegionVars ![Either Type Local] !RegionVars
  | Instantiate !Local ![Type]
  -- Evaluates a value to WHNF or returns the value if it is already in WHNF.
  | Eval !Variable
  -- Gets the value of a variable. Does not evaluate the variable.
  | Var !Variable
  -- Casts a variable to a (possibly) different type.
  | Cast !Local !Type
  -- Casts type `!a` to `a`
  | CastThunk !Local
  -- Represents a phi node in the control flow of the method. Gets a value, based on the previous block.
  | Phi ![PhiBranch]
  -- Calls a primitive instruction, like integer addition. The number of arguments should be equal to the number of parameters
  -- that the primitive expects.
  | PrimitiveExpr !Id ![Either Type Local]
  -- Denotes an undefined value, not the Haskell function 'undefined'. This expression does not throw, but just has some unknown value.
  -- This can be used for a value which is not used.
  | Undefined !Type
  -- `%c = seq %a %b` marks a dependency between variables %a and %b. Assigns %b to %c and ignores the value of %a. 
  -- Prevents that variable %a is removed by dead code removal. Can be used to compile the Haskell functions `seq` and `pseq`.
  | Seq !Local !Local
  deriving (Eq, Ord)

data PhiBranch = PhiBranch { phiBlock :: !BlockName, phiVariable :: !Local }
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
typeOfExpr env (Call (GlobalFunction _ _ t) _ args _) = typeToStrict $ typeApplyArguments env t args
typeOfExpr env (Instantiate v args) = typeNormalizeHead env $ typeApplyList (localType v) args
typeOfExpr _ (Eval v) = typeToStrict $ variableType v
typeOfExpr _ (Var v) = variableType v
typeOfExpr _ (Cast _ t) = t
typeOfExpr _ (CastThunk var) = typeNotStrict $ localType var
typeOfExpr _ (Phi []) = error "typeOfExpr: Empty phi node. A phi expression should have at least 1 branch."
typeOfExpr _ (Phi (PhiBranch _ var : _)) = localType var
typeOfExpr env (PrimitiveExpr name args) = typeApplyArguments env (typeFromFunctionType $ primType $ findPrimitive name) args
typeOfExpr _ (Undefined t) = t
typeOfExpr _ (Seq _ v) = localType v

dependenciesOfExpr :: Expr -> [Variable]
dependenciesOfExpr (Literal _) = []
dependenciesOfExpr (Call _ _ args _) = [VarLocal arg | Right arg <- args]
dependenciesOfExpr (Instantiate var _) = [VarLocal var]
dependenciesOfExpr (Eval var) = [var]
dependenciesOfExpr (Var var) = [var]
dependenciesOfExpr (Cast var _) = [VarLocal var]
dependenciesOfExpr (CastThunk var) = [VarLocal var]
dependenciesOfExpr (Phi branches) = map (VarLocal . phiVariable) branches
dependenciesOfExpr (PrimitiveExpr _ args) = [VarLocal arg | Right arg <- args]
dependenciesOfExpr (Undefined _) = []
dependenciesOfExpr (Seq v1 v2) = [VarLocal v1, VarLocal v2]

variableType :: Variable -> Type
variableType (VarLocal (Local _ t)) = t
variableType (VarGlobal (GlobalVariable _ t)) = t

variableName :: Variable -> Id
variableName (VarLocal (Local x _)) = x
variableName (VarGlobal (GlobalVariable x _)) = x

callingConvention :: [MethodAnnotation] -> CallingConvention
callingConvention [] = CCFast -- Default
callingConvention (MethodAnnotateCallConvention c : _) = c
callingConvention (_ : as) = callingConvention as

-- Checks whether this module has a declaration or definition for this function
declaresFunction :: Module -> Id -> Bool
declaresFunction (Module _ _ _ _ _ abstracts methods) name = any ((== name) . declarationName) abstracts || any ((== name) . declarationName) methods

envWithSynonyms :: Module -> TypeEnvironment
envWithSynonyms (Module _ _ _ _ synonyms _ _) = TypeEnvironment (mapFromList synonymsList) emptyMap emptyMap
  where
    synonymsList = map (\(Declaration name _ _ _ (TypeSynonym _ tp)) -> (name, tp)) synonyms

methodLocals :: Bool -> TypeEnvironment -> Method -> [Local]
methodLocals withArguments env (Method _ _ args _ _ _ block blocks) = foldr blockLocals (blockLocals block argLocals) blocks
  where
    argLocals
      | withArguments = rights args
      | otherwise = []

    blockLocals :: Block -> [Local] -> [Local]
    blockLocals (Block _ instruction) = instructionLocals instruction

    instructionLocals :: Instruction -> [Local] -> [Local]
    instructionLocals (Let name expr next) accum =
      instructionLocals next $ Local name (typeOfExpr env expr) : accum
    instructionLocals (LetAlloc binds next) accum =
      instructionLocals next $ map (bindLocal env) binds ++ accum
    instructionLocals (NewRegion _ _ next) accum = instructionLocals next accum
    instructionLocals (ReleaseRegion _ next) accum = instructionLocals next accum
    instructionLocals (Match _ target instantiation fields next) accum =
      instructionLocals next $ catMaybes (matchFieldLocals target instantiation fields) ++ accum
    instructionLocals _ accum = accum

methodBinds :: Method -> [Bind]
methodBinds (Method _ _ _ _ _ _ block blocks) = (block : blocks) >>= travBlock
  where
    travBlock (Block _ instr) = travInstr instr
    travInstr (Let _ _ next) = travInstr next
    travInstr (LetAlloc binds next) = binds ++ travInstr next
    travInstr (NewRegion _ _ next) = travInstr next
    travInstr (ReleaseRegion _ next) = travInstr next
    travInstr (Jump _) = []
    travInstr (Match _ _ _ _ next) = travInstr next
    travInstr (Case _ _) = []
    travInstr (Return _) = []
    travInstr (Unreachable _) = []

methodExpressions :: Method -> [(Id, Expr)]
methodExpressions (Method _ _ _ _ _ _ block blocks) = (block : blocks) >>= travBlock
  where
    travBlock (Block _ instr) = travInstr instr
    travInstr (Let name expr next) = (name, expr) : travInstr next
    travInstr (LetAlloc _ next) = travInstr next
    travInstr (NewRegion _ _ next) = travInstr next
    travInstr (ReleaseRegion _ next) = travInstr next
    travInstr (Jump _) = []
    travInstr (Match _ _ _ _ next) = travInstr next
    travInstr (Case _ _) = []
    travInstr (Return _) = []
    travInstr (Unreachable _) = []

methodCalls :: Method -> [(Id, GlobalFunction, [Either Type Local])]
methodCalls method = [(name, fn, args) | (name, Call fn _ args _) <- methodExpressions method]
