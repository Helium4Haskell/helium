{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileBlock (compileBlock) where

import Data.String(fromString)
import Data.Word(Word32)
import Data.Either

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.CompileBind
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.CompileConstructor(compileExtractFields)
import Helium.CodeGeneration.LLVM.Struct(tagValue, tupleStruct)
import Helium.CodeGeneration.LLVM.CompileStruct
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins

import Helium.Lvm.Common.Id(Id, NameSupply, splitNameSupply, splitNameSupplies, mapWithSupply, freshId, idFromString)
import Helium.Lvm.Common.IdMap(findMap)
import qualified Helium.Lvm.Core.Type as Core

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.Primitive as Iridium
import LLVM.AST as AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Constant (Constant(Int, Float, Array, Undef, GlobalReference))
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate
import qualified LLVM.AST.Float as Float

import Data.List (maximumBy, group, sort, partition)
import Data.Function (on)

data Partial = Partial [Named Instruction] (Named Terminator) [BasicBlock]

infixr 3 +>
(+>) :: [Named Instruction] -> Partial -> Partial
instrs1 +> (Partial instrs2 terminator blocks) = Partial (instrs1 ++ instrs2) terminator blocks

compileBlock :: Env -> NameSupply -> Iridium.Block -> [BasicBlock]
compileBlock env supply (Iridium.Block name instruction) = BasicBlock (toName name) instrs term : blocks
  where
    Partial instrs term blocks = compileInstruction env supply instruction

compileInstruction :: Env -> NameSupply -> Iridium.Instruction -> Partial
compileInstruction env supply (Iridium.Let name expr next) = compileExpression env supply1 expr name +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.LetAlloc binds next) =
  compileBinds env supply1 binds
  +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.Jump to) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it actually matches.
compileInstruction env supply (Iridium.Match var _ _ [] next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var target _ args next)
  = [ addressName := AST.BitCast (toOperand env var) (pointer t) []
    ]
    +> compileExtractFields env supply'' address struct args
    +> compileInstruction env supply''' next
  where
    t = structType env struct
    (addressName, supply') = freshName supply
    address = LocalReference (pointer t) addressName
    (supply'', supply''') = splitNameSupply supply'
    LayoutPointer struct = case target of
      Iridium.MatchTargetConstructor (Iridium.DataTypeConstructor conId _) -> findMap conId (envConstructors env)
      Iridium.MatchTargetTuple arity -> LayoutPointer $ tupleStruct arity
compileInstruction env supply (Iridium.Case var (Iridium.CaseConstructor alts))
  -- All constructors are pointers
  | null inlines =
    let (instr, terminator) = compileCaseConstructorPointer env supply var pointers
    in Partial instr terminator []

  -- All constructors are inline
  | null pointers =
    -- Extract the most frequent branch
    let
      (defaultBranch, alts'') = caseExtractMostFrequentBranch inlines
      (instr, terminator) = compileCaseConstructorInline env supply var alts'' defaultBranch
    in
      Partial instr terminator []

  -- Only one pointer value
  | length pointers == 1 =
    let
      [CaseAlt _ _ pointerBranch] = pointers
      (instr, terminator) = compileCaseConstructorInline env supply var inlines pointerBranch
    in
      Partial instr terminator []

  -- Mixed
  | otherwise =
    let
      supply1 : supplyCaseInline : supplyCasePointer : _ = splitNameSupplies supply
      (pointerBranch, _) = freshId supply1

      -- Check whether an inline constructor matches, otherwise jump to the pointers branch
      (inlineInstr, inlineTerminator) = compileCaseConstructorInline env supply var inlines pointerBranch

      -- Check which pointer constructor matches
      (pointerInstr, pointerTerminator) = compileCaseConstructorPointer env supply var pointers
    in
      Partial inlineInstr inlineTerminator [BasicBlock (toName pointerBranch) pointerInstr pointerTerminator]

  where
    alts' = map (toCaseAlt env) alts
    (inlines, pointers) = partition altIsInline alts'

compileInstruction env supply (Iridium.Case var (Iridium.CaseInt alts defaultBranch)) = Partial [] (Do terminator) []
  where
    terminator :: Terminator
    terminator = Switch (toOperand env var) (toName defaultBranch) (map altToDestination alts) []
    altToDestination :: (Int, Id) -> (Constant, Name)
    altToDestination (value, to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral value), toName to)

compileInstruction _ _ (Iridium.Unreachable _) = Partial [] (Do $ Unreachable []) []

compileExpression :: Env -> NameSupply -> Iridium.Expr -> Id -> [Named Instruction]
compileExpression env supply (Iridium.Literal (Iridium.LitString value)) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  , Do $ Store False (LocalReference (pointer vectorType) namePtr) (ConstantOperand vector) Nothing 0 []
  -- Cast [n x i32]* to i32*
  , nameArray := BitCast (LocalReference (pointer vectorType) namePtr) voidPointer []
  , toName name := Call
    { tailCallKind = Nothing
    , callingConvention = Fast
    , returnAttributes = []
    , function = Right $ Builtins.unpackString
    , arguments =
      [ (ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) $ fromIntegral $ length value, [])
      , (LocalReference voidPointer nameArray, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply') = freshName supply
    (nameArray, _) = freshName supply'
    vectorType = ArrayType (fromIntegral $ length value) (IntegerType 32)
    vector = Array (IntegerType 32) $ map (\c -> Int 32 $ fromIntegral $ fromEnum c) value
compileExpression env supply (Iridium.Literal literal) name = [toName name := BitCast (ConstantOperand constant) t []]
  where
    constant :: Constant
    (constant, t) = case literal of
      Iridium.LitInt _ value ->
        ( Int (fromIntegral $ targetWordSize $ envTarget $ env) (fromIntegral $ value)
        , envValueType env
        )
      Iridium.LitFloat Iridium.Float32 value ->
        ( Float $ Float.Single $ realToFrac value
        , FloatingPointType FloatFP
        )
      Iridium.LitFloat Iridium.Float64 value ->
        ( Float $ Float.Double value
        , FloatingPointType DoubleFP
        )
compileExpression env supply expr@(Iridium.Call to@(Iridium.GlobalFunction global arity tp) args) name
  | not fakeIO && all isRight args =
    [ toName name := Call
        { tailCallKind = Nothing
        , callingConvention = compileCallingConvention convention
        , returnAttributes = []
        , function = Right $ globalFunctionToOperand env to
        , arguments = [(toOperand env arg, []) | Right arg <- args]
        , functionAttributes = []
        , metadata = []
        }
    ]
  | not fakeIO =
    let
      (name', supply') = freshName supply
      fromType = Iridium.typeToStrict retType
      toType = Iridium.typeOfExpr (envTypeEnv env) expr
      castArgument s (var, argType) =
        ( cast s' env (toOperand env var) argName (Iridium.variableType var) argType
        , LocalReference (compileType env argType) argName)
        where
          (argName, s') = freshNameFromId (Iridium.variableName var) s
      (castArgumentInstructions, argOperands) = unzip $ mapWithSupply castArgument supply' $ zip (rights args) $ rights argTypes
    in
      concat castArgumentInstructions
      ++
        [ name' := Call
          { tailCallKind = Nothing
          , callingConvention = compileCallingConvention convention
          , returnAttributes = []
          , function = Right $ globalFunctionToOperand env to
          , arguments = map (\arg -> (arg, [])) argOperands
          , functionAttributes = []
          , metadata = []
          }
        ]
      ++ cast supply env (LocalReference (compileType env fromType) name') (toName name) fromType toType
    -- We might need to cast the returned value and argument values, if type arguments were passed.
    -- Consider `%y = call @id: (forall a. !a -> a) $ {!Float} {%x: !Float}`
    -- Function 'id' will return the value as `i8*`, which we thus need to cast to Float
  | otherwise =
    [ toName nameValue := Call
        { tailCallKind = Nothing
        , callingConvention = compileCallingConvention convention
        , returnAttributes = []
        , function = Right $ globalFunctionToOperand env (Iridium.GlobalFunction global (arity - 1) $ Iridium.typeFromFunctionType $ Iridium.FunctionType (init argTypes) $ Core.TCon $ Core.TConDataType $ idFromString "Int")
        , arguments = [(toOperand env arg, []) | Right arg <- init args]
        , functionAttributes = []
        , metadata = []
        }
    ]
    ++ [toName nameRealWorld := Select (ConstantOperand $ Int 1 1) (ConstantOperand $ Undef tRealWorld) (ConstantOperand $ Undef tRealWorld) []]
    ++ compileBinds env supply'' [Iridium.Bind name (Iridium.BindTargetConstructor ioRes)
        [Left Iridium.typeInt, Right $ Iridium.VarLocal $ Iridium.Local nameValue Iridium.typeInt, Right $ Iridium.VarLocal $ Iridium.Local nameRealWorld Iridium.typeRealWorld]]
  where
    Iridium.FunctionType argTypes retType = Iridium.extractFunctionTypeWithArity (envTypeEnv env) arity tp
    EnvMethodInfo convention fakeIO = findMap global (envMethodInfo env)
    (nameValue, supply') = freshId supply
    (nameRealWorld, supply'') = freshId supply'
    ioRes = Iridium.DataTypeConstructor ioResId $ Iridium.typeFromFunctionType $ Iridium.FunctionType [Left $ Core.Quantor Nothing, Right $ Core.TVar 0, Right Iridium.typeRealWorld] Iridium.typeRealWorld
    ioResId = idFromString "IORes"
    tRealWorld = compileType env Iridium.typeRealWorld
compileExpression env supply (Iridium.Eval var) name = compileEval env supply (toOperand env var) (Iridium.variableType var) $ toName name
compileExpression env supply (Iridium.Var var) name = cast supply env (toOperand env var) (toName name) t t
  where t = Iridium.variableType var
compileExpression env supply (Iridium.Cast var toType) name = cast supply env (toOperand env var) (toName name) t toType
  where t = Iridium.variableType var
compileExpression env supply (Iridium.CastThunk var) name = cast supply env (toOperand env var) (toName name) t toType
  where
    t = Iridium.variableType var
    toType = Iridium.typeNotStrict t
compileExpression env supply expr@(Iridium.Instantiate var _) name = cast supply env (toOperand env var) (toName name) t toType
  where
    t = Iridium.variableType var
    toType = Iridium.typeOfExpr (envTypeEnv env) expr
compileExpression env supply (Iridium.Seq _ var) name = cast supply env (toOperand env var) (toName name) t t
  where t = Iridium.variableType var
compileExpression env supply expr@(Iridium.Phi branches) name = [toName name := Phi (compileType env t) (map compileBranch branches) []]
  where
    t = Iridium.typeOfExpr (envTypeEnv env) expr
    compileBranch :: Iridium.PhiBranch -> (Operand, Name)
    compileBranch (Iridium.PhiBranch blockId var) = (toOperand env var, toName blockId)
compileExpression env supply (Iridium.PrimitiveExpr primName args) name = compile (envTarget env) supply [toOperand env arg | Right arg <- args] $ toName name
  where
    (Iridium.Primitive _ compile) = Iridium.findPrimitive primName
compileExpression env supply (Iridium.Undefined ty) name = [toName name := Select (ConstantOperand $ Int 1 1) (ConstantOperand $ Undef t) (ConstantOperand $ Undef t) []]
  where
    t = compileType env ty

compileEval :: Env -> NameSupply -> Operand -> Core.Type -> Name -> [Named Instruction]
compileEval env supply operand tp name
  | Core.typeIsStrict tp = copy env operand name tp
  | otherwise =
    [ namePtr := ExtractValue operand [0] []
    , nameIsWHNF := ExtractValue operand [1] []
    , nameIsWHNFExt := ZExt (LocalReference boolType nameIsWHNF) (envValueType env) []
    , nameWHNF := callEval (LocalReference voidPointer namePtr) (LocalReference (envValueType env) nameIsWHNFExt)
    ] ++ cast supply env (LocalReference voidPointer nameWHNF) name (Core.TStrict $ Core.TVar 0) (Core.typeToStrict tp) 
  where
    (namePtr, supply') = freshName supply
    (nameIsWHNF, supply'') = freshName supply'
    (nameIsWHNFExt, supply''') = freshName supply''
    (nameWHNF, _) = freshName supply'''

callEval :: Operand -> Operand -> Instruction
callEval pointer isWHNF =
  Call
  { tailCallKind = Nothing
  , callingConvention = Fast
  , returnAttributes = []
  , function = Right $ Builtins.eval
  , arguments = [(pointer, []), (isWHNF, [])]
  , functionAttributes = []
  , metadata = []
  }

data CaseAlt = CaseAlt Iridium.DataTypeConstructor ConstructorLayout Iridium.BlockName

toCaseAlt :: Env -> (Iridium.DataTypeConstructor, Iridium.BlockName) -> CaseAlt
toCaseAlt env (con@(Iridium.DataTypeConstructor conId _), block) = CaseAlt con layout block
  where
    layout = findMap conId (envConstructors env)

altIsInline :: CaseAlt -> Bool
altIsInline (CaseAlt _ (LayoutInline _) _) = True
altIsInline _ = False

compileCaseConstructorInline :: Env -> NameSupply -> Iridium.Variable -> [CaseAlt] -> Iridium.BlockName -> ([Named Instruction], Named Terminator)
compileCaseConstructorInline env supply var alts defaultBranch = ([nameInt := PtrToInt (toOperand env var) (envValueType env) []], (Do switch))
  where
    (nameInt, supply') = freshName supply
    switch :: Terminator
    switch = Switch (LocalReference (envValueType env) nameInt) (toName defaultBranch) (map altToDestination alts) []
    altToDestination :: CaseAlt -> (Constant, Name)
    altToDestination (CaseAlt (Iridium.DataTypeConstructor conId _) (LayoutInline tag) to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral $ 2 * tag + 1), toName to)

compileCaseConstructorPointer :: Env -> NameSupply -> Iridium.Variable -> [CaseAlt] -> ([Named Instruction], Named Terminator)
compileCaseConstructorPointer env supply var alts = (instructions, (Do switch))
  where
    (defaultBranch, alts') = caseExtractMostFrequentBranch alts

    -- Cast the pointer to the type of the first constructor. It does not matter to which constructor we cast,
    -- as they all have the tag on the same position.
    CaseAlt _ (LayoutPointer structFirst) _ : _ = alts
    t = pointer $ structType env structFirst

    (supplyExtractTag, supply1) = splitNameSupply supply
    (nameCasted, supply2) = freshName supply1
    (nameTag, supply3) = freshName supply2

    instructions :: [Named Instruction]
    instructions =
      [ nameCasted := BitCast (toOperand env var) t [] ]
      ++ extractTag supply env (LocalReference t nameCasted) structFirst nameTag

    altToDestination :: CaseAlt -> (Constant, Name)
    altToDestination (CaseAlt (Iridium.DataTypeConstructor conId _) (LayoutPointer struct) to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral $ tagValue struct), toName to)

    switch :: Terminator
    switch = Switch (LocalReference (envValueType env) nameTag) (toName defaultBranch) (map altToDestination alts) []

caseExtractMostFrequentBranch :: [CaseAlt] -> (Iridium.BlockName, [CaseAlt])
caseExtractMostFrequentBranch alts = (defaultBranch, alts')
  where
     -- Find the branch that occurs most frequently
     defaultBranch = head $ maximumBy (compare `on` length) $ group $ sort $ map (\(CaseAlt _ _ block) -> block) alts
     -- Remove the default branch from the alts
     alts' = filter (\(CaseAlt _ _ block) -> defaultBranch /= block) alts
