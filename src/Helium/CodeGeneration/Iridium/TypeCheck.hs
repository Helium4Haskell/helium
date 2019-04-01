module Helium.CodeGeneration.Iridium.TypeCheck where

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show
import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type
import Data.Maybe
import Data.List
import System.Exit

data Location
  = DeclareLocal
  | UseLocal
  | DeclareGlobal !Int
  | UseGlobalFunction !Int
  | UseGlobalVariable
  deriving (Eq, Show)

data TypeError
  -- The type of the MatchTarget does not match the variable
  = TEMatch !Variable !Type
  -- The type of the variable of a Case instruction does not match with a type of a pattern
  | TECase !Variable !Type
  | TEReturn !Variable !Type
  -- Type at declaration does not match type at use
  | TEVariable !Variable !Variable
  | TEMultipleDeclarations ![Variable]
  | TENotDeclared !Id
  -- The annotated type of a method does not match the given argument types and return type
  | TEMethod !Id !Type !Type

instance Show TypeError where
  show (TEMatch var tp) = "Variable " ++ show var ++ " should have type " ++ show tp ++ " in a match instruction"
  show (TECase var tp) = "Variable " ++ show var ++ " should have type " ++ show tp ++ " in a case instruction"
  show (TEReturn var tp) = "Variable " ++ show var ++ " should have type " ++ show tp ++ " in a return instruction"
  show (TEVariable var1 var2) = "Variable declared as " ++ show var1 ++ " is used as " ++ show var2
  show (TEMultipleDeclarations vars) = "Variable has multiple declarations: " ++ show vars
  show (TENotDeclared name) = "Variable " ++ show name ++ " is not declared"
  show (TEMethod name t1 t2) = "Method " ++ show name ++ " was declared with type " ++ show t1 ++ ", which does not match the type inferred from the arguments and return type: " ++ show t2

data Analysis
  = AJoin !Analysis !Analysis
  | AVar !Id !Location !Type
  | ATypeError !TypeError
  | AEmpty

checkModule :: Module -> [TypeError]
checkModule mod = errors
  where
    typeEnv = envWithSynonyms mod
    analysis =
      fromList (map (analyseMethod typeEnv) $ moduleMethods mod)
      `AJoin` fromList (map analyseAbstractMethod $ moduleAbstractMethods mod)
    (Env occurrences errors1) = toEnv analysis emptyEnv
    errors2 = listFromMap occurrences >>= uncurry checkOccurrences
    errors = errors1 ++ errors2

checkModuleIO :: String -> FilePath-> Module -> IO ()
checkModuleIO name path mod = do
  let errors = checkModule mod
  if null errors then
    return ()
  else do
    putStrLn ("Type errors in Iridium file after pass " ++ show name)
    print mod
    mapM_ print errors
    putStrLn (show (length errors) ++ " type error(s) in Iridium file " ++ show path ++ " after pass " ++ show name)
    exitWith (ExitFailure 1)

aCheck :: TypeEnvironment -> Type -> Type -> TypeError -> Analysis
aCheck env t1 t2 err
  | typeIsStrict t1 == typeIsStrict t2 && typeEqual env t1 t2 = AEmpty
  | otherwise = ATypeError err

fromList :: [Analysis] -> Analysis
fromList = foldr AJoin AEmpty

analyseAbstractMethod :: Declaration AbstractMethod -> Analysis
analyseAbstractMethod (Declaration name _ _ _ (AbstractMethod arity tp _)) = AVar name (DeclareGlobal arity) tp

analyseMethod :: TypeEnvironment -> Declaration Method -> Analysis
analyseMethod env (Declaration name _ _ _ method@(Method fnType args retType' _ block blocks)) =
  aCheck env fnType fnType' (TEMethod name fnType fnType')
    `AJoin` AVar name (DeclareGlobal $ length aArgs) fnType
    `AJoin` fromList aArgs
    `AJoin` analyseBlock env retType block
    `AJoin` fromList (map (analyseBlock env retType) blocks)
  where
    fnType' = typeFromFunctionType $ methodFunctionType method
    retType = typeToStrict retType'
    aArgs = [AVar arg (DeclareLocal) tp | Right (Local arg tp) <- args]

analyseBlock :: TypeEnvironment -> Type -> Block -> Analysis
analyseBlock env tp (Block _ instr) = analyseInstruction env tp instr

variableToAnalysis :: Variable -> Analysis
variableToAnalysis (VarLocal (Local name tp)) = AVar name UseLocal tp
variableToAnalysis (VarGlobal (GlobalFunction name arity tp)) = AVar name (UseGlobalFunction arity) tp
variableToAnalysis (VarGlobal (GlobalVariable name tp)) = AVar name UseGlobalVariable tp

analyseInstruction :: TypeEnvironment -> Type -> Instruction -> Analysis
analyseInstruction env returnType (Let name expr next) =
  AJoin
    (AVar name DeclareLocal $ typeOfExpr env expr)
    $ AJoin
      (fromList $ map variableToAnalysis $ dependenciesOfExpr expr)
      $ analyseInstruction env returnType next
analyseInstruction env returnType (LetAlloc binds next) =
  AJoin
    (fromList $ map (analyseBind env) binds)
    $ analyseInstruction env returnType next
analyseInstruction env returnType (Match var target instantiation fields next)
  = variableToAnalysis var
    `AJoin` aCheck env (variableType var) expectedType (TEReturn var expectedType)
    `AJoin` fromList (catMaybes $ zipWith analyseArg fields $ matchFieldTypes target instantiation)
    `AJoin` analyseInstruction env returnType next
  where
    expectedType = matchArgumentType target instantiation
    analyseArg Nothing _ = Nothing
    analyseArg (Just name) tp = Just $ AVar name DeclareLocal tp
analyseInstruction env returnType (Return var) =
  aCheck env (variableType var) returnType (TEReturn var returnType)
  `AJoin` variableToAnalysis var
analyseInstruction env _ (Case var _) = variableToAnalysis var
  -- TODO: Check whether the types of the alts/branches match with the type of 'var'
analyseInstruction _ _ _ = AEmpty

analyseBind :: TypeEnvironment -> Bind -> Analysis
analyseBind env bind@(Bind var target args) =
  AVar var DeclareLocal tp
  `AJoin` aTarget
  `AJoin` fromList [ variableToAnalysis arg | Right arg <- args ]
  where
    tp = bindType env bind
    aTarget = case target of
      BindTargetFunction var -> variableToAnalysis var
      BindTargetThunk var -> variableToAnalysis var
      _ -> AEmpty

data Occurrence = Occurrence !Location !Type
data Env = Env !(IdMap [Occurrence]) ![TypeError]

emptyEnv :: Env
emptyEnv = Env emptyMap []

addOccurence :: Id -> Occurrence -> Env -> Env
addOccurence name occurrence (Env m errors) = Env (insertMapWith name [occurrence] (occurrence :) m) errors

addError :: TypeError -> Env -> Env
addError err (Env m errors) = Env m (err:errors)

toEnv :: Analysis -> Env -> Env
toEnv (AVar name location tp) env = addOccurence name (Occurrence location tp) env
toEnv (ATypeError err) env = addError err env
toEnv AEmpty env = env
toEnv (AJoin a1 a2) env = toEnv a2 $ toEnv a1 env

checkOccurrences :: Id -> [Occurrence] -> [TypeError]
checkOccurrences name occurrences =
  case declarations of
    [] -> [TENotDeclared name]
    decl1 : decl2 : _
      | any (\(Occurrence l _) -> l == DeclareLocal) declarations -> [TEMultipleDeclarations $ map (toVariable name) declarations]
    decl : _ ->
      let
        declaration = toVariable name decl
        alternative = case decl of
          (Occurrence (DeclareGlobal arity) tp) -> Just $ VarGlobal $ GlobalVariable name tp
          _ -> Nothing
        check :: Occurrence -> Maybe TypeError
        check use
          | var /= declaration && Just var /= alternative = Just $ TEVariable declaration var
          | otherwise = Nothing
          where
            var = toVariable name use
      in
        mapMaybe check uses
  where
    (declarations, uses) = partition (\(Occurrence l _) -> isDeclaration l) occurrences

isDeclaration :: Location -> Bool
isDeclaration DeclareLocal = True
isDeclaration (DeclareGlobal _) = True
isDeclaration _ = False

toVariable :: Id -> Occurrence -> Variable
toVariable name (Occurrence DeclareLocal tp) = VarLocal $ Local name tp
toVariable name (Occurrence UseLocal tp) = VarLocal $ Local name tp
toVariable name (Occurrence (DeclareGlobal arity) tp) = VarGlobal $ GlobalFunction name arity tp
toVariable name (Occurrence (UseGlobalFunction arity) tp) = VarGlobal $ GlobalFunction name arity tp
toVariable name (Occurrence UseGlobalVariable tp) = VarGlobal $ GlobalVariable name tp
