-- A type checker for Iridium.


module Helium.CodeGeneration.Iridium.Check.Type (iridiumTypeCheck) where

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show (showId)

import Lvm.Common.Id (Id)
import Lvm.Common.IdMap (lookupMap, insertMap)

iridiumTypeCheck :: Module -> 

data Error
  -- Same local variable name is used with different types
  = ErrorLocal !Id !PrimitiveType !PrimitiveType
  -- A global is not defined
  | ErrorGlobalUndeclared !Global
  -- Same global variable name is used with different types
  | ErrorGlobalType !Id !FunctionType !FunctionType
  -- A constructor is not defined
  | ErrorConstructorUndeclared !DataTypeConstructor
  -- A constructor is used with a different signature
  | ErrorConstructorType !DataTypeConstructor !DataTypeConstructor
  | ErrorMatchVariable !Variable !PrimitiveType
  | ErrorReturn !Variable !PrimitiveType

data Context = Context
  { contextFunction :: Id
  , contextBlock :: Id
  , contextReturnType :: PrimitiveType
  }

data ErrorWithContext = ErrorWithContext !Error !Context

data Env = Env
  { envLocals ::!(IdMap PrimitiveType)
  , envGlobals :: !(IdMap FunctionType)
  , envConstructors :: !(IdMap DataTypeConstructor)
  , envContext :: !Context
  , envErrors :: ![ErrorWithContext]
  }

checkVariable :: Variable -> Env -> Env
checkVariable (VarGlobal var) = checkGlobal var
checkVariable (VarLocal var) = checkLocal var

checkVariables :: [Variable] -> Env -> Env
checkVariables = flip $ foldr checkVariable

report :: Error -> Env -> Env
report error (Env locals globals cons context errors) = Env locals globals cons context (ErrorWithContext error context : errors)

reportIf :: Bool -> Error -> Env -> Env
reportIf False _ = id
reportIf True error = report error

checkGlobal :: Global -> Env -> Env
checkGlobal var@(Global name ty) env@(Env _ globals _ _ _) = case lookupMap name globals of
  Nothing -> report (ErrorGlobalUndeclared var) env
  Just declaredType
    | declaredType == ty -> env
    | otherwise -> report (ErrorGlobalType name declaredType ty) env

checkLocal :: Local -> Env -> Env
checkLocal var@(Local name ty) env@(Env locals globals cons context errors) = case lookupMap name locals of
  Nothing -> Env (insertMap name ty) globals cons context errors
  Just ty'
    | ty == ty' -> env
    | otherwise -> report (ErrorLocal name ty' ty) env

checkConstructor :: DataTypeConstructor -> Env -> Env
checkConstructor con@(DataTypeConstructor _ name _) env@(Env _ _ cons _ _) = case lookupMap name cons of
  Nothing -> report (ErrorConstructorUndeclared con)
  Just con'
    | con == con' -> env
    | otherwise -> report (ErrorConstructorType con' con)

checkExpr :: Expr -> Env -> Env
checkExpr = undefined

checkBind :: Bind -> Env -> Env
checkBind = undefined

checkBinds :: [Bind] -> Env -> Env
checkBinds = flip $ foldr checkBind

matchTargetTypes :: MatchTarget -> (PrimitiveType, [PrimitiveType])
matchTargetTypes = undefined

checkMatchTarget :: MatchTarget -> Env -> Env
checkMatchTarget = undefined

checkInstruction :: Instruction -> Env -> Env
checkInstruction (Let name expr next) = checkLocal name (typeOfExpr expr) . checkExpr expr . checkInstruction next
checkInstruction (LetAlloc binds next) = checkBinds binds . checkInstruction next
checkInstruction (Jump _) = id
checkInstruction (Match variable target locals next) =
  checkVariable variable
  . reportIf (variableType variable /= varType) (ErrorMatchVariable variable varType)
  . checkVariables (zipWith (\n t -> VarLocal $ Local n t) locals fields)
  . checkMatchTarget target
  . checkInstruction next
  where
    (varType, fields) = matchTargetTypes
checkInstruction (Case var c) = checkVariable var -- TODO: Check whether the alts match with the variable
checkInstruction (Return var) = checkVariable var . (\env -> let retType = contextReturnType . envContext env in reportIf (variableType var /= retType) (ErrorReturn var retType) env)
checkInstruction (Unreachable _) = id
