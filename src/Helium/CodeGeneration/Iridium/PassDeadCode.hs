{-| Module      :  PassDeadCode
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Implements a dead code analysis pass.
-- The pass removes all variables whose value is not needed.
-- Furthermore it removes arguments from functions if possible.
-- Unused arguments cannot always be removed due to currying.
-- The analysis determines the minimum number of arguments which are always
-- bound to a function when curried, stored in stateBindCount.
-- The arguments whose index is smaller than the minimum bind count may be removed.
-- If an argument cannot be removed, the caller will replace the (possibly dead)
-- variable with an undefined value.

module Helium.CodeGeneration.Iridium.PassDeadCode(passDeadCode) where

import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Data
import Data.Maybe (catMaybes, fromMaybe, isNothing)
import Data.Either (rights, isRight)
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Type

passDeadCode :: NameSupply -> Module -> Module
passDeadCode supply mod = mod{ moduleMethods = methods, moduleAbstractMethods = abstracts }
  where
    res = analyse mod
    methods = catMaybes $ mapWithSupply (`transformMethod` res) supply $ moduleMethods mod
    abstracts = filter (\decl -> isExported decl || isLive res (declarationName decl)) $ moduleAbstractMethods mod

    isExported (Declaration _ (ExportedAs _) _ _ _) = True
    isExported _ = False

-- Analysis
data Constraint
  = CEmpty -- true
  | CLive !Id -- live(x)
  | CImplies !Id ![Id] -- live(x) ==> (live(y1) ^ live(y2) ^ ..)
  | CArgument { argReturn :: !Id, argFn :: !Id, argArgIndex :: !Int, argValue :: !Id } -- (live(return) ^ live(ith argument of fn)) ==> live(value)
  | CBindCount !Id !Int -- bindcount(x) <= k
  | CSequence Constraint Constraint -- c1 ^ c2

fromList :: [Constraint] -> Constraint
fromList [] = CEmpty
fromList (c : cs) = foldr CSequence c cs

bindCountInVariable :: Variable -> Constraint
bindCountInVariable (VarGlobal (GlobalVariable name _)) = CBindCount name 0
bindCountInVariable _ = CEmpty

data Env = Env { envFunction :: !Id }
-- Set of live variables, bools denoting whether the argument of a variable should be preserved
data Result = Result !TypeEnvironment !IdSet !(IdMap [Bool])

analyse :: Module -> Result
analyse mod = Result (envWithSynonyms mod) (stateLive state) $ mapMapWithId liveArgs argMap
  where
    state = solve initialState
    initialState = constraintToState argMap c $ emptyState argMap
    argMap = mapFromList fns
    c = fromList constraints
    (fns, constraints) = unzip $ map analyseMethod $ moduleMethods mod
    liveArgs :: Id -> [Either () Id] -> [Bool]
    liveArgs fn args = zipWith argIsLive args [0..]
      where
        argIsLive :: Either () Id -> Int -> Bool
        argIsLive (Left _) _ = True
        argIsLive (Right name) index = index >= bindCount || name `elemSet` stateLive state
        bindCount = findMap fn $ stateBindCount state

analyseMethod :: Declaration Method -> ((Id, [Either () Id]), Constraint)
analyseMethod (Declaration name vis _ _ (Method _ args _ _ b bs)) =
  ( (name, map argName args) -- Try to remove unused arguments
  , fnConstraint $ fromList $ map (analyseBlock env) $ b : bs
  )
  where
    argName (Left _) = Left ()
    argName (Right local) = Right $ localName local
    env = Env name
    exported = case vis of
      ExportedAs _ -> True
      _ -> name == idFromString "main"
    fnConstraint = case exported of
      True -> CSequence $ CSequence
        (CBindCount name 0) -- cannot remove arguments, as other modules can import this function
        $ CLive name -- the function is exported and is thus live
      False -> id

analyseBlock :: Env -> Block -> Constraint
analyseBlock env (Block _ instr) = analyseInstruction env instr

analyseInstruction :: Env -> Instruction -> Constraint
analyseInstruction env (Let var (Call fn args) next) = CSequence
  (analyseCall var (globalFunctionName fn) args)
  $ analyseInstruction env next
analyseInstruction env (Let var expr next) = CSequence
  (fromList $ map bindCountInVariable vars)
  $ CSequence (CImplies var (map variableName vars))
  $ analyseInstruction env next
  where
    vars = dependenciesOfExpr expr
analyseInstruction env (LetAlloc binds next) = CSequence
  (fromList $ map analyseBind binds)
  $ analyseInstruction env next
analyseInstruction env (Jump _) = CEmpty
analyseInstruction env (Match var _ _ args next) = CSequence
  (fromList $ map (\name -> CImplies name [variableName var]) $ catMaybes args)
  $ analyseInstruction env next
analyseInstruction env (Case var _) = CImplies (envFunction env) [variableName var]
analyseInstruction env (Return var) = CImplies (envFunction env) [variableName var]
analyseInstruction env (Unreachable (Just var)) = CImplies (envFunction env) [variableName var]
analyseInstruction env (Unreachable Nothing) = CEmpty

analyseCall :: Id -> Id -> [Either Type Variable] -> Constraint
analyseCall var fn args = CSequence argumentConstraints $ fromList $
  CImplies var [fn]
  : CBindCount fn (length args)
  : zipWith constraintArgument args [0..]
  where
    constraintArgument (Right arg) index = CArgument var fn index $ variableName arg
    constraintArgument (Left tp) index = CEmpty
    argumentConstraints = fromList $ map bindCountInVariable $ rights args

analyseBind :: Bind -> Constraint
analyseBind (Bind var (BindTargetFunction fn) args) = analyseCall var (globalFunctionName fn) args
analyseBind (Bind var target args) = CSequence
  (fromList $ map bindCountInVariable args')
  $ CImplies var $ targetVars ++ map variableName args'
  where
    args' = rights args
    targetVars = case target of
      BindTargetThunk var -> [variableName var]
      _ -> []

data Implications = Implications ![Id] ![(Id, Id)]

-- State for the solver
data State = State
  { stateLive :: IdSet
  , stateImplies :: IdMap Implications
  , stateBindCount :: IdMap Int -- The minimum number of arguments that are used in binds to the variable
  , stateWorklist :: [Id]
  }

emptyState :: IdMap [Either () Id] -> State
emptyState argMap = State emptySet emptyMap (mapMap length argMap) []

addLive :: Id -> State -> State
addLive var s@(State live implies bindCount worklist)
  | var `elemSet` live = s
  | otherwise = State (insertSet var live) implies bindCount (var : worklist)

addImplies :: Id -> [Id] -> State -> State
addImplies var vars (State live implies bindCount worklist) =
  State live (insertMapWith var (Implications vars []) (\(Implications xs ys) -> Implications (vars ++ xs) ys) implies) bindCount worklist

-- Adds the implications `live(a) ^ live(b) ==> live(c)`
addTwoImplies :: Id -> Id -> Id -> State -> State
addTwoImplies a b c (State live implies bindCount worklist) =
  State live (add a b $ add b a $ implies) bindCount worklist
  where
    add x y = insertMapWith x (Implications [] [(y, c)]) (\(Implications xs ys) -> Implications xs ((y, c) : ys))

addBindCount :: Id -> Int -> State -> State
addBindCount var count (State live implies bindCount worklist) = State live implies (insertMapWith var 0 (min count) bindCount) worklist

constraintToState :: IdMap [Either () Id] -> Constraint -> State -> State
constraintToState _ CEmpty = id
constraintToState _ (CLive var) = addLive var
constraintToState _ (CImplies var vars) = addImplies var vars
constraintToState argMap (CArgument ret fn argIndex value) = case lookupMap fn argMap of
  Just args
    | argIndex < length args ->
      let Right argName = args !! argIndex
      in addTwoImplies argName ret value
  _ -> addImplies ret [value]
constraintToState _ (CBindCount var count) = addBindCount var count
constraintToState argMap (CSequence c1 c2) = constraintToState argMap c1 . constraintToState argMap c2

solve :: State -> State
solve s@(State _ _ _ []) = s
solve s = solve (solveStep s)

solveStep :: State -> State
solveStep (State live implies bindCount (var : worklist)) =
  foldr addLive (State live implies bindCount worklist) implied
  where
    implied :: [Id]
    implied = case lookupMap var implies of
      Just (Implications xs ys) -> xs ++ map snd (filter ((`elemSet` live) . fst) ys)
      Nothing -> []

isLive :: Result -> Id -> Bool
isLive (Result _ live _) var = var `elemSet` live

preservedArguments :: Result -> Id -> [Bool]
preservedArguments (Result _ _ args) var = fromMaybe (repeat True) $ lookupMap var args

preservedArguments' :: Result -> Id -> Maybe [Bool]
preservedArguments' (Result _ _ args) var = lookupMap var args

transformMethod :: NameSupply -> Result -> Declaration Method -> Maybe (Declaration Method)
transformMethod supply res (Declaration name vis mod customs (Method tp args retType annotations b bs))
  | not $ isLive res name = Nothing
  | otherwise = Just $ Declaration name vis mod customs $ Method tp' args' retType annotations b' bs'
  where
    (_, tp') = transformType res name (length $ filter isRight args) tp
    args' = map fst $ filter snd $ zip args $ preservedArguments res name
    b' : bs' = mapWithSupply transformBlock supply $ b : bs
    transformBlock s (Block blockName instr) = Block blockName $ transformInstruction s res instr

transformInstruction :: NameSupply -> Result -> Instruction -> Instruction
transformInstruction supply res (Let var expr next)
  | isLive res var = instr $ Let var expr' $ transformInstruction supply2 res next
  | otherwise = transformInstruction supply res next
  where
    (expr', instr) = transformExpr supply1 res expr
    (supply1, supply2) = splitNameSupply supply
transformInstruction supply res (LetAlloc binds next)
  | null binds' = transformInstruction supply res next
  | otherwise = instr $ LetAlloc binds' $ transformInstruction supply2 res next
  where
    instr = flip (foldr id) instrs
    (binds', instrs) = unzip $ mapWithSupply (`transformBind` res) supply1 $ filter (isLive res . bindVar) binds
    (supply1, supply2) = splitNameSupply supply
transformInstruction _ _ instr@(Jump _) = instr
transformInstruction _ _ instr@(Return _) = instr
transformInstruction _ _ instr@(Unreachable _) = instr
transformInstruction _ _ instr@(Case _ _) = instr
transformInstruction supply res (Match var t instantiation fields next)
  | all isNothing fields' = transformInstruction supply res next
  | otherwise = Match var t instantiation fields' $ transformInstruction supply res next
  where
    fields' = map (>>= (\field -> if isLive res field then Just field else Nothing)) fields

transformExpr :: NameSupply -> Result -> Expr -> (Expr, Instruction -> Instruction)
transformExpr supply res (Call fn args) = (Call (transformGlobal res fn) args', instr)
  where
    (args', instr) = transformCall supply res fn args (getArgTypes args)
transformExpr _ _ expr = (expr, id)

getArgTypes :: [Either Type Variable] -> [Either () Type]
getArgTypes = map argType
  where
    argType (Right var) = Right $ variableType var
    argType (Left _) = Left ()

transformBind :: NameSupply -> Result -> Bind -> (Bind, Instruction -> Instruction)
transformBind supply res@(Result env _ _) (Bind var (BindTargetFunction global@(GlobalFunction _ _ _)) args) =
  (Bind var target args', instr)
  where
    (args', instr) = transformCall supply res global args (getArgTypes args)
    target
      | arity == 0 = BindTargetThunk $ VarGlobal $ GlobalVariable name tp
      | otherwise = BindTargetFunction global'
    global'@(GlobalFunction name arity tp) = transformGlobal res global
transformBind _ _ bind = (bind, id)

transformCall :: NameSupply -> Result -> GlobalFunction -> [Either Type Variable] -> [Either () Type] -> ([Either Type Variable], Instruction -> Instruction)
transformCall supply res fn args argTypes = (args', flip (foldr id) instrs)
  where
    (args', instrs) = unzip $ catMaybes $ mapWithSupply transformArgument supply $ zip (zip args argTypes)
      -- In case of a LetAlloc bind, the function may be oversaturated. Those oversaturated arguments must always be preserved
      $ preservedArguments res (globalFunctionName fn) ++ repeat True
    
    transformArgument :: NameSupply -> ((Either Type Variable, Either () Type), Bool) -> Maybe (Either Type Variable, Instruction -> Instruction)
    transformArgument _ (_, False) = Nothing
    transformArgument s ((Right arg, Right t), True)
      | not $ isLive res $ variableName arg = Just (Right $ VarLocal $ Local name t, Let name $ Undefined t)
      where
        (name, _) = freshIdFromId (variableName arg) s
    transformArgument s ((arg, _), True) = Just $ (arg, id)

transformGlobal :: Result -> GlobalFunction -> GlobalFunction
transformGlobal res (GlobalFunction name arity fnType) = GlobalFunction name arity' fnType'
  where
    (arity', fnType') = transformType res name arity fnType

transformType :: Result -> Id -> Int -> Type -> (Int, Type)
transformType res@(Result env _ _) name arity fnType =
  case preservedArguments' res name of
    Just bools
      | any not bools ->
        let
          FunctionType args retType = extractFunctionTypeWithArity env arity fnType
          args' = map fst $ filter snd $ zip args bools
        in
          (length $ filter isRight args', typeFromFunctionType $ FunctionType args' retType)
    _ -> (arity, fnType)
