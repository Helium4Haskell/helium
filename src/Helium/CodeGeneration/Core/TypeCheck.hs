-- A type checker for Core files.

-- | Module      :  TypeCheck
--    License     :  GPL
--
--    Maintainer  :  helium@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable
module Helium.CodeGeneration.Core.TypeCheck
  ( checkModule,
    checkModuleIO,
  )
where

import Data.List
import Helium.CodeGeneration.Core.TypeEnvironment
import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type
import Lvm.Core.Utils
import System.Exit
import Text.PrettyPrint.Leijen (pretty)

type Location = [String]

data TypeError = TypeError Location Message

data Message
  = MessageExpected String Type (Maybe Expr)
  | MessageNotEqual Type Type
  | MessageNameNotFound Id

instance Show Message where
  show (MessageExpected str tp (Just expr)) =
    "  Expected " ++ str ++ ", got `" ++ showType tp ++ "' instead"
      ++ " as the type of expression:\n\n"
      ++ show (pretty expr)
  show (MessageExpected str tp Nothing) =
    "  Expected " ++ str ++ ", got `" ++ showType tp ++ "' instead"
  show (MessageNotEqual t1 t2) =
    "  Types `" ++ showType t1 ++ "' and `" ++ showType t2 ++ "' do not match"
  show (MessageNameNotFound name) =
    "  Variable not found: " ++ show name

instance Show TypeError where
  show (TypeError location msg) =
    "Type error"
      ++ concat (map (\loc -> "\nin " ++ loc) location)
      ++ "\n"
      ++ show msg
      ++ "\n\n"

type Check a = Either TypeError a

report :: Message -> Check a
report = Left . TypeError []

assert :: TypeEnvironment -> Type -> Type -> Check ()
assert env t1 t2
  | typeEqual env t1 t2 = Right ()
  | otherwise = report $ MessageNotEqual t1 t2

(@@) :: Check a -> String -> Check a
Right x @@ name = Right x
Left (TypeError loc msg) @@ name = Left $ TypeError (name : loc) msg

infix 1 @@

checkModule :: CoreModule -> [(CoreDecl, TypeError)]
checkModule mod@(Module _ _ _ _ decls) = decls >>= checkDecl env
  where
    env = typeEnvForModule mod

checkModuleIO :: String -> CoreModule -> IO ()
checkModuleIO pass mod = case checkModule mod of
  [] -> return ()
  errors -> do
    putStrLn ("\n\nType errors in Core file after pass " ++ show pass)
    mapM_ printError errors
    putStrLn (show (length errors) ++ " errors after pass " ++ show pass)
    exitWith (ExitFailure 1)
  where
    printError (decl, err) = putStrLn $ "\n" ++ show (pretty decl) ++ "\n\n" ++ show err

checkDecl :: TypeEnvironment -> CoreDecl -> [(CoreDecl, TypeError)]
checkDecl env decl = case checkDecl' env decl of
  Left err -> [(decl, err)]
  Right _ -> []

checkDecl' :: TypeEnvironment -> CoreDecl -> Check ()
checkDecl' env decl@DeclValue {} = do
  tp <- checkExpression env (valueValue decl) @@ "function " ++ show (declName decl)
  assert env tp (typeRemoveAnn (declType decl)) @@ "annotated type of function " ++ show (declName decl)
checkDecl' env _ = return ()

checkExpression :: TypeEnvironment -> Expr -> Check Type
checkExpression env (Let binds expr) = do
  let env' = typeEnvAddBinds binds env
  let envBinds =
        case binds of
          Rec _ -> env'
          _ -> env
  sequence_ $ map (checkBind env') $ listFromBinds binds
  checkExpression env' expr
checkExpression env (Match name alts) = do
  scrutinee <- checkId env name
  ~(tp : tps) <- traverse (\alt -> checkAlt env scrutinee alt @@ "match on variable " ++ show name) alts
  sequence_ $ map (\tp' -> assert env tp tp' @@ "the inferred types of the alts") tps
  return tp
checkExpression env (Ap e1 e2) = do
  t1 <- checkExpression env e1
  t2 <- checkExpression env e2
  case typeNotStrict $ typeNormalizeHead env t1 of
    (TAp (TAp (TCon TConFun) tArg) tReturn) -> do
      assert env t2 tArg @@ "the argument of an application"
      return tReturn
    t1' -> report (MessageExpected "function type" t1' $ Just e1) @@ "the argument of an application"
checkExpression env (ApType e1 t2) = do
  t1 <- checkExpression env e1
  case typeNormalizeHead env t1 of
    TForall (Quantor idx _ _) t1' -> return $ typeSubstitute idx t2 t1'
    t1' -> report $ MessageExpected "forall type" t1' $ Just e1
checkExpression env (Lam _ var@(Variable x tArg) expr) = do
  let env' = typeEnvAddVariable var env
  tReturn <- checkExpression env' expr @@ "lambda with argument " ++ show x
  return $ TAp (TAp (TCon TConFun) tArg) tReturn
checkExpression env (Forall quantor expr) = do
  tp <- checkExpression env expr
  return $ TForall quantor tp
checkExpression env (Var name) = checkId env name
checkExpression _ (Con (ConTuple arity) _) = return $ typeTuple arity
checkExpression env (Con (ConId x) Nothing) = return $ typeOfId env x
checkExpression env (Con (ConId x) (Just mid)) = do
  checkId env mid @@ "annotated type for memory reuse " ++ stringFromId mid
  return $ typeOfId env x
checkExpression _ (Lit lit) = return $ typeOfLiteral lit

checkBind :: TypeEnvironment -> Bind -> Check ()
checkBind env (Bind (Variable x tpAnnotated) expr) = do
  tpResolved <- checkExpression env expr @@ "bind for variable " ++ show x
  assert env tpAnnotated tpResolved @@ "annotated type for variable " ++ show x

checkAlt :: TypeEnvironment -> Type -> Alt -> Check Type
checkAlt env tp (Alt pat expr) = do
  env' <- checkPattern env tp pat @@ "pattern " ++ show (ppPattern [] pat)
  checkExpression env' expr @@ "alt with pattern " ++ show (ppPattern [] pat)

checkPattern :: TypeEnvironment -> Type -> Pat -> Check TypeEnvironment
checkPattern env tp (PatLit lit) = do
  assert env tp (typeOfLiteral lit)
  return env
checkPattern env tp PatDefault = return env
checkPattern env tp pat@(PatCon con@(ConId _) typeArgs ids) = do
  let tCon = typeApplyList (typeOfCoreExpression env $ Con con Nothing) typeArgs
  vars <- findVars tCon ids
  return $ typeEnvAddVariables vars env
  where
    findVars :: Type -> [Id] -> Check [Variable]
    findVars tReturn [] = do
      assert env tp tReturn
      return []
    findVars (TAp (TAp (TCon TConFun) tArg) tReturn) (x : xs) = do
      let var = Variable x tArg
      vars <- findVars tReturn xs
      return (var : vars)
    findVars t _ = do
      report $ MessageExpected "function type" t Nothing
checkPattern env tp pat = return $ typeEnvAddPattern pat env

checkId :: TypeEnvironment -> Id -> Check Type
checkId (TypeEnvironment _ values) name = case lookupMap name values of
  Just tp -> return tp
  Nothing -> report $ MessageNameNotFound name
