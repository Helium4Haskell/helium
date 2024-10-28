{-| Module      :  TypeCheck
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- A type checker for Core files.

module Helium.CodeGeneration.Core.TypeCheck (checkModule, checkModuleIO) where

import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.Lvm.Core.Module
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.Utils
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdMap

import System.Exit
import Data.List
import Text.PrettyPrint.Leijen (pretty)

type Location = [String]
data TypeError = TypeError Location Message
data Message
  = MessageExpected QuantorNames String Type (Maybe Expr)
  | MessageNotEqual QuantorNames Type Type
  | MessageNameNotFound Id

instance Show Message where
  show (MessageExpected quantors str tp (Just expr))
    = "  Expected " ++ str ++ ", got `" ++ showType quantors tp ++ "' instead"
    ++ "  as the type of expression:\n\n" ++ show (pretty expr)
  show (MessageExpected quantors str tp Nothing)
    = "  Expected " ++ str ++ ", got `" ++ showType quantors tp ++ "' instead"
  show (MessageNotEqual quantors t1 t2)
    = "  Types `" ++ showType quantors t1 ++ "' and `" ++ showType quantors t2 ++ "' do not match"
  show (MessageNameNotFound name)
    = "  Variable not found: " ++ show name

instance Show TypeError where
  show (TypeError location msg)
    = "Type error"
    ++ concat (map (\loc -> "\nin " ++ loc) location)
    ++ "\n" ++ show msg
    ++ "\n\n"

type Check a = Either TypeError a

report :: Message -> Check a
report = Left . TypeError []

assert :: TypeEnvironment -> QuantorNames -> Type -> Type -> Check ()
assert env quantors t1 t2
  | typeEqual env t1 t2 = Right ()
  | otherwise = report $ MessageNotEqual quantors t1 t2

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
checkDecl' env decl@DeclValue{} = do
  tp <- checkExpression env [] (valueValue decl) @@ "function " ++ show (declName decl)
  assert env [] tp (declType decl) @@ "annotated type of function " ++ show (declName decl)
checkDecl' env _ = return ()

checkExpression :: TypeEnvironment -> QuantorNames -> Expr -> Check Type
checkExpression env quantors (Let binds expr) = do
  let env' = typeEnvAddBinds binds env
  let envBinds =
        case binds of
          Rec _ -> env'
          _ -> env
  sequence_ $ map (checkBind env' quantors) $ listFromBinds binds
  checkExpression env' quantors expr
checkExpression env quantors (Match name alts) = do
  scrutinee <- checkId env name
  ~(tp:tps) <- traverse (\alt -> checkAlt env quantors scrutinee alt @@ "match on variable " ++ show name) alts
  sequence_ $ map (\tp' -> assert env quantors tp tp' @@ "the inferred types of the alts") tps
  return tp
checkExpression env quantors (Ap e1 e2) = do
  t1 <- checkExpression env quantors e1
  t2 <- checkExpression env quantors e2
  case typeNotStrict $ typeNormalizeHead env t1 of
    (TAp (TAp (TCon TConFun) tArg) tReturn) -> do
      assert env quantors t2 tArg @@ "the argument of an application"
      return tReturn
    t1' -> report (MessageExpected quantors "function type" t1' $ Just e1) @@ "the argument of an application"
checkExpression env quantors (ApType e1 t2) = do
  t1 <- checkExpression env quantors e1
  case typeNormalizeHead env t1 of
    t1'@(TForall _ _ _) -> return $ typeApply t1' t2
    t1' -> report $ MessageExpected quantors "forall type" t1' $ Just e1
checkExpression env quantors (Lam _ var@(Variable x tArg) expr) = do
  let env' = typeEnvAddVariable var env
  tReturn <- checkExpression env' quantors expr @@ "lambda with argument " ++ show x
  return $ TAp (TAp (TCon TConFun) tArg) tReturn
checkExpression env quantors (Forall quantor kind expr) = do
  tp <- checkExpression (typeEnvWeaken 1 env) (freshQuantorName quantors quantor : quantors) expr
  return $ TForall quantor kind tp
checkExpression env quantors (Var name) = checkId env name
-- Con or Lit
checkExpression env quantors expr = return $ typeOfCoreExpression env expr

checkBind :: TypeEnvironment -> QuantorNames -> Bind -> Check ()
checkBind env quantors (Bind (Variable x tpAnnotated) expr) = do
  tpResolved <- checkExpression env quantors expr @@ "bind for variable " ++ show x
  assert env quantors tpAnnotated tpResolved @@ "annotated type for variable " ++ show x

checkAlt :: TypeEnvironment -> QuantorNames -> Type -> Alt -> Check Type
checkAlt env quantors tp (Alt pat expr) = do
  env' <- checkPattern env quantors tp pat @@ "pattern " ++ show (ppPattern [] pat)
  checkExpression env' quantors expr @@ "alt with pattern " ++ show (ppPattern [] pat)

checkPattern :: TypeEnvironment -> QuantorNames -> Type -> Pat -> Check TypeEnvironment
checkPattern env quantors tp (PatLit lit) = do
  assert env quantors tp (typeOfLiteral lit)
  return env
checkPattern env quantors tp PatDefault = return env
checkPattern env quantors tp pat@(PatCon con@(ConId _) typeArgs ids) = do
  let tCon = typeApplyList (typeOfCoreExpression env $ Con con) typeArgs
  vars <- findVars tCon ids
  return $ typeEnvAddVariables vars env
  where
    findVars :: Type -> [Id] -> Check [Variable]
    findVars tReturn [] = do
      assert env quantors tp tReturn
      return []
    findVars (TAp (TAp (TCon TConFun) tArg) tReturn) (x:xs) = do
      let var = Variable x tArg
      vars <- findVars tReturn xs
      return (var : vars)
    findVars t _ = do
      report $ MessageExpected quantors "function type" t Nothing
checkPattern env quantors tp pat = return $ typeEnvAddPattern pat env


checkId :: TypeEnvironment -> Id -> Check Type
checkId (TypeEnvironment _ globals locals) name = case lookupMap name globals of
  Just tp -> return tp
  Nothing -> case lookupMap name locals of
    Just tp -> return tp
    Nothing -> report $ MessageNameNotFound name
