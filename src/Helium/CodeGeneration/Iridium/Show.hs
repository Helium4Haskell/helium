{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Show instances for Iridium

module Helium.CodeGeneration.Iridium.Show where

import Lvm.Common.Byte(stringFromBytes)
import Lvm.Common.Id(Id, stringFromId, idFromString)
import Lvm.Core.Module(Custom(..), DeclKind(..))
import Data.List(intercalate)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

class ShowDeclaration a where
  showDeclaration :: a -> (String, String)

instance ShowDeclaration a => Show (Declaration a) where
  show (Declaration name vis mod customs a) = customsString ++ export ++ maybe "" (("from " ++) . (++ " ") . stringFromId) mod ++ keyword ++ " @" ++ showId name ++ body
    where
      customsString = customs >>= ((++ "\n") . ('#' : ) . showCustom)
      export
        | vis == Exported = "export "
        | otherwise = ""
      (keyword, body) = showDeclaration a

showCustom :: Custom -> String
showCustom (CustomInt i) = "[int " ++ show i ++ "]"
showCustom (CustomBytes bs) = "[bytes " ++ show (stringFromBytes bs) ++ "]"
showCustom (CustomName id) = "[name " ++ showId id ++ "]"
showCustom (CustomLink id kind) = "[link @" ++ showId id ++ " " ++ showDeclKind kind ++ "]"
showCustom (CustomDecl kind customs) = "[decl " ++ showDeclKind kind ++ (customs >>= ((" " ++) . showCustom)) ++ "]"
showCustom CustomNothing = "[]"

showDeclKind :: DeclKind -> String
showDeclKind DeclKindName = "name"
showDeclKind DeclKindKind = "kind"
showDeclKind DeclKindBytes = "bytes"
showDeclKind DeclKindCode = "code"
showDeclKind DeclKindValue = "value"
showDeclKind DeclKindCon = "con"
showDeclKind DeclKindImport = "import"
showDeclKind DeclKindModule = "module"
showDeclKind DeclKindExtern = "extern"
showDeclKind DeclKindExternType = "externtype"
showDeclKind (DeclKindCustom id) = "@" ++ showId id

instance Show Literal where
  show (LitInt x) = "int " ++ show x
  show (LitFloat precision x) = "float" ++ show precision ++ " " ++ show x
  show (LitString x) = "str " ++ show x

instance Show Expr where
  show (Literal lit) = "literal " ++ show lit
  show (Call fn args) = "call " ++ show fn ++ " $ " ++ showArguments args
  show (Eval var) = "eval " ++ show var
  show (Var var) = "var " ++ show var
  show (Cast var t) = "cast " ++ show var ++ " as " ++ show t
  show (Phi branches) = "phi " ++ showArguments branches
  show (PrimitiveExpr prim args) = "prim " ++ stringFromId prim ++ showArguments args
  show (Undefined t) = "undefined " ++ show t
  show (Seq v1 v2) = "seq " ++ show v1 ++ ", " ++ show v2

instance Show PhiBranch where
  show (PhiBranch branch var) = stringFromId branch ++ " => " ++ show var

instructionIndent :: String
instructionIndent = "  "

instance Show Bind where
  show (Bind var target args) = "%" ++ showId var ++ " = " ++ show target ++ " $ " ++ showArguments args

instance Show BindTarget where
  show (BindTargetFunction global) = "function " ++ show global
  show (BindTargetThunk var) = "thunk " ++ show var
  show (BindTargetConstructor con) = "constructor " ++ show con
  show (BindTargetTuple arity) = "tuple " ++ show arity

instance Show MatchTarget where
  show (MatchTargetConstructor con) = show con
  show (MatchTargetThunk arity) = "thunk " ++ show arity
  show (MatchTargetTuple arity) = "tuple " ++ show arity

instance Show Case where
  show (CaseConstructor branches) = "constructor " ++ showArguments' showBranch branches
    where
      showBranch :: (DataTypeConstructor, BlockName) -> String
      showBranch (con, to) = "\n" ++ instructionIndent ++ "  " ++ show con ++ " to " ++ stringFromId to
  show (CaseInt branches defaultBranch) = "int " ++ showArguments' showBranch branches ++ "\n" ++ instructionIndent ++ "  otherwise " ++ stringFromId defaultBranch
    where
      showBranch :: (Int, BlockName) -> String
      showBranch (lit, to) = "\n" ++ instructionIndent ++ "  " ++ show lit ++ " to " ++ stringFromId to

instance Show Instruction where
  show (Let var expr next) = instructionIndent ++ "%" ++ showId var ++ " = " ++ show expr ++ "\n" ++ show next
  show (LetAlloc binds next) = instructionIndent ++ "letalloc " ++ intercalate ", " (map show binds) ++ "\n" ++ show next
  show (Jump to) = instructionIndent ++ "jump " ++ show to
  show (Match var target args next) = instructionIndent ++ "match " ++ show var ++ " on " ++ show target ++ " " ++ showArguments' showField args ++ "\n" ++ show next
    where
      showField Nothing = "_"
      showField (Just l) = '%' : showId l
  show (Case var branches) = instructionIndent ++ "case " ++ show var ++ " " ++ show branches
  show (Return var) = instructionIndent ++ "return " ++ show var
  show Unreachable = instructionIndent ++ "unreachable"

instance Show Local where
  show (Local name t) = "%" ++ showId name ++ ": " ++ show t

instance Show Global where
  show (GlobalFunction name fntype) = "@" ++ showId name ++ ": " ++ show fntype
  show (GlobalVariable name t) = "@" ++ showId name ++ ": " ++ show t

instance Show Variable where
  show (VarLocal local) = show local
  show (VarGlobal global) = show global

instance Show Block where
  show (Block name instruction) = stringFromId name ++ ":\n" ++ show instruction

instance Show Annotation where
  show AnnotateTrampoline = "trampoline"
  show (AnnotateCallConvention conv) = "callconvention:" ++ show conv

instance Show CallingConvention where
  show CCC = "c"
  show CCFast = "fast"
  show CCPreserveMost = "preserve_most"

showAnnotations :: [Annotation] -> String
showAnnotations [] = ""
showAnnotations annotations = "[" ++ intercalate " " (map show annotations) ++ "]"

instance ShowDeclaration AbstractMethod where
  showDeclaration (AbstractMethod fntype annotations) =
    ( "declare"
    , ": " ++ show fntype ++ " " ++ showAnnotations annotations ++ "\n"
    )

instance ShowDeclaration Method where
  showDeclaration (Method args rettype annotations entry blocks) =
    ( "define"
    , showArguments args ++ ": " ++ show rettype ++ " " ++ showAnnotations annotations ++ " {\n" ++ show entry ++ (blocks >>= ('\n' :) . show) ++ "\n}\n"
    )

instance Show Module where
  show (Module name dependencies customs decls abstracts methods) =
    "module " ++ stringFromId name ++ "\n"
    ++ importString
    ++ (customs >>= ('\n' :) . show)
    ++ (decls >>= ('\n' :) . show)
    ++ (abstracts >>= ('\n' :) . show)
    ++ (methods >>= ('\n' :) . show)
    where
      importString = "import " ++ showArguments' (stringFromId) dependencies ++ "\n"

instance ShowDeclaration CustomDeclaration where
  showDeclaration (CustomDeclaration kind) = ("custom", ": " ++ showDeclKind kind ++ "\n")

instance ShowDeclaration DataTypeConstructorDeclaration where
  showDeclaration (DataTypeConstructorDeclaration args) =
    ( "constructor"
    , showArguments args
    )

instance Show DataTypeConstructor where
  show (DataTypeConstructor dataType name args) = "@" ++ showId name ++ ": " ++ showArguments args ++ " -> @" ++ showId dataType

instance ShowDeclaration DataType where
  showDeclaration (DataType cons) =
    ( "data"
    , " {" ++ (cons >>= (("\n" ++) .unlines . map ("  " ++) . lines . show)) ++ "}\n"
    )

instance Show PrimitiveType where
  show (TypeAny) = "any"
  show (TypeAnyThunk) = "any_thunk"
  show (TypeAnyWHNF) = "any_whnf"

  show TypeInt = "int"
  show (TypeFloat precision) = "float" ++ show precision
  show TypeRealWorld = "real_world"
  show (TypeDataType name) = "@" ++ showId name
  show (TypeTuple arity) = "tuple " ++ show arity
  show (TypeFunction) = "anyfunction"
  show (TypeGlobalFunction fntype) = "function " ++ show fntype

  show (TypeUnsafePtr) = "unsafeptr"

instance Show FloatPrecision where
  show Float32 = "32"
  show Float64 = "64"
showArguments' :: (a -> String) -> [a] -> String
showArguments' showFn = ("("++) . (++")") . intercalate ", " . map showFn

showArguments :: Show a => [a] -> String
showArguments = showArguments' show

instance Show FunctionType where
  show (FunctionType args ret) = showArguments args ++ " -> " ++ show ret

showId :: Id -> String
showId name
  | str == "" = "\"\""
  | all (`elem` chars) str = str
  | otherwise = show str
  where
    chars = ['.', '$'] ++ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] 
    str = stringFromId name
