{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- Show instances for Iridium

module Helium.CodeGeneration.Iridium.Show where

import Helium.Lvm.Common.Id(Id, stringFromId, idFromString)
import Helium.Lvm.Core.Module(Custom(..), DeclKind(..), Field(..))
import Helium.Lvm.Core.Type
import Helium.Lvm.Common.Byte(stringFromBytes)
import Data.List(intercalate)
import Data.Either(isRight)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import qualified Text.PrettyPrint.Leijen as Pretty

class ShowDeclaration a where
  showDeclaration :: a -> (String, String)

instance ShowDeclaration a => Show (Declaration a) where
  show (Declaration name vis mod customs a) = customsString ++ export ++ maybe "" (("from " ++) . (++ " ") . stringFromId) mod ++ keyword ++ " @" ++ showId name body
    where
      customsString = customs >>= ((++ "\n") . ('#' : ) . showCustom)
      export = case vis of
        ExportedAs exportName -> "export_as @" ++ showId exportName " "
        _ -> ""
      (keyword, body) = showDeclaration a

class ShowWithQuantors a where
  showQ :: QuantorNames -> a -> String
  showQ names value = showsQ names value ""

  showsQ :: QuantorNames -> a -> ShowS
  showsQ names value = (showQ names value ++)

instance {-# Overlaps #-} ShowWithQuantors a => Show a where
  show = showQ []
  showsPrec _ = showsQ []

text :: String -> ShowS
text = (++)

list :: ShowS -> [ShowS] -> ShowS
list _ [] = id
list sep (x:xs) = x . list' xs
  where
    list' (y:ys) = sep . y . list' ys
    list' [] = id


instance ShowWithQuantors Type where
  showQ quantors = showTypeAtom quantors

showCustom :: Custom -> String
showCustom (CustomInt i) = "[int " ++ show i ++ "]"
showCustom (CustomBytes bs) = "[bytes " ++ show (stringFromBytes bs) ++ "]"
showCustom (CustomName id) = "[name @" ++ showId id [] ++ "]"
showCustom (CustomLink id kind) = "[link @" ++ showId id [] ++ " " ++ showDeclKind kind ++ "]"
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
showDeclKind (DeclKindCustom id) = "@" ++ showId id []

instance Show Literal where
  show (LitInt IntTypeInt x) = "int " ++ show x
  show (LitInt IntTypeChar x) = "char " ++ show x
  show (LitFloat precision x) = "float" ++ show precision ++ " " ++ show x
  show (LitString x) = "str " ++ show x

instance ShowWithQuantors Expr where
  showsQ quantors (Literal lit) = text "literal " . shows lit
  showsQ quantors (Call fn args) = text "call " . shows fn . text " $ " . showCallArguments quantors args
  showsQ quantors (Instantiate var args) = text "instantiate " . showsQ quantors var . text " " . showTypeArguments quantors args
  showsQ quantors (Eval var) = text "eval " . showsQ quantors var
  showsQ quantors (Var var) = text "var " . showsQ quantors var
  showsQ quantors (Cast var t) = text "cast " . showsQ quantors var . text " as " . showsQ quantors t
  showsQ quantors (CastThunk var) = text "castthunk " . showsQ quantors var
  showsQ quantors (Phi branches) = text "phi " . showArguments quantors branches
  showsQ quantors (PrimitiveExpr prim args) = text "prim " . text (stringFromId prim) . showCallArguments quantors args
  showsQ quantors (Undefined t) = text "undefined " . showsQ quantors t
  showsQ quantors (Seq v1 v2) = text "seq " . showsQ quantors v1 . text ", " . showsQ quantors v2

instance ShowWithQuantors PhiBranch where
  showsQ quantors (PhiBranch branch var) = text (stringFromId branch) . text " => " . showsQ quantors var

instructionIndent :: String
instructionIndent = "  "

instance ShowWithQuantors Bind where
  showsQ quantors (Bind var target args) = text "%" . showId var . text " = " . showsQ quantors target . text " $ " . showCallArguments quantors args

instance ShowWithQuantors BindTarget where
  showsQ quantors (BindTargetFunction global) = text "function " . shows global
  showsQ quantors (BindTargetThunk var) = text "thunk " . showsQ quantors var
  showsQ quantors (BindTargetConstructor con) = text "constructor " . shows con
  showsQ quantors (BindTargetTuple arity) = text "tuple " . shows arity

instance Show MatchTarget where
  showsPrec _ (MatchTargetConstructor con) = shows con
  showsPrec _ (MatchTargetTuple arity) = text "tuple " . shows arity

instance Show Case where
  showsPrec _ (CaseConstructor branches) = text "constructor " . showArguments' showBranch branches
    where
      showBranch :: (DataTypeConstructor, BlockName) -> ShowS
      showBranch (con, to) = text "\n" . text instructionIndent . text "  " . shows con . text " to " . text (stringFromId to)
  showsPrec _ (CaseInt branches defaultBranch) = text "int " . showArguments' showBranch branches . text "\n" . text instructionIndent . text "  otherwise " . text (stringFromId defaultBranch)
    where
      showBranch :: (Int, BlockName) -> ShowS
      showBranch (lit, to) = text "\n" . text instructionIndent . text "  " . shows lit . text " to " . text (stringFromId to)

instance ShowWithQuantors Instruction where
  showsQ quantors (Let var expr next) =
    text instructionIndent . text "%" . showId var . text " = " . showsQ quantors expr . text "\n" . showsQ quantors next
  showsQ quantors (LetAlloc binds next) =
    text instructionIndent . text "letalloc " . list (text ", ") (map (showsQ quantors) binds) . text "\n" . showsQ quantors next
  showsQ quantors (Jump to) =
    text instructionIndent . text "jump " . text (stringFromId to)
  showsQ quantors (Match var target instantiation args next) =
    text instructionIndent . text "match " . showsQ quantors var . text " on " . shows target . text " " . showTypeArguments quantors instantiation . showArguments' showField args . text "\n" . showsQ quantors next
    where
      showField :: Maybe Id -> ShowS
      showField Nothing = text "_"
      showField (Just l) = ('%' :) . showId l
  showsQ quantors (Case var branches) =
    text instructionIndent . text "case " . showsQ quantors var . text " " . shows branches
  showsQ quantors (Return var) =
    text instructionIndent . text "return " . showsQ quantors var
  showsQ quantors (Unreachable (Just var)) =
    text instructionIndent . text "unreachable " .showsQ quantors var
  showsQ quantors (Unreachable Nothing) =
    text instructionIndent . text "unreachable"

instance ShowWithQuantors Local where
  showsQ quantors (Local name t) = ('%' :) . showId name . text ": " . showsQ quantors t

instance Show Global where
  showsPrec _ (GlobalVariable name t) = ('@' :) . showId name . text ": " . shows t

instance Show GlobalFunction where
  showsPrec _ (GlobalFunction name arity fntype) = ('@' :) . showId name . text "[" . shows arity . text "]: " . shows fntype

instance ShowWithQuantors Variable where
  showsQ quantors (VarLocal local) = showsQ quantors local
  showsQ quantors (VarGlobal global) = shows global

instance ShowWithQuantors Block where
  showsQ quantors (Block name instruction) = text (stringFromId name) . text ":\n" . showsQ quantors instruction

instance Show Annotation where
  show AnnotateTrampoline = "trampoline"
  show (AnnotateCallConvention conv) = "callconvention:" ++ show conv
  show AnnotateImplicitIO = "implicit_io"

instance Show CallingConvention where
  show CCC = "c"
  show CCFast = "fast"
  show CCPreserveMost = "preserve_most"

showAnnotations :: [Annotation] -> String
showAnnotations [] = ""
showAnnotations annotations = "[" ++ intercalate " " (map show annotations) ++ "]"

instance ShowDeclaration AbstractMethod where
  showDeclaration (AbstractMethod sourceType fnType annotations)
    | sourceType == typeRemoveArgumentStrictness (typeFromFunctionType fnType) =
      ( "declare"
      , "[" ++ show arity ++ "]: { " ++ show (typeFromFunctionType fnType) ++ " } " ++ showAnnotations annotations ++ "\n"
      )
    | otherwise =
      ( "declare"
      , ": { " ++ show sourceType ++ " } $ [" ++ show arity ++ "]{ " ++ show (typeFromFunctionType fnType) ++ " }"
      )
    where
      arity = functionArity fnType

instance ShowDeclaration Method where
  showDeclaration (Method tp args rettype annotations entry blocks) =
    ( "define"
    , ": { " ++ show tp ++ " } $ (" ++ intercalate ", " args' ++ "): "
      ++ showQ quantors rettype ++ " " ++ showAnnotations annotations ++ " {\n" ++ showQ quantors entry ++ (blocks >>= ('\n' :) . showQ quantors) ++ "\n}\n"
    )
    where
      (args', quantors) = showMethodArguments [] args

showMethodArguments :: QuantorNames -> [Either Quantor Local] -> ([String], QuantorNames)
showMethodArguments quantors (Left quantor : args) = (("forall " ++ name) : args', quantors'')
  where
    name = freshQuantorName quantors quantor
    quantors' = name : quantors
    (args', quantors'') = showMethodArguments quantors' args
showMethodArguments quantors (Right arg : args) = (showQ quantors arg : args', quantors')
  where
    (args', quantors') = showMethodArguments quantors args
showMethodArguments quantors [] = ([], quantors)

instance Show Module where
  show (Module name dependencies customs datas types abstracts methods) =
    "module " ++ stringFromId name ++ "\n"
    ++ importString
    ++ (customs >>= ('\n' :) . show)
    ++ (datas >>= ('\n' :) . show)
    ++ (types >>= ('\n' :) . show)
    ++ (abstracts >>= ('\n' :) . show)
    ++ (methods >>= ('\n' :) . show)
    where
      importString = "import (" ++ intercalate ", " (map stringFromId dependencies) ++ ")\n"

instance ShowDeclaration CustomDeclaration where
  showDeclaration (CustomDeclaration kind) = ("custom", ": " ++ showDeclKind kind ++ "\n")

instance ShowDeclaration DataTypeConstructorDeclaration where
  showDeclaration (DataTypeConstructorDeclaration tp fs) =
    ( "constructor"
    , ": { " ++ show tp ++ " }" ++ recordFields
    )
    where
      recordFields = case fs of
        [] -> ""
        _  -> " (" ++ intercalate ", " (map show fs) ++ ")"

instance Show DataTypeConstructor where
  show (DataTypeConstructor name tp) = "@" ++ showId name "" ++ ": " ++ show tp

instance Show Field where
  showsPrec _ (Field name) = showId name

instance ShowDeclaration DataType where
  showDeclaration (DataType cons) =
    ( "data"
    , " {" ++ (cons >>= (("\n" ++) .unlines . map ("  " ++) . lines . show)) ++ "}\n"
    )

instance ShowDeclaration TypeSynonym where
  showDeclaration (TypeSynonym s tp) =
    ( keyword
    , " = " ++ constructor ++ "{ " ++ destructor ++ show tp ++ " }\n"
    )
    where
      (keyword, constructor, destructor) = case s of
        TypeSynonymAlias -> ("type", "", "")
        TypeSynonymNewtype exportConstructor exportDestructor ->
          ( "newtype"
          , case exportConstructor of
              ExportedAs name -> '@' : showId name " "
              _ -> ""
          , case exportDestructor of
              ExportedAs name -> '@' : showId name " :: "
              _ -> ""
          )

instance Show FloatPrecision where
  show Float32 = "32"
  show Float64 = "64"

showArguments' :: (a -> ShowS) -> [a] -> ShowS
showArguments' showFn xs = text "(" . list (text ", ") (map showFn xs) . text ")"

showArguments :: ShowWithQuantors a => QuantorNames -> [a] -> ShowS
showArguments quantors = showArguments' (showsQ quantors)

showCallArguments :: QuantorNames -> [Either Type Variable] -> ShowS
showCallArguments quantors = showArguments' showArg
  where
    showArg (Left tp) = text "{" . showsQ quantors tp . text "}"
    showArg (Right var) = showsQ quantors var

showTypeArguments :: QuantorNames -> [Type] -> ShowS
showTypeArguments quantors tps = list (text " ") $ map (\tp -> text "{" . showsQ quantors tp . text "}") tps

instance Show FunctionType where
  show fntype@(FunctionType args _) = "[" ++ show arity ++ "] " ++ show tp
    where
      arity = length $ filter isRight args
      tp = typeFromFunctionType fntype

showId :: Id -> ShowS
showId name
  | str == "" = text "\"\""
  | all (`elem` chars) str = text str
  | otherwise = shows str
  where
    chars = ['.', '$', '#', '_'] ++ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] 
    str = stringFromId name
