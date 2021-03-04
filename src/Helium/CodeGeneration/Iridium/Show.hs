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

import Lvm.Common.Byte(stringFromBytes)
import Lvm.Common.Id(Id, stringFromId, idFromString)
import Lvm.Core.Module(Custom(..), DeclKind(..), Field(..))
import Lvm.Core.Type
import Data.List(intercalate)
import Data.Either(isRight)
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Utils
import qualified Text.PrettyPrint.Leijen as Pretty

class ShowDeclaration a where
  showDeclaration :: a -> (String, String)

instance ShowDeclaration a => Show (Declaration a) where
  showsPrec _ (Declaration name vis mod customs a) s = customsString ++ export ++ maybe "" (("from " ++) . (++ " ") . stringFromId) mod ++ keyword ++ " @" ++ showId name body ++ s
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

showDefault :: ShowWithQuantors a => a -> String
showDefault = showQ []

showsPrecDefault :: ShowWithQuantors a => Int -> a -> ShowS
showsPrecDefault _ = showsQ []

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

instance Show Type where
  show = showDefault

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
  showsQ quantors expr = case expr of
    Literal lit
      -> text "literal " . shows lit
    Call fn additionalRegions args returnRegions
      -> text "call " . shows fn . text " $ " . showsIfRegion additionalRegions (showsQ quantors additionalRegions . text " ") . showCallArguments quantors args . showsIfRegion returnRegions (text " @ " . showsQ quantors returnRegions)
    Instantiate var args
      -> text "instantiate " . showsQ quantors var . text " " . showTypeArguments quantors args
    Eval var
      -> text "eval " . showsQ quantors var
    Var var
      -> text "var " . showsQ quantors var
    Cast var t
      -> text "cast " . showsQ quantors var . text " as " . showsQ quantors t
    CastThunk var
      -> text "castthunk " . showsQ quantors var
    Phi branches
      -> text "phi " . showArguments quantors branches
    PrimitiveExpr prim args
      -> text "prim " . text (stringFromId prim) . showCallArguments quantors args
    Undefined t
      -> text "undefined " . showsQ quantors t
    Seq v1 v2
      -> text "seq " . showsQ quantors v1 . text ", " . showsQ quantors v2

instance Show Expr where
  show = showDefault
  showsPrec = showsPrecDefault

instance ShowWithQuantors PhiBranch where
  showsQ quantors (PhiBranch branch var) = text (stringFromId branch) . text " => " . showsQ quantors var

instance Show PhiBranch where
  show = showDefault
  showsPrec = showsPrecDefault

instructionIndent :: String
instructionIndent = "  "

instance ShowWithQuantors Bind where
  showsQ quantors (Bind var target args region) = text "%" . showId var . text " = " . showsQ quantors target . text " $ " . showCallArguments quantors args . (if region == RegionGlobal then id else text " @ " . showsQ quantors region)

instance Show Bind where
  show = showDefault
  showsPrec = showsPrecDefault

instance ShowWithQuantors BindTarget where
  showsQ quantors target = case target of
    BindTargetFunction global additionalRegions (BindThunkRegions r1 r2) -> text "function " . shows global . (if additionalRegions /= RegionVarsTuple [] || r1 /= RegionVarsTuple [] || r2 /= RegionVarsTuple [] then text " $ " . showsQ quantors (RegionVarsTuple [additionalRegions, r1, r2]) else id)
    BindTargetThunk var bindRegions -> text "thunk " . showsQ quantors var . (if bindRegions /= BindThunkRegions (RegionVarsTuple []) (RegionVarsTuple []) then text " $ " . showsQ quantors bindRegions else id)
    BindTargetConstructor con -> text "constructor " . shows con
    BindTargetTuple arity -> text "tuple " . shows arity

instance Show BindTarget where
  show = showDefault
  showsPrec = showsPrecDefault

instance ShowWithQuantors BindThunkRegions where
  showsQ quantors (BindThunkRegions r1 r2) = showsQ quantors (RegionVarsTuple [r1, r2])

instance Show BindThunkRegions where
  show = showDefault
  showsPrec = showsPrecDefault

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
  showsQ quantors (NewRegion var (Just size) next) =
    text instructionIndent . text "newregion " . shows var . text " bounded " . shows size . text "\n" . showsQ quantors next
  showsQ quantors (NewRegion var Nothing next) =
    text instructionIndent . text "newregion " . shows var . text " unbounded\n" . showsQ quantors next
  showsQ quantors (ReleaseRegion var next) =
    text instructionIndent . text "release " . shows var . text "\n" . showsQ quantors next
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

instance Show Instruction where
  show = showDefault
  showsPrec = showsPrecDefault

instance ShowWithQuantors Local where
  showsQ quantors (Local name t) = ('%' :) . showId name . text ": " . showsQ quantors t

instance Show Local where
  show = showDefault
  showsPrec = showsPrecDefault

instance Show Global where
  showsPrec _ (GlobalVariable name t) = ('@' :) . showId name . text ": " . shows t

instance Show GlobalFunction where
  showsPrec _ (GlobalFunction name arity fntype) = ('@' :) . showId name . text "[" . shows arity . text "]: " . shows fntype

instance ShowWithQuantors Variable where
  showsQ quantors (VarLocal local) = showsQ quantors local
  showsQ _ (VarGlobal global) = shows global

instance Show Variable where
  show = showDefault
  showsPrec = showsPrecDefault

instance ShowWithQuantors Block where
  showsQ quantors (Block name instruction) = text (stringFromId name) . text ":\n" . showsQ quantors instruction

instance Show Block where
  show = showDefault
  showsPrec = showsPrecDefault

instance Show MethodAnnotation where
  show MethodAnnotateTrampoline = "trampoline"
  show (MethodAnnotateCallConvention conv) = "callconvention:" ++ show conv
  show MethodAnnotateImplicitIO = "implicit_io"

instance Show CallingConvention where
  show CCC = "c"
  show CCFast = "fast"
  show CCPreserveMost = "preserve_most"

showAnnotations :: [MethodAnnotation] -> String
showAnnotations [] = ""
showAnnotations annotations = "[" ++ intercalate " " (map show annotations) ++ "]"

showReturnRegion, showAdditionalRegion, showLocalRegion :: Int -> String
showReturnRegion idx = "ρᵣ" ++ showSubscript idx
showAdditionalRegion idx = "ρₐ" ++ showSubscript idx
showLocalRegion idx = "ρ" ++ showSubscript idx

instance ShowWithQuantors RegionVar where
  showQ _ = show
  showsQ _ = shows

instance ShowWithQuantors RegionVars where
  showQ _ = show
  showsQ _ = shows

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
  showDeclaration (Method tp additionalRegions args rettype retRegions annotations entry blocks) =
    ( "define"
    , ": { " ++ show tp ++ " } $ " ++ (showIfRegion additionalRegions $ show additionalRegions ++ " ") ++ "(" ++ intercalate ", " args' ++ "): "
      ++ showQ quantors rettype ++ showIfRegion retRegions (" @ " ++ show retRegions) ++ " " ++ showAnnotations annotations ++ " {\n" ++ showQ quantors entry ++ (blocks >>= ('\n' :) . showQ quantors) ++ "\n}\n"
    )
    where
      (args', quantors) = showMethodArguments [] args

showIfRegion :: RegionVars -> String -> String
showIfRegion (RegionVarsTuple []) _ = ""
showIfRegion _ str = str

showsIfRegion :: RegionVars -> ShowS -> ShowS
showsIfRegion (RegionVarsTuple []) _ = id
showsIfRegion _ f = f

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

showCallArguments :: QuantorNames -> [Either Type Local] -> ShowS
showCallArguments quantors = showArguments' showArg
  where
    showArg (Left tp) = text "{" . showsQ quantors tp . text "}"
    showArg (Right var) = showsQ quantors var

showTypeArguments :: QuantorNames -> [Type] -> ShowS
showTypeArguments quantors tps = list (text " ") $ map (\tp -> text "{" . text (showTypeAtom quantors tp) . text "}") tps

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
