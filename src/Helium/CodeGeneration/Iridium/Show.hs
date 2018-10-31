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
  show (Declaration name vis customs a) = customsString ++ export  ++ keyword ++ " @" ++ stringFromId name ++ body
    
    where
      customsString = customs >>= ((++ "\n") . ('#' : ) . showCustom) -- TODO: Show customs
      export
        | vis == Exported = "export "
        | otherwise = ""
      (keyword, body) = showDeclaration a

showCustom :: Custom -> String
showCustom (CustomInt i) = "[int " ++ show i ++ "]"
showCustom (CustomBytes bs) = "[bytes " ++ show (stringFromBytes bs) ++ "]"
showCustom (CustomName id) = "[name " ++ stringFromId id ++ "]"
showCustom (CustomLink id kind) = "[link @" ++ stringFromId id ++ " " ++ showDeclKind kind ++ "]"
showCustom (CustomDecl kind customs) = "[decl " ++ showDeclKind kind ++ (customs >>= ((" " ++) . showCustom)) ++ "]"
showCustom CustomNothing = "[nothing]"

{- data Custom
= CustomInt   !Int
| CustomBytes !Bytes
| CustomName  Id
| CustomLink  Id !DeclKind
| CustomDecl  !DeclKind ![Custom]
| CustomNothing -}

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
showDeclKind (DeclKindCustom id) = "@" ++ stringFromId id

instance Show Literal where
  show (LitInt x) = "int " ++ show x
  show (LitDouble x) = "float " ++ show x
  show (LitString x) = "str " ++ show x

instance Show Pattern where
  show (PatternCon con) = show con
  show (PatternLit lit) = show lit

instance Show Expr where
  show (Literal lit) = show lit
  show (Call fn args) = "call " ++ show fn ++ " $ " ++ showArguments args
  show (Eval var) = "eval " ++ show var
  show (Var var) = "var " ++ show var
  show (Cast var t) = "cast " ++ show var ++ " as " ++ show t
  show (Phi branches) = "phi " ++ showArguments branches

instance Show PhiBranch where
  show (PhiBranch branch var) = stringFromId branch ++ " => " ++ show var

instructionIndent :: String
instructionIndent = "  "

instance Show Bind where
  show b@(Bind _ target args) = show (bindLocal b) ++ " = " ++ show target ++ " $ " ++ showArguments args

instance Show BindTarget where
  show (BindTargetFunction global) = show global
  show (BindTargetConstructor con) = show con

instance Show Instruction where
  show (Let var expr next) = instructionIndent ++ "let " ++ show (Local var $ typeOfExpr expr) ++ " = " ++ show expr ++ "\n" ++ show next
  show (LetAlloc binds next) = instructionIndent ++ "letalloc " ++ intercalate ", " (map show binds) ++ "\n" ++ show next
  show (Jump to) = instructionIndent ++ "jump " ++ show to
  show (Match var conId args next) = instructionIndent ++ "match " ++ show var ++ " on " ++ show conId ++ showArguments' showField args ++ "\n" ++ show next
    where
      showField Nothing = "_"
      showField (Just l) = show l
  show (If var pat whenTrue whenFalse) = instructionIndent ++ "if " ++ show var ++ " matches " ++ show pat ++ " then jump " ++ stringFromId whenTrue ++ " else " ++ stringFromId whenFalse
  show (Return var) = instructionIndent ++ "ret " ++ show var

instance Show Local where
  show (Local name t) = "%" ++ stringFromId name ++ ": " ++ show t

instance Show Global where
  show (Global name fntype) = "@" ++ stringFromId name ++ ": " ++ show fntype

instance Show Variable where
  show (VarLocal local) = show local
  show (VarGlobal global) = show global

instance Show Block where
  show (Block name instruction) = stringFromId name ++ ":\n" ++ show instruction

instance Show AbstractMethod where
  show (AbstractMethod name fntype) = "declare @" ++ stringFromId name ++ ": " ++ show fntype

instance ShowDeclaration Method where
  showDeclaration (Method args rettype entry blocks) =
    ( "define"
    , showArguments args ++ ": " ++ show rettype ++ " {\n" ++ show entry ++ (blocks >>= ('\n' :) . show) ++ "\n}\n"
    )

instance Show Module where
  show (Module name decls abstracts methods) =
    "module " ++ show name ++ "\n"
    ++ (decls >>= ('\n' :) . show)
    ++ (abstracts >>= ('\n' :) . show)
    ++ (methods >>= ('\n' :) . show)
