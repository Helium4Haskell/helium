module Helium.CodeGeneration.Iridium.Parse.Custom where

import Control.Applicative
import Helium.CodeGeneration.Iridium.Parse.Parser
import Lvm.Common.Byte (bytesFromString)
import Lvm.Core.Module
import qualified Text.Parsec as P

pCustoms :: Parser [Custom]
pCustoms = P.many (pToken '#' *> pCustom)

pCustom :: Parser Custom
pCustom = pBrackets (pCustomInt <|> pCustomBytes <|> pCustomName <|> pCustomLink <|> pCustomDecl)

pCustomInt :: Parser Custom
pCustomInt = CustomInt <$ pSymbol "int" <*> pSignedInt

pCustomBytes :: Parser Custom
pCustomBytes = (CustomBytes . bytesFromString) <$ pSymbol "bytes" <*> pString

pCustomName :: Parser Custom
pCustomName = CustomName <$ pSymbol "name" <* pToken '@' <*> pId

pCustomLink :: Parser Custom
pCustomLink = CustomLink <$ pSymbol "link" <* pToken '@' <*> pId <*> pDeclKind

pCustomDecl :: Parser Custom
pCustomDecl = CustomDecl <$ pSymbol "decl" <*> pDeclKind <*> pSome pCustom

pDeclKind :: Parser DeclKind
pDeclKind =
  DeclKindCustom <$ pToken '@' <*> pId
    <|> DeclKindBytes
    <$ pSymbol "bytes"
    <|> DeclKindCode
    <$ P.try (pSymbol "code")
    <|> DeclKindCon
    <$ pSymbol "con"
    <|> DeclKindExtern
    <$ P.try (pSymbol "extern")
    <|> DeclKindExternType
    <$ pSymbol "externtype"
    <|> DeclKindImport
    <$ pSymbol "import"
    <|> DeclKindKind
    <$ pSymbol "kind"
    <|> DeclKindModule
    <$ pSymbol "module"
    <|> DeclKindName
    <$ pSymbol "name"
    <|> DeclKindValue
    <$ pSymbol "value"
