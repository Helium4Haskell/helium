module Helium.CodeGeneration.Iridium.Parse.Custom where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.Lvm.Core.Module
import Helium.Lvm.Common.Byte(bytesFromString)

pCustoms :: Parser [Custom]
pCustoms = do
  c <- lookahead
  if c == '#' then do
    pChar
    custom <- pCustom
    pWhitespace
    (custom :) <$> pCustoms
  else
    return []

pCustom :: Parser Custom
pCustom = do
  pToken '['
  pWhitespace
  c <- lookahead
  if c == ']' then do
    pChar
    return CustomNothing
  else do
    keyword <- pName
    pWhitespace
    result <- case keyword of
      "int" -> CustomInt <$> pSignedInt
      "bytes" -> (CustomBytes . bytesFromString) <$> pString
      "name" -> CustomName <$ pToken '@' <*> pId
      "link" -> CustomLink <$ pToken '@' <*> pId <* pWhitespace <*> pDeclKind
      "decl" -> CustomDecl <$> pDeclKind <* pWhitespace <*> pSome pCustom ((== '[') <$ pWhitespace <*> lookahead)
      _ -> pError "expected keyword for custom declaration"
    pWhitespace
    pToken ']'
    return result

pDeclKind :: Parser DeclKind
pDeclKind = do
  c <- lookahead
  if c == '@' then do
    pChar
    DeclKindCustom <$> pId
  else do
    keyword <- pKeyword
    case keyword of
      "name" -> return DeclKindName
      "kind" -> return DeclKindKind
      "bytes" -> return DeclKindBytes
      "code" -> return DeclKindCode
      "value" -> return DeclKindValue
      "con" -> return DeclKindCon
      "import" -> return DeclKindImport
      "module" -> return DeclKindModule
      "extern" -> return DeclKindExtern
      "externtype" -> return DeclKindExternType
      _ -> pError "expected declaration kind"
