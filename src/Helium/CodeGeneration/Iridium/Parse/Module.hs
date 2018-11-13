module Helium.CodeGeneration.Iridium.Parse.Module where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Custom
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Method
import Helium.CodeGeneration.Iridium.Data

pCustomDeclaration :: Parser CustomDeclaration
pCustomDeclaration = CustomDeclaration <$ pToken ':' <* pWhitespace <*> pDeclKind

pDataTypeConstructorDeclaration :: Parser (Declaration DataTypeConstructorDeclaration)
pDataTypeConstructorDeclaration = pDeclaration f
  where
    f "constructor" decl = (decl . DataTypeConstructorDeclaration) <$> pArguments pType
    f _ _ = pError "expected constructor declaration"

pDataType :: Parser DataType
pDataType = DataType <$ pWhitespace <* pToken '{' <*> pSome (pWhitespace *> pDataTypeConstructorDeclaration) pSep
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      if c == '}' then do
        pChar
        return False
      else
        return True

pDeclaration :: (String -> (forall a . a -> Declaration a) -> Parser b) -> Parser b
pDeclaration f = do
  customs <- pCustoms
  (vis, key) <- pDeclarationVisibilityAndKeyword
  pToken '@'
  name <- pId
  f key (Declaration name vis customs)

pDeclarationVisibilityAndKeyword :: Parser (Visibility, String)
pDeclarationVisibilityAndKeyword = do
  key <- pKeyword
  if key == "export" then do
    key' <- pKeyword
    return (Exported, key')
  else
    return (Private, key)

pModule :: Parser Module
pModule = do
  pSymbol "module"
  pWhitespace
  name <- pId
  pWhitespace
  pSymbol "import"
  pWhitespace
  dependencies <- pArguments pId
  pWhitespace
  let emptyModule = Module name dependencies [] [] [] []
  decls <- pSome pModuleDeclaration (not <$ pWhitespace <*> isEndOfFile)
  return $ foldr (\f m -> f m) emptyModule decls

pModuleDeclaration :: Parser (Module -> Module)
pModuleDeclaration = pDeclaration f
  where
    f :: String -> (forall a . a -> Declaration a) -> Parser (Module -> Module)
    f "custom" decl = addCustom . decl <$> pCustomDeclaration
    f "data" decl = addDataType . decl <$> pDataType
    f "declare" decl = addAbstract . decl <$> pAbstractMethod
    f "define" decl = addMethod . decl <$> pMethod

parseModule :: String -> Either ParseError Module
parseModule = parse pModule

addCustom :: Declaration CustomDeclaration -> Module -> Module
addCustom c m = m{ moduleCustoms = c : moduleCustoms m }

addDataType :: Declaration DataType -> Module -> Module
addDataType d m = m{ moduleDataTypes = d : moduleDataTypes m }

addAbstract :: Declaration AbstractMethod -> Module -> Module
addAbstract a m = m{ moduleAbstractMethods = a : moduleAbstractMethods m }

addMethod :: Declaration Method -> Module -> Module
addMethod f m = m{ moduleMethods = f : moduleMethods m }
