{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Helium.CodeGeneration.Iridium.Parse.Module where

import Control.Applicative
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Custom
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Parse.Method
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Lvm.Common.Id (Id)
import Lvm.Core.Module (Field (..))
import System.Exit
import qualified Text.Parsec as P

--parseModule :: String -> Either ParseError Module
parseModule :: FilePath -> String -> Either P.ParseError Module
parseModule path text = P.parse pModule path text

parseModuleIO :: FilePath -> IO Module
parseModuleIO path = readFile path >>= parseModuleIO' path

parseModuleIO' :: FilePath -> String -> IO Module
parseModuleIO' fullName contents =
  case parseModule fullName contents of
    Left err -> do
      putStrLn $ "Failed to parse Iridium file " ++ show fullName
      print err
      exitWith (ExitFailure 1)
    Right ir -> return ir

newtype DeclarationL = DeclarationL {dL :: forall a. Id -> a -> Declaration a}

pCustomDeclaration :: Parser CustomDeclaration
pCustomDeclaration = CustomDeclaration <$ pToken ':' <*> pDeclKind

pDataTypeConstructorDeclaration :: Parser (Declaration DataTypeConstructorDeclaration)
pDataTypeConstructorDeclaration = pDeclaration f
  where
    f :: DeclarationL -> Parser (Declaration DataTypeConstructorDeclaration)
    f (dL -> decl) =
      (\n tp fs -> decl n (DataTypeConstructorDeclaration tp fs)) <$ pSymbol "constructor"
        <*> pDeclarationName
        <* pToken (':')
        <*> pBraces pType
        <*> pFields

pDataType :: Parser DataType
pDataType = DataType <$> pBraces (P.many pDataTypeConstructorDeclaration)

pFields :: Parser [Field]
pFields = P.option [] (pParentheses (P.sepBy pField (pToken ',')))

pField :: Parser Field
pField = Field <$> pId

pTypeSynonym :: Parser TypeSynonym
pTypeSynonym = TypeSynonym <$ pToken '=' <*> pBraces pType

pDeclaration :: (DeclarationL -> Parser b) -> Parser b
pDeclaration f = pEmptyDeclaration >>= f

pVisibility :: Parser Visibility
pVisibility = P.option (Private) (ExportedAs <$ pSymbol "export_as" <* pToken '@' <*> pId)

pOrigin :: Parser (Maybe Id)
pOrigin = P.optionMaybe (pSymbol "from" *> pId)

pEmptyDeclaration :: Parser DeclarationL
pEmptyDeclaration = (\b c d -> DeclarationL (\e -> Declaration e c d b)) <$> pCustoms <*> pVisibility <*> pOrigin

pDeclarationName :: Parser Id
pDeclarationName = pToken '@' *> pId

pModuleDeclaration' :: Parser (Module -> Module)
pModuleDeclaration' = pDeclaration f
  where
    f :: DeclarationL -> Parser (Module -> Module)
    f (dL -> decl) =
      ((addCustom .) . decl) <$ pSymbol "custom" <*> pDeclarationName <*> pCustomDeclaration
        <|> ((addDataType .) . decl) <$ P.try (pSymbol "data") <*> pDeclarationName <*> pDataType
        <|> ((addAbstract .) . decl) <$ P.try (pSymbol "declare") <*> pDeclarationName <*> pAbstractMethod
        <|> ((addTypeSynonym .) . decl) <$ pSymbol "type" <*> pDeclarationName <*> pTypeSynonym
        <|> ((addMethod .) . decl) <$ pSymbol "define" <*> pDeclarationName <*> pMethod

pModule :: Parser Module
pModule = foldr id <$> pEmptyModule <*> pSome pModuleDeclaration'

pEmptyModule :: Parser Module
pEmptyModule =
  (\name dependencies -> Module name dependencies [] [] [] [] [])
    <$ pSymbol "module" <*> pId <* pSymbol "import" <*> pArguments pId

addCustom :: Declaration CustomDeclaration -> Module -> Module
addCustom c m = m {moduleCustoms = c : moduleCustoms m}

addDataType :: Declaration DataType -> Module -> Module
addDataType d m = m {moduleDataTypes = d : moduleDataTypes m}

addAbstract :: Declaration AbstractMethod -> Module -> Module
addAbstract a m = m {moduleAbstractMethods = a : moduleAbstractMethods m}

addMethod :: Declaration Method -> Module -> Module
addMethod f m = m {moduleMethods = f : moduleMethods m}

addTypeSynonym :: Declaration TypeSynonym -> Module -> Module
addTypeSynonym ts m = m {moduleTypeSynonyms = ts : moduleTypeSynonyms m}
