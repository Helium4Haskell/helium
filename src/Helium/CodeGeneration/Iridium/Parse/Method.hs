module Helium.CodeGeneration.Iridium.Parse.Method where

import Control.Applicative
import Data.Maybe
import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Lvm.Common.Id (idFromString)
import Lvm.Core.Type
import qualified Text.Parsec as P

pMethod :: Parser Method
pMethod =
  createMethod <$> P.optionMaybe (pToken (':') *> pBraces pType <* pToken ('$'))
    <*> pParentheses (pMethodArguments)
    <*> pAnnotations
    <* pToken ':'
    <*> pType
    <*> (pMethodBlocks <|> pMethodExpression)

createMethod :: Maybe Type -> [Either Quantor Local] -> [Annotation] -> Type -> Either Expr [Block] -> Method
createMethod tp args an rt be = getBlocks rt (Method (convertType tp args rt) args rt an) be

getBlocks :: Type -> (Block -> [Block] -> b) -> Either Expr [Block] -> b
getBlocks _ m (Right (x : xs)) = m x xs
getBlocks rt m (Left expr) = m (expresstionToBlock rt expr) []

convertType :: Maybe Type -> [Either Quantor Local] -> Type -> Type
convertType tp args rt = fromMaybe (typeFromFunctionType $ FunctionType (map toArg args) rt) tp
  where
    toArg (Right (Local _ t)) = Right t
    toArg (Left quantor) = Left quantor

expresstionToBlock :: Type -> Expr -> Block
expresstionToBlock rt expr =
  let result = idFromString "result"
   in Block (idFromString "entry") (Let result expr $ Return $ VarLocal $ Local result $ typeToStrict rt)

pMethodBlocks :: Parser (Either a [Block])
pMethodBlocks = pBraces (Right <$> P.many1 pBlock)

pMethodExpression :: Parser (Either Expr a)
pMethodExpression = Left <$ pToken '=' <*> pExpression

pMethodArguments :: Parser ([Either Quantor Local])
pMethodArguments = P.sepBy (pMethodArgument) (pToken ',')

pMethodArgument :: Parser (Either Quantor Local)
pMethodArgument = Right <$> pLocal <|> Left <$ pSymbol "forall" <*> pQuantor

pBlock :: Parser Block
pBlock = Block <$> pId <* pToken ':' <*> pInstruction

pAbstractMethod :: Parser AbstractMethod
pAbstractMethod = AbstractMethod <$> (pBrackets pUnsignedInt) <* pToken ':' <*> pBraces pType <*> pAnnotations

pAnnotations :: Parser [Annotation]
pAnnotations = P.option [] (pBrackets (P.sepBy pAnnotation (pToken ',')))

pAnnotation :: Parser Annotation
pAnnotation = pAnnotateTrampoline <|> pAnnotateCallConvention <|> pAnnotateFakeIO

pAnnotateTrampoline :: Parser Annotation
pAnnotateTrampoline = AnnotateTrampoline <$ pSymbol "trampoline"

pAnnotateCallConvention :: Parser Annotation
pAnnotateCallConvention =
  AnnotateCallConvention <$ pSymbol "callconvention" <* pToken ':'
    <*> (CCC <$ pToken 'c' <|> CCFast <$ pSymbol "fast" <|> CCPreserveMost <$ pSymbol "preserve_most")

pAnnotateFakeIO :: Parser Annotation
pAnnotateFakeIO = AnnotateFakeIO <$ pSymbol "fake_io"
