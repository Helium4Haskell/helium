module Helium.CodeGeneration.Iridium.Parse.Type where

import Control.Applicative
import Data.Char
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Type
import Lvm.Common.Id (Id, idFromString)
import Lvm.Core.Type
import qualified Text.Parsec as P

pTypeVariable :: Parser Int
pTypeVariable = pLexeme $ P.string "v$" *> P.option "" (P.many1 P.lower) *> number

pUniquenessVariable :: Parser Int
pUniquenessVariable = P.string "u$" *> number

pQuantor :: Parser (Kind, Int)
pQuantor = (,) KStar <$> pTypeVariable <|> (,) KAnn <$> pUniquenessVariable

pTypeForall' :: (Kind, Int) -> Type -> Parser Type
pTypeForall' (k, q) t = return $ TForall (Quantor q Nothing) k t

pTypeForall :: Parser Type
pTypeForall = pSymbol "forall" *> ((\(k,q) _ t -> TForall (Quantor q Nothing) k t) <$> pQuantor <*> pToken '.' <*> pType)

pType :: Parser Type
pType = pTypeForall <|> pFunctionType

pFunctionType :: Parser Type
pFunctionType = foldr1 (TAp . TAp (TCon TConFun)) <$> P.sepBy1 (pTypeForall <|> pTypeAp) (pSymbol "->")

pTypeAp :: Parser Type
pTypeAp = foldl TAp <$> pTypeAtom <*> P.many pTypeAtom'

pTypeAtom :: Parser Type
pTypeAtom = pTypeAtomAnn <|> pTypeAtom'

pTypeAtom' :: Parser Type
pTypeAtom' = pTypeAtomList <|> pTypeAtomT <|> pTypeAtomTypeVariable <|> pTypeAtomDataType

pTypeAtomTypeVariable :: Parser Type
pTypeAtomTypeVariable = TVar <$> pTypeVariable

pTypeAtomAnn :: Parser Type
pTypeAtomAnn = (typeToStrict <$ pToken '!' <*> pTypeAtomAnn') <|> pTypeAtomAnn'

pTypeAtomAnn' :: Parser Type
pTypeAtomAnn' = ((\a t -> TAp (TUniq a) t) <$> (Shared <$ pSymbol "w:" <|> Unique <$ pSymbol "1:" <|> (UVar <$> pUniquenessVariable <* pToken ':')) <*> pTypeAtom') <|> pTypeAtom'

pTypeAtomList :: Parser Type
pTypeAtomList = pBrackets pTypeAtomMaybeList

pTypeAtomMaybeList :: Parser Type
pTypeAtomMaybeList = let tcon = (TCon $ TConDataType $ idFromString "[]") in TAp tcon <$> pType <|> return tcon

pTypeAtomT :: Parser Type
pTypeAtomT = pParentheses (pTypeAtomTypeClass <|> pType <|> pTypeAtomTuple)

pTypeAtomTypeClass :: Parser Type
pTypeAtomTypeClass = (TCon . TConTypeClassDictionary) <$ pSymbol "@dictionary" <*> pNameDataType

pTypeAtomTuple :: Parser Type
pTypeAtomTuple = (TCon . TConTuple . length') <$> P.many (P.satisfy ((',') ==))
  where
    -- arity is the number of types the tuple contains, for example (t1,t2) = 2 but () = 0
    length' tp = case length tp of
      0 -> 0
      x -> x + 1

pTypeAtomDataType :: Parser Type
pTypeAtomDataType = (TCon . TConDataType) <$> pNameDataType

pNameDataType :: Parser Id
pNameDataType = pLexeme $ ((idFromString .) . (:)) <$> P.satisfy vstart <*> pSome (P.satisfy valid) <|> idFromString <$> pString
  where
    valid c =
      isAlphaNum c
        || c == '.'
        || c == '_'
        || c == '$'
    vstart c = isUpper c || c == '$' || c == '.'

pFloatPrecision :: Parser FloatPrecision
pFloatPrecision = Float64 <$ pSymbol "64" <|> Float64 <$ pSymbol "32"

pNamedTypeAtom :: (Id -> Type -> b) -> Parser b
pNamedTypeAtom a = a <$ pToken '@' <*> pNameDataType <* pToken ':' <*> pTypeAtom

pDataTypeConstructor :: Parser DataTypeConstructor
pDataTypeConstructor = pNamedTypeAtom DataTypeConstructor

pInstantiation :: Parser [Type]
pInstantiation = P.many $ pBraces pType
