module Helium.CodeGeneration.Iridium.Parse.Type where

import Control.Applicative
import Control.Monad (ap)
import Data.Char
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Type
import Lvm.Common.Id (Id, idFromString)
import Lvm.Core.Type
import qualified Text.Parsec as P

-- We first parse the type of the function, then possible uniqueness constraints follow
pConstraintType :: Parser Type
pConstraintType = ap maybe TQTy <$> pType <*> P.optionMaybe (pToken (',') *> pTQTy)

pTQTy :: Parser [(UAnn, UAnn)]
pTQTy = pBrackets (P.sepBy pConstraint (pToken ','))

pConstraint :: Parser (UAnn, UAnn)
pConstraint = (,) <$> pLexeme pAnnVar <* pSymbol "<=" <*> pLexeme pAnnVar

pTypeVariable :: Parser Int
pTypeVariable = pLexeme $ P.string "v$" *> P.option "" (P.many1 P.lower) *> number

pUniquenessVariable :: Parser Int
pUniquenessVariable = P.string "u$" *> number

pUniqueQuantor :: Parser (Maybe String -> Quantor)
pUniqueQuantor = Quantor <$> pUniquenessVariable <*> pure KAnn

pTypeQuantor :: Parser (Maybe String -> Quantor)
pTypeQuantor = Quantor <$> pTypeVariable <*> pure KStar

pQuantor :: Parser Quantor
pQuantor = ($ Nothing) <$> (pUniqueQuantor <|> pTypeQuantor)

pForall :: Parser Type
pForall = TForall <$ pSymbol "forall" <*> pQuantor <* pToken '.' <*> pType

pType :: Parser Type
pType = pFunctionType <|> pForall

pFun :: Parser (Type -> Type -> Type)
pFun = ((TAp .) . TAp) <$ pSymbol "->" <*> pArrow

pArrow :: Parser Type
pArrow = P.option arr (flip addUAnnToType arr <$ pToken ':' <*> pUAnn)
  where arr = TCon TConFun

pFunctionType :: Parser Type
pFunctionType = P.chainr1 pTypeAp pFun

pTypeAp :: Parser Type
pTypeAp = foldl1 TAp <$> P.many1 pTypeAtom

pTypeAtom :: Parser Type
pTypeAtom = pTypeAtomAnn pTypeAtom'

pTypeAtom' :: Parser Type
pTypeAtom' = pTypeAtomList <|> pTypeAtomT <|> pTypeAtomTypeVariable <|> pTypeAtomDataType

pTypeAtomTypeVariable :: Parser Type
pTypeAtomTypeVariable = TVar <$> pTypeVariable

pTypeAtomAnn :: Parser Type -> Parser Type
pTypeAtomAnn p = (typeToStrict <$ pToken '!' <*> pTypeAtomUAnn p) <|> pTypeAtomUAnn p

pTypeAtomUAnn :: Parser Type -> Parser Type
pTypeAtomUAnn p = (addUAnnToType <$> pUAnn <* pToken ':' <*> p) <|> p

pUAnn :: Parser UAnn
pUAnn = (UShared <$ pToken 'w' <|> UUnique <$ pToken '1' <|> pAnnVar)

pAnnVar :: Parser UAnn
pAnnVar = UVar <$> pUniquenessVariable

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
