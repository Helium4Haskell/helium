module Helium.CodeGeneration.Iridium.Parse.Method where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data

pMethod :: Parser Method
pMethod = (\args rettype (b:bs) -> Method args rettype b bs) <$> pArguments pLocal <* pToken ':' <* pWhitespace <*> pType <* pWhitespace <* pToken '{' <* pWhitespace <*> pSome pBlock pSep
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

pBlock :: Parser Block
pBlock = Block <$> pId <* pToken ':' <* pWhitespace <*> pInstruction <* pWhitespace

pAbstractMethod :: Parser AbstractMethod
pAbstractMethod = AbstractMethod <$ pToken ':' <* pWhitespace <*> pFunctionType
