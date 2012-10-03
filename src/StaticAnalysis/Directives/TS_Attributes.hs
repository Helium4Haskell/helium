{-| Module      :  TS_Attributes
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Substitute the attributes in a user defined error message.
	
	(directives based on "Scripting the Type Inference Process", ICFP 2003)
-}

module StaticAnalysis.Directives.TS_Attributes where

import StaticAnalysis.Inferencers.BindingGroupAnalysis (Assumptions)
import StaticAnalysis.Miscellaneous.ConstraintInfo (ConstraintSet, LocalInfo, assignedType, self)
import StaticAnalysis.Messages.Messages             (MessageBlock(..))
import Top.Types            (Tp, toTpScheme)
import Utils.OneLiner       (OneLineTree)
import Syntax.UHA_Syntax    (Range) 
import StaticAnalysis.Miscellaneous.UHA_Source (rangeOfSource, oneLinerSource)
import Utils.Utils          (internalError)
import Data.Char            (isAlphaNum)

type MetaVariableTable = [(String, MetaVariableInfo)]

data MetaVariableInfo = MetaVarInfo
   { getConstraintSet :: ConstraintSet
   , getAssumptions   :: Assumptions
   , getLocalInfo     :: LocalInfo
   }
   
metaVarInfo :: ConstraintSet -> Assumptions -> LocalInfo -> MetaVariableInfo
metaVarInfo = MetaVarInfo

getMaybeType :: MetaVariableInfo -> Maybe Tp
getMaybeType = assignedType . getLocalInfo

getType :: MetaVariableInfo -> Tp
getType = 
   let err = internalError "TS_MetaInfo" "getType" "no type was assigned at the current local info" 
   in maybe err id . getMaybeType
   
getRange :: MetaVariableInfo -> Range
getRange = rangeOfSource . self . getLocalInfo
   
getOneLineTree :: MetaVariableInfo -> OneLineTree
getOneLineTree = oneLinerSource . self . getLocalInfo
   
-- attributes

type AttributeTable = [(String, MetaVariableInfo -> MessageBlock)] -- ?????

data Attribute = LocalAttribute String
               | MetaVarAttribute String String
   deriving Eq

instance Show Attribute where 
   show attribute = 
      case attribute of
         LocalAttribute s      -> "@" ++ s ++ "@"
         MetaVarAttribute mv s -> "@" ++ mv ++ "." ++ s ++ "@"

parseWithAttributes :: String -> [Either Attribute String]
parseWithAttributes [] = []
parseWithAttributes xs = 
   let (begin, rest) = span (/= '@') xs
   in case rest of 
         []          -> [Right begin]
         '@' : rest1 -> 
            let (variableName, as) = span isAlphaNum rest1
            in case as of 
                  '@' : rest2 -> Right begin : Left (LocalAttribute variableName) : parseWithAttributes rest2
                  '.' : rest2 ->
                     let (fieldName, bs) = span isAlphaNum rest2
                     in case bs of
                           '@' : rest3 -> Right begin : Left (MetaVarAttribute variableName fieldName) : parseWithAttributes rest3
                           _ -> Right (begin++"@"++variableName++"."++fieldName) : parseWithAttributes as
                  _ -> Right (begin++"@"++variableName) : parseWithAttributes as

findAttributes :: String -> [Attribute]
findAttributes s = [ a | Left a <- parseWithAttributes s ]

changeAttributes :: (Attribute -> Attribute) -> String -> String
changeAttributes f = concatMap (either (show . f) id) . parseWithAttributes

substituteAttributes :: (Attribute -> MessageBlock) -> String -> MessageBlock
substituteAttributes f = MessageCompose . map (either f MessageString) . parseWithAttributes

toMessageBlock :: [(String, MessageBlock)] -> MetaVariableInfo -> MetaVariableTable -> Attribute -> MessageBlock
toMessageBlock locals metaInfo table attribute =
   case attribute of
      LocalAttribute s -> 
         let err = internalError "TS_Attributes.hs" "toMessageBlock" ("unknown local attribute " ++ s) 
         in maybe err id (lookup s locals)
      MetaVarAttribute s f
         | s == "expr" -> findAttributeField f s metaInfo
         | otherwise ->
              let err = internalError "TS_Attributes.hs" "toMessageBlock" ("unknown combination " ++ s ++ "." ++ f)                  
              in maybe err (findAttributeField f s) (lookup s table)

-- Added parameter s for diagnostic reasons, and renamed the old s to f.              
findAttributeField :: String -> String -> MetaVariableInfo -> MessageBlock
findAttributeField f s = 
   let err = internalError "TS_Attributes.hs" "toMessageBlock" ("unknown attribute field " ++ f ++ " of metavariable " ++ s)
   in maybe err id (lookup f attributeFieldTable)

attributeFieldTable :: [(String, MetaVariableInfo -> MessageBlock)]
attributeFieldTable = 
   [ ("type" , MessageType . toTpScheme . getType)
   , ("pp"   , MessageOneLineTree . getOneLineTree)
   , ("range", MessageRange . getRange)
   ]
