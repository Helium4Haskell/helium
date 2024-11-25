--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file
-- is distributed under the terms of the BSD3 License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

{-# LANGUAGE LambdaCase #-}

module Helium.Lvm.Core.Parsing.Parser
  ( parseModule
  )
where

import           Control.Monad
import           Data.List
import           Data.Functor
import           Helium.Lvm.Common.Byte
import           Helium.Lvm.Common.Id

import           Helium.Lvm.Core.Expr
import           Helium.Lvm.Core.Parsing.Token         ( Token
                                                , Lexeme(..)
                                                )
import           Helium.Lvm.Core.Parsing.Lexer
import           Helium.Lvm.Core.Type
import           Helium.Lvm.Core.Utils
import           Prelude                 hiding (mod, lex )
import           Text.ParserCombinators.Parsec
                                         hiding ( satisfy )

parseModule
  :: FilePath
  -> [Token]
  -> IO CoreModule
parseModule fname ts = case runParser pmodule () fname ts of
  Left  err -> ioError (userError ("parse error: " ++ show err))
  Right res -> return res

----------------------------------------------------------------
-- Basic parsers
----------------------------------------------------------------
type TokenParser a = GenParser Token () a

----------------------------------------------------------------
-- Program
----------------------------------------------------------------

wrap :: TokenParser a -> TokenParser [a]
wrap p = do
  x <- p
  return [x]

pmodule :: TokenParser CoreModule
pmodule = do
  lexeme LexMODULE
  moduleId <- conid <?> "module name"
  lexeme LexWHERE
  lexeme LexLBRACE
  imports <- pimports <|> return []
  declss <- semiList
    (   wrap (ptopDecl <|> pconDecl <|> pextern <|> pCustomDecl)
    <|> pdata
    <|> ptypeTopDecl
    )
  lexeme LexRBRACE
  lexeme LexEOF
  return $ Module moduleId 0 0 imports $ concat declss

pimports :: TokenParser [Id]
pimports = do
  lexeme LexIMPORT
  imports <- commaParens (conid <?> "module name")
  lexeme LexSEMI
  return imports

----------------------------------------------------------------
-- abstract declarations
----------------------------------------------------------------
{-
pabstract :: TokenParser CoreDecl
pabstract = do
  lexeme LexABSTRACT
  pabstractValue

pabstractValue :: TokenParser (Decl v)
pabstractValue = do
  x             <- pVariableName
  (acc, custom) <- pAttributes
  lexeme LexCOLON
  arity <- lexInt
  lexeme LexASG
  (mid, impid) <- qualifiedVar
  t            <- ptypeDecl
  let access | isImported acc = acc
             | otherwise      = Imported False mid impid DeclKindValue 0 0
  return (DeclAbstract x access (fromIntegral arity) t custom)

pabstractCon :: TokenParser (Decl v)
pabstractCon = do
  x             <- conid
  (acc, custom) <- pAttributes -- ignore access
  lexeme LexASG
  (mid, impid) <- qualifiedCon
  lexeme LexCOLCOL
  t <- ptype
  let access | isImported acc = acc
             | otherwise      = Imported False mid impid DeclKindCon 0 0
  return (DeclCon x access t [] custom)
-}

----------------------------------------------------------------
-- constructor declarations
----------------------------------------------------------------

pconDecl :: TokenParser CoreDecl
pconDecl = do
  lexeme LexCON
  x                <- constructor
  (access, mod, custom) <- pAttributes x constructor
  lexeme LexCOLCOL
  t <- ptype []
  return $ DeclCon x access mod t [] custom

-- constructor info: (@tag, arity)
pConInfo :: TokenParser (Tag, Arity)
pConInfo =
  parens
      (do
        lexeme LexAT
        tag <- lexInt <?> "tag"
        lexeme LexCOMMA
        arity <- lexInt <?> "arity"
        return (fromInteger tag, fromInteger arity)
      )
    <|> do -- :: TypeSig = tag
          tp <- ptypeDecl
          lexeme LexASG
          tag <- lexInt <?> "tag"
          return (fromInteger tag, arityFromType tp)


----------------------------------------------------------------
-- value declarations
----------------------------------------------------------------

ptopDecl :: TokenParser CoreDecl
ptopDecl = do
  x <- pVariableName
  ptopDeclType x

ptopDeclType :: Id -> TokenParser (Decl Expr)
ptopDeclType x = do
  tp <- ptypeDecl
  lexeme LexSEMI
  x2 <- pVariableName
  when (x /= x2) $ fail
    (  "identifier for type signature "
    ++ stringFromId x
    ++ " doesn't match the definition"
    ++ stringFromId x2
    )
  (access, mod, custom, expr) <- pbindTopRhs x pVariableName
  return (DeclValue x access mod tp expr custom)

pbindTopRhs :: Id -> TokenParser Id -> TokenParser (Access, Maybe Id, [Custom], Expr)
pbindTopRhs name palias =
  do
      (access, mod, custom) <- pAttributes name palias
      lexeme LexASG
      body <- pexpr []
      return (access, mod, custom, body)
    <?> "declaration"

pbind :: QuantorNames -> TokenParser Bind
pbind quantors = do
  var <- variable quantors
  lexeme LexASG
  Bind var <$> pexpr quantors

----------------------------------------------------------------
-- data declarations
----------------------------------------------------------------

makeCustomBytes :: String -> Bytes -> Custom
makeCustomBytes k bs = CustomDecl (customDeclKind k) [CustomBytes bs]

customKind :: Kind -> Custom
customKind = makeCustomBytes "kind" . bytesFromString . show

pdata :: TokenParser [CoreDecl]
pdata = do
  lexeme LexDATA
  x    <- typeid
  (quantorNames, quantors) <- pquantors []
  let args     = reverse $ take (length quantors) [0..]
      kind     = foldr (KFun . const KStar) KStar args
      datadecl = DeclCustom x (Export x) Nothing customData [customKind kind]
  do
      lexeme LexASG
      let t1 = foldl TAp (TCon $ TConDataType x) (map TVar args)
      cons <- sepBy1 (pconstructor quantorNames t1) (lexeme LexBAR)
      let con (cid, t2) = DeclCon cid (Export cid) Nothing t2 [] [CustomLink x customData]
      return (datadecl : map con cons)
    <|> {- empty data types -}
        return [datadecl]

pconstructor :: QuantorNames -> Type -> TokenParser (Id, Type)
pconstructor quantors tp = do
  x    <- constructor
  args <- many (ptypeAtom quantors)
  return (x, foldr (\t1 t2 -> TAp (TAp (TCon TConFun) t1) t2) tp args)

----------------------------------------------------------------
-- type declarations
----------------------------------------------------------------

ptypeTopDecl :: TokenParser [CoreDecl]
ptypeTopDecl = do
  s <- (TypeSynonymAlias <$ lexeme LexTYPE) <|> (TypeSynonymNewtype <$ lexeme LexNEWTYPE)
  x <- typeid
-- ; args <- many lexTypeVar
  lexeme LexASG
  tp <- ptype []
  return [DeclTypeSynonym x (Export x) Nothing s tp []] -- TODO: Handle type arguments

----------------------------------------------------------------
-- Custom
----------------------------------------------------------------
pCustomDecl :: TokenParser CoreDecl
pCustomDecl = do
  lexeme LexCUSTOM
  kind              <- pdeclKind
  x                 <- customid
  (access, mod, customs) <- pAttributes x customid
  return (DeclCustom x access mod kind customs)

pAttributes :: Id -> TokenParser Id -> TokenParser (Access, Maybe Id, [Custom])
pAttributes name palias =
  do
      lexeme LexCOLON
      mod <- pfrom
      access  <- paccess name palias
      customs <- pcustoms
      return (access, mod, customs)
    <|> return (Private, Nothing, [])

paccess :: Id -> TokenParser Id -> TokenParser Access
paccess name palias =
  do
      lexeme LexEXPORT
      alias <- palias <|> return name
      return $ Export alias
    <|> return Private

pfrom :: TokenParser (Maybe Id)
pfrom = do
    lexeme LexFROM
    mod <- identifier lexString <|> conid
    return (Just mod)
  <|> return Nothing

pcustoms :: TokenParser [Custom]
pcustoms =
  do
      lexeme LexLBRACKET
      customs <- pcustom `sepBy` lexeme LexCOMMA
      lexeme LexRBRACKET
      return customs
    <|> return []

pcustom :: TokenParser Custom
pcustom =

  CustomInt
    .   fromInteger
    <$> lexInt
    <|> do
          CustomBytes . bytesFromString <$> lexString
    <|> do
          x <- pVariableName <|> constructor
          return (CustomName x)
    <|> do
          lexeme LexNOTHING
          return CustomNothing
    <|> do
          lexeme LexCUSTOM
          kind <- pdeclKind
          do
              x <- customid
              return (CustomLink x kind)
            <|> do
                  CustomDecl kind <$> pcustoms
    <?> "custom value"

pdeclKind :: TokenParser DeclKind
pdeclKind =
  makeDeclKind
    <$> varid
    <|> do
          lexeme LexTYPE
          return DeclKindTypeSynonym
    <|> toEnum
    .   fromInteger
    <$> lexInt
    <|> customDeclKind
    <$> lexString
    <?> "custom kind"

----------------------------------------------------------------
-- Expressions
----------------------------------------------------------------

pexpr :: QuantorNames -> TokenParser Expr
pexpr quantors =
  do
      lexeme LexBSLASH
      strict <- lexeme LexEXCL $> True <|> return False
      arg    <- variable quantors
      lexeme LexRARROW
      Lam strict arg <$> pexpr quantors
    <|> do
          lexeme LexLET
          binds <- semiBraces (pbind quantors)
          lexeme LexIN
          Let (Rec binds) <$> pexpr quantors
    <|> do
          lexeme LexCASE
          var <- pVariableName
          lexeme LexOF
          Match var <$> palts quantors
    <|> do
          lexeme LexLETSTRICT
          binds <- semiBraces (pbind quantors)
          lexeme LexIN
          expr <- pexpr quantors
          return (foldr (Let . Strict) expr binds)
    <|> do
          lexeme LexFORALL
          (quantors', quantor) <- pquantor quantors
          let kind = KStar
          lexeme LexDOT
          Forall quantor kind <$> pexpr quantors'
    <|> pexprAp quantors
    <?> "expression"

wildId :: Id
wildId = idFromString "_"

pexprAp :: QuantorNames -> TokenParser Expr
pexprAp quantors = do
  e1   <- patom quantors
  args <- many $ pApArg quantors
  return (foldl (flip id) e1 args)

pApArg :: QuantorNames -> TokenParser (Expr -> Expr)
pApArg quantors =
  do
      atom <- patom quantors
      return (`Ap` atom)
    <|> do
          lexeme LexLBRACE
          tp <- ptype quantors
          lexeme LexRBRACE
          return (`ApType` tp)

patom :: QuantorNames -> TokenParser Expr
patom quantors =
  Var
    <$> varid
    <|> Con
    .   ConId
    <$> conid
    <|> Lit
    <$> pliteral
    <|> parenExpr quantors
    <|> listExpr quantors
    <?> "atomic expression"


listExpr :: QuantorNames -> TokenParser Expr
listExpr quantors = do
  lexeme LexLBRACKET
  exprs <- sepBy (pexpr quantors) (lexeme LexCOMMA)
  lexeme LexRBRACKET
  return (foldr cons nil exprs)
 where
  cons = Ap . Ap (Con (ConId (idFromString ":")))
  nil  = Con (ConId (idFromString "[]"))

parenExpr :: QuantorNames -> TokenParser Expr
parenExpr quantors = do
  lexeme LexLPAREN
  expr <-
    Var
    <$> opid
    <|> Con
    .   ConId
    <$> conopid
    <|> do
          lexeme LexAT
          arity <- lexInt <?> "arity"
          return (Con (ConTuple (fromInteger arity)))
    <|> do
          exprs <- pexpr quantors `sepBy` lexeme LexCOMMA
          case exprs of
            [expr] -> return expr
            _ ->
              let con = Con (ConTuple (length exprs))
                  tup = foldl Ap con exprs
              in  return tup
  lexeme LexRPAREN
  return expr

pliteral :: TokenParser Literal
pliteral =
  pnumber id id
    <|> LitBytes
    .   bytesFromString
    <$> lexString
    <|> do
          c <- lexChar
          return (LitInt (fromEnum c) IntTypeChar)
    <|> do
          lexeme LexDASH
          pnumber negate negate
    <?> "literal"

pnumber :: (Int -> Int) -> (Double -> Double) -> TokenParser Literal
pnumber signint signdouble =
  do
      i <- lexInt
      return (LitInt (signint (fromInteger i)) IntTypeInt)
    <|> LitDouble
    .   signdouble
    <$> lexDouble

----------------------------------------------------------------
-- alternatives
----------------------------------------------------------------
palts :: QuantorNames -> TokenParser Alts
palts quantors = do
  lexeme LexLBRACE
  paltSemis quantors

paltSemis :: QuantorNames -> TokenParser Alts
paltSemis quantors =
  do
      alt <- paltDefault quantors
      optional (lexeme LexSEMI)
      lexeme LexRBRACE
      return [alt]
    <|> do
          alt <- palt quantors
          do
              lexeme LexSEMI
              do
                  alts <- paltSemis quantors
                  return (alt : alts)
                <|> do
                      lexeme LexRBRACE
                      return [alt]
            <|> do
                  lexeme LexRBRACE
                  return [alt]

palt :: QuantorNames -> TokenParser Alt
palt quantors = do
  pat <- ppat quantors
  lexeme LexRARROW
  Alt pat <$> pexpr quantors

pInstantiation :: QuantorNames -> TokenParser [Type]
pInstantiation quantors = many (lexeme LexLBRACE *> ptype quantors <* lexeme LexRBRACE)

ppat :: QuantorNames -> TokenParser Pat
ppat quantors = ppatCon quantors <|> ppatLit <|> ppatParens quantors

ppatParens :: QuantorNames -> TokenParser Pat
ppatParens quantors = do
  lexeme LexLPAREN
  do
      lexeme LexAT
      arity <- lexInt <?> "arity"
      lexeme LexRPAREN
      ids <- many bindid
      return (PatCon (ConTuple (fromInteger arity)) [] ids)
    <|> do
          x <- conopid
          lexeme LexRPAREN
          instantiation <- pInstantiation quantors
          ids           <- many bindid
          return (PatCon (ConId x) instantiation ids)
    <|> do
          pat <- ppat quantors <|> ppatTuple
          lexeme LexRPAREN
          return pat

ppatCon :: QuantorNames -> TokenParser Pat
ppatCon quantors = do
  x <- conid <|> do
    lexeme LexLBRACKET
    lexeme LexRBRACKET
    return (idFromString "[]")
  instantiation <- pInstantiation quantors
  args          <- many bindid
  return (PatCon (ConId x) instantiation args)

ppatLit :: TokenParser Pat
ppatLit = PatLit <$> pliteral

ppatTuple :: TokenParser Pat
ppatTuple = do
  ids <- bindid `sepBy` lexeme LexCOMMA
  return (PatCon (ConTuple (length ids)) [] ids)

paltDefault :: QuantorNames -> TokenParser Alt
paltDefault quantors = do
  lexeme LexDEFAULT
  lexeme LexRARROW
  Alt PatDefault <$> pexpr quantors

wildcard :: TokenParser Id
wildcard = identifier (return "_")

----------------------------------------------------------------
-- externs
----------------------------------------------------------------
pextern :: TokenParser CoreDecl
pextern =
  do
      lexeme LexEXTERN
      linkConv      <- plinkConv
      callConv      <- pcallConv
      x             <- varid
      m             <- lexString <|> return (stringFromId x)
      (mname, name) <- pExternName m
      tp            <- ptypeDecl
      return (DeclExtern x Private Nothing tp "" linkConv callConv mname name [])
    <|> do
          lexeme LexINSTR
          x  <- varid
          s  <- lexString
          tp <- ptypeDecl
          return
            (DeclExtern x Private Nothing tp "" LinkStatic CallInstr "" (Plain s) [])

------------------

plinkConv :: TokenParser LinkConv
plinkConv =
  do
      lexeme LexSTATIC
      return LinkStatic
    <|> do
          lexeme LexDYNAMIC
          return LinkDynamic
    <|> do
          lexeme LexRUNTIME
          return LinkRuntime
    <|> return LinkStatic

pcallConv :: TokenParser CallConv
pcallConv =
  do
      lexeme LexCCALL
      return CallC
    <|> do
          lexeme LexSTDCALL
          return CallStd
    <|> do
          lexeme LexINSTRCALL
          return CallInstr
    <|> return CallC

pExternName :: String -> TokenParser (String, ExternName)
pExternName mname =
  do
      lexeme LexDECORATE
      name <- lexString
      return (mname, Decorate name)
    <|> do
          lexeme LexORDINAL
          ord <- lexInt
          return (mname, Ordinal (fromIntegral ord))
    <|> do
          name <- lexString
          return (mname, Plain name)
    <|> return ("", Plain mname)


----------------------------------------------------------------
-- types
----------------------------------------------------------------

ptypeDecl :: TokenParser Type
ptypeDecl = do
  lexeme LexCOLCOL
  ptype []

ptype :: QuantorNames -> TokenParser Type
ptype quantors = ptypeFun quantors <|> do
  lexeme LexFORALL
  (quantors', quantor) <- pquantor quantors
  let kind = KStar
  lexeme LexDOT
  TForall quantor kind <$> ptype quantors'

pquantor :: QuantorNames -> TokenParser (QuantorNames, Quantor)
pquantor quantorNames
  =   (\name -> let str = stringFromId name in (str : quantorNames, Quantor $ Just str)) <$> varid
  <|> do
    idx <- lexTypeVar
    when (idx /= length quantorNames) $ fail
      (  "identifier for type argument v$"
      ++ show idx
      ++ " doesn't match the next fresh type argument v$"
      ++ show (length quantorNames)
      )
    return $ (("v$" ++ show idx) : quantorNames, Quantor Nothing)

pquantors :: QuantorNames -> TokenParser (QuantorNames, [Quantor])
pquantors quantorNames
  = do
      (quantorNames', quantor) <- pquantor quantorNames
      (quantorNames'', quantors) <- pquantors quantorNames'
      return (quantorNames'', quantor : quantors)
  <|> return (quantorNames, [])

ptypeFun :: QuantorNames -> TokenParser Type
ptypeFun quantors = chainr1 (ptypeAp quantors) pFun
 where
  pFun = do
    lexeme LexRARROW
    return (\t1 t2 -> TAp (TAp (TCon TConFun) t1) t2)

ptypeAp :: QuantorNames -> TokenParser Type
ptypeAp quantors = do
  atoms <- many1 (ptypeAtom quantors)
  return (foldl1 TAp atoms)

ptypeAtom :: QuantorNames -> TokenParser Type
ptypeAtom quantors =
  do
      x <- typeid
      ptypeStrict (TCon $ TConDataType x)
    <|> do
          -- unnamed type variable
          idx <- lexTypeVar
          let t = TVar $ length quantors - 1 - idx
          when (idx > length quantors) $ fail $ "Unnamed type variable v$" ++ show idx ++ " not in scope"
          ptypeStrict t
    <|> do
          -- named type variable
          name <- varid
          case stringFromId name `elemIndex` quantors of
            Nothing -> fail $ "Named type variable " ++ stringFromId name ++ " not in scope"
            Just idx -> ptypeStrict $ TVar idx
    <|> (listType quantors >>= ptypeStrict)
    <|> ((lexeme LexLPAREN *> parenType quantors <* lexeme LexRPAREN) >>= ptypeStrict)
    <?> "atomic type"

ptypeStrict :: Type -> TokenParser Type
ptypeStrict tp =
  do
      lexeme LexEXCL
      return (TStrict tp)
    <|> return tp

parenType :: QuantorNames -> TokenParser Type
parenType quantors =
  do
      lexeme LexAT
      lexeme LexCOMMA
      commas <- many (lexeme LexCOMMA)
      let arity = length commas + 2
      return $ TCon $ TConTuple $ fromIntegral arity
    <|> do
          lexeme LexAT
          lexeme (LexId "dictionary")
          TCon . TConTypeClassDictionary <$> typeid
    <|> do
          tps <- sepBy (ptype quantors) (lexeme LexCOMMA)
          case tps of
            [tp] -> return tp
            _    -> return (foldl TAp (TCon $ TConTuple $ length tps) tps)

listType :: QuantorNames -> TokenParser Type
listType quantors = do
  lexeme LexLBRACKET
  do
      tp <- ptype quantors
      lexeme LexRBRACKET
      x <- identifier (return "[]")
      return (TAp (TCon $ TConDataType x) tp)
    <|> do
          lexeme LexRBRACKET
          x <- identifier (return "[]")
          return (TCon $ TConDataType x)

----------------------------------------------------------------
-- helpers
----------------------------------------------------------------

semiBraces, commaParens :: TokenParser a -> TokenParser [a]
semiBraces p = braces (semiList p)
commaParens p = parens (sepBy p (lexeme LexCOMMA))

braces, parens :: TokenParser a -> TokenParser a
braces = between (lexeme LexLBRACE) (lexeme LexRBRACE)
parens = between (lexeme LexLPAREN) (lexeme LexRPAREN)

-- terminated or separated
semiList1 :: TokenParser a -> TokenParser [a]
semiList1 p = do
  x <- p
  do
      lexeme LexSEMI
      xs <- semiList p
      return (x : xs)
    <|> return [x]

semiList :: TokenParser a -> TokenParser [a]
semiList p = semiList1 p <|> return []

----------------------------------------------------------------
-- Lexeme parsers
----------------------------------------------------------------

customid :: TokenParser Id
customid =
  varid
    <|> conid
    <|> parens (opid <|> conopid)
    <|> idFromString
    <$> lexString
    <?> "custom identifier"

pVariableName :: TokenParser Id
pVariableName = varid <|> parens opid

variable :: QuantorNames -> TokenParser Variable
variable quantors = do
  name <- pVariableName
  lexeme LexCOLON
  Variable name <$> ptypeAp quantors

opid :: TokenParser Id
opid = identifier lexOp <?> "operator"

varid :: TokenParser Id
varid = identifier lexId <?> "variable"

bindid :: TokenParser Id
bindid = varid {-
  = do{ x <- varid
      ; do{ lexeme LexEXCL
          ; return x {- (setSortId SortStrict id) -}
          }
        <|> return x
      -}

constructor :: TokenParser Id
constructor = conid <|> parens conopid

conopid :: TokenParser Id
conopid =
  identifier lexConOp
    <|> do
          lexeme LexCOLON
          return (idFromString ":")
    <?> "constructor operator"

conid :: TokenParser Id
conid = identifier lexCon <?> "constructor"

typeid :: TokenParser Id
typeid =
  identifier lexCon
    <?> "type"

identifier :: TokenParser String -> TokenParser Id
identifier = fmap idFromString

----------------------------------------------------------------
-- Basic parsers
----------------------------------------------------------------

lexeme :: Lexeme -> TokenParser ()
lexeme lex = satisfy f <?> show lex
 where
  f a | a == lex  = Just ()
      | otherwise = Nothing


lexChar :: TokenParser Char
lexChar = satisfy
  (\case
    LexChar c -> Just c
    _         -> Nothing
  )

lexString :: TokenParser String
lexString = satisfy
  (\case
    LexString s -> Just s
    _           -> Nothing
  )

lexDouble :: TokenParser Double
lexDouble = satisfy
  (\case
    LexFloat d -> Just d
    _          -> Nothing
  )

lexInt :: TokenParser Integer
lexInt = satisfy
  (\case
    LexInt i -> Just i
    _        -> Nothing
  )

lexId :: TokenParser String
lexId = satisfy
  (\case
    LexId s -> Just s
    _       -> Nothing
  )

lexTypeVar :: TokenParser Int
lexTypeVar = satisfy
  (\case
    LexTypeVar idx -> Just idx
    _              -> Nothing
  )

lexOp :: TokenParser String
lexOp = satisfy
  (\case
    LexOp s -> Just s
    _       -> Nothing
  )

lexCon :: TokenParser String
lexCon = satisfy
  (\case
    LexCon s -> Just s
    _        -> Nothing
  )

lexConOp :: TokenParser String
lexConOp = satisfy
  (\case
    LexConOp s -> Just s
    _          -> Nothing
  )

satisfy :: (Lexeme -> Maybe a) -> TokenParser a
satisfy p = tokenPrim showtok nextpos (\(_, lex) -> p lex)
 where
  showtok (_, lex) = show lex
  nextpos pos _ (((line, col), _) : _) =
    setSourceColumn (setSourceLine pos line) col
  nextpos pos _ [] = pos

parseFromString :: TokenParser a -> String -> Either String a
parseFromString p str =
  let toks = lexer (0, 0) str
  in  case runParser (waitForEOF p) () "Core.Parsing.Parser" toks of
        Left  _ -> Left str --error ("Core.Parsing.Parser parseFromString: parse error in " ++ string ++ show tokens)
        Right x -> Right x

waitForEOF :: TokenParser a -> TokenParser a
waitForEOF p = do
  x <- p
  lexeme LexEOF
  return x
