--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id: Lexer.hs 269 2012-08-31 15:16:49Z bastiaan $

module Helium.Lvm.Core.Parsing.Layout
   ( layout
   )
where

import           Helium.Lvm.Core.Parsing.Token

-----------------------------------------------------------
-- The layout rule
-----------------------------------------------------------

layout :: [Token] -> [Token]
layout = doubleSemi . lay [] . addLayout


data Layout = CtxLay   Int
            | CtxLet   Int
            | CtxBrace
            | Indent   Int
   deriving (Eq,Show)

type LayoutToken = Either (Pos, Layout) Token

getPos :: LayoutToken -> Pos
getPos = either fst fst

addLayout :: [Token] -> [LayoutToken]
addLayout ts = case ts of
   (pos, LexMODULE) : _ -> addLay pos rest
   (pos, LexLBRACE) : _ -> addLay pos rest
   (pos, _        ) : _ -> Left (pos, CtxLay (snd pos)) : addLay pos rest
   []                   -> []
   where rest = map Right ts

addLay :: Pos -> [LayoutToken] -> [LayoutToken]
addLay _      []       = []
addLay (l, _) (t : ts) = case t of
   Left (pos@(ln, col), _) | ln > l    -> Left (pos, Indent col) : rest
                           | otherwise -> rest
      where rest = t : addLay pos ts

   Right (pos@(ln, col), lexeme) | ln > l -> Left (pos, Indent col) : t : rest
                                 | otherwise -> t : rest
    where
     rest = case lexeme of
        LexLET       -> newlay CtxLet
        LexLETSTRICT -> newlay CtxLet
        LexWHERE     -> newlay CtxLay
        LexOF        -> newlay CtxLay
        LexDO        -> newlay CtxLay
        _            -> addLay pos ts

     newlay ctx = case ts of
        []                               -> []
        u@(Right (pos', LexLBRACE)) : us -> u : addLay pos' us
        u : us ->
           let pos' = getPos u
           in  Left (pos', ctx (snd pos')) : u : addLay pos' us

lay :: [Layout] -> [LayoutToken] -> [Token]
lay ctx tokens = case tokens of
   []                 -> []

   Left (pos, c) : ts -> case (ctx, c, ts) of
      (CtxLet _ : cs, Indent _, Right t@(post, LexIN) : rest) ->
         (post, LexRBRACE) : t : lay cs rest

      (CtxLet n : cs, Indent i, _) | i == n -> (pos, LexSEMI) : lay ctx ts
                                   | i < n -> (pos, LexRBRACE) : lay cs tokens
                                   | otherwise -> lay ctx ts

      (CtxLay n : cs, Indent i, _)
         | i == n    -> (pos, LexSEMI) : lay ctx ts
         | i < n     -> (pos, LexRBRACE) : lay cs tokens
         | otherwise -> lay ctx ts

      (CtxBrace : _, Indent _, _) -> lay ctx ts
      (_           , Indent _, _) -> lay ctx ts

      _                           -> (pos, LexLBRACE) : lay (c : ctx) ts

   Right t@(pos, lexeme) : ts -> case (ctx, lexeme) of
      (CtxLet _ : cs, LexIN    ) -> (pos, LexRBRACE) : t : lay cs ts
      (CtxLay _ : cs, LexIN    ) -> (pos, LexRBRACE) : lay cs tokens
      (CtxBrace : cs, LexRBRACE) -> t : lay cs ts
      (_            , LexLBRACE) -> t : lay (CtxBrace : ctx) ts
      _                          -> t : lay ctx ts

doubleSemi :: [Token] -> [Token]
doubleSemi (t@(_, LexSEMI) : (_, LexSEMI) : rest) = doubleSemi (t : rest)
doubleSemi (t : ts) = t : doubleSemi ts
doubleSemi [] = []
