{-| Module      :  LayoutRule
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

{- We need to address the following issue:
     * all where blocks can be empty
     * it is empty when the next token is indented less or equally compared to 
       first token on the line that contains the where
     * unless the where is where associated with a module
   The fix: when dealing with the where, check for the next token. If it is indented
   insufficiently open and close the bracket, otherwise open as usual. This ONLY
   APPLIES TO WHERE, not to let, do, etc..
   It may be that the trick of setting the module column position to zero will 
   then work, in the sense that that is not the problem.

   Verify workings with helium -b -u LegeWhere.hs
-}

module Helium.Parser.LayoutRule(layout) where

--import Debug.Trace
import Helium.Parser.LexerToken(Token, Lexeme(..), lexemeLength)
import Text.ParserCombinators.Parsec.Pos

--trS :: Show a => a -> b -> b
--trS = traceShow

trc :: String -> a -> a
trc _ = id

layout :: [Token] -> [Token]
layout [] = []
layout input@((pos, lexeme):_) = optimise $
    case lexeme of 
        LexKeyword "module" -> 
            lay dummyToken [] input
        LexSpecial '{' ->
            lay dummyToken [] input
        _ ->
            (pos, LexInsertedOpenBrace) : 
            lay dummyToken [CtxLay (sourceColumn pos) False] input
    where
        zeroPos = setSourceColumn (setSourceLine pos 0) 0
        dummyToken = (zeroPos, LexVar "")

optimise :: [Token] -> [Token]
optimise (token1@(_, LexInsertedOpenBrace) : (_, LexInsertedSemicolon) : ts) =
    optimise (token1 : ts)
optimise (t:ts) = 
    t : optimise ts
optimise [] = []

data Context 
    = CtxLay Int Bool {- let? -}
    | CtxBrace
    deriving (Eq,Show)
    
--     previous token
--              enclosing contexts
lay :: Token -> [Context] -> [Token] -> [Token]

-- If we're in a CtxBrace and we see a '}', we leave that context.
-- If we see another token, we check to see if we need to add a
-- new context.
lay     _ 
        cc@(CtxBrace:cs) 
        input@(t@(_, lexeme):ts)
    | lexeme == LexSpecial '}' =
        t : lay t cs ts
    | otherwise = 
        t : addContext t cc input 

-- If we're in a let layout context, an 'in' can end
-- the context, too.
lay     prevToken 
        (CtxLay _ True:cs) 
        (t@(_, LexKeyword "in"):ts) 
    = (behind prevToken, LexInsertedCloseBrace) : t : lay t cs ts

-- If we're in a layout context and the new token is not on the 
-- same line as the previous, we check the column against the
-- context. If the new token is on the same line, we only need
-- to check whether a context has to be added.
lay     prevToken@(prevPos, _)
        cc@(CtxLay ctxCol _:cs) 
        input@(t@(pos, _):_) 
    | sourceLine pos > sourceLine prevPos = -- token on next line?
        if sourceColumn pos > ctxCol then -- indent more => nothing
            t : addContext t cc input
        else if sourceColumn pos == ctxCol then -- indent same => insert ';' 
            (behind prevToken, LexInsertedSemicolon) : t : addContext t cc input
        else -- indent less => insert brace, remove context and try again
            (behind prevToken, LexInsertedCloseBrace) : lay prevToken cs input
    | otherwise = -- token on same line
        t : addContext t cc input
        
lay _ _ [] = []

lay _ [] input@(t@(_, _):_) = 
    t : addContext t [] input

behind :: Token -> SourcePos
behind (pos, lexeme) = incSourceColumn pos (lexemeLength lexeme)

addContext :: Token -> [Context] -> [Token] -> [Token]

-- If we see a '{' we add a CtxBrace context
addContext prevToken cs ((_, LexSpecial '{'):ts) = 
    lay prevToken (CtxBrace : cs) ts

-- If we see a 'do', 'where', 'of' or 'let' we add a context
-- and a '{' only if the next token is not a '{'
addContext prevToken cs 
        ((_, LexKeyword keyword):t2@(pos2, lexeme2):ts) 
    | keyword `elem` ["do", "where", "of","let"] =
        if lexeme2 == LexSpecial '{' then
            lay prevToken cs (t2:ts)
        else
          let 
            (prevpos, _) = prevToken
            poscol = sourceColumn pos2
          in
            (pos2, LexInsertedOpenBrace) :
            (if (keyword == "where" && isEmptyNonModuleWhere cs poscol) then
              (pos2, LexInsertedCloseBrace) : lay prevToken cs (t2:ts) -- Close an empty where block
            else
              lay (trc ("Anchor lexeme: " ++ show lexeme2 ++ "Poscol: " ++ 
                        show poscol ++ "PrevPos:" ++ show prevpos
                        ++ "\nCs: " ++ show cs) prevToken)
                 -- 2nd arg to CtxLay remembers the start location of this line,
                 -- which FOLLOWS the structuring element. The following lines
                 -- that are indented with the exact same amount belong to this block.
                  (CtxLay poscol (keyword == "let") : cs) 
                 (t2:ts)
              )           
    | otherwise = 
        lay prevToken cs (t2:ts)
        -- isEmptyNonModuleWhere decides for the case that when we have a where clause that 
        -- does not belong to a module scope where, then whatever
        -- follows and is expected to belong to it, must be indented. 
        -- The check that we are dealing with a "where" has already been performed
       where
          isEmptyNonModuleWhere :: [Context] -> Int -> Bool
          isEmptyNonModuleWhere []     _      = False
          isEmptyNonModuleWhere (c:cs') poscol =
            case c of 
              CtxBrace     -> isEmptyNonModuleWhere cs' poscol
              CtxLay col _ -> poscol <= col 

addContext prevToken cs (_:ts) =
    lay prevToken cs ts

addContext _ _ [] = []
