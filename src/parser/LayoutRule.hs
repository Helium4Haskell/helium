module LayoutRule(layout) where

import LexerToken(Token, Lexeme(..), lexemeLength)
import ParsecPos

layout :: [Token] -> [Token]
layout [] = []
layout input@((pos, lexeme):_) = fixEOF . optimise $
    case lexeme of 
        LexKeyword "module" -> 
            lay zeroPos [] input
        LexSpecial '{' ->
            lay zeroPos [] input
        _ ->
            (pos, LexInsertedOpenBrace) : 
            lay zeroPos [CtxLay (sourceColumn pos) False] input
    where
        zeroPos = setSourceColumn (setSourceLine pos 0) 0

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
    
--  position previous token
--            enclosing contexts
lay :: SourcePos -> [Context] -> [Token] -> [Token]

-- If we're in a CtxBrace and we see a '}', we leave that context.
-- If we see another token, we check to see if we need to add a
-- new context.
lay     _ 
        cc@(CtxBrace:cs) 
        input@(t@(pos, lexeme):ts)
    | lexeme == LexSpecial '}' =
        t : lay pos cs ts
    | otherwise = 
        t : addContext pos cc input 

-- If we're in a let layout context, an 'in' can end
-- the context, too.
lay     _ 
        (CtxLay _ True:cs) 
        (t@(pos, LexKeyword "in"):ts) 
    = (pos, LexInsertedCloseBrace) : t : lay pos cs ts

-- If we're in a layout context and the new token is not on the 
-- same line as the previous, we check the column against the
-- context. If the new token is on the same line, we only need
-- to check whether a context has to be added.
lay     prevPos 
        cc@(CtxLay ctxCol _:cs) 
        input@(t@(pos, _):_) 
    | sourceLine pos > sourceLine prevPos = -- token on next line?
        if sourceColumn pos > ctxCol then -- indent more => nothing
            t : addContext pos cc input
        else if sourceColumn pos == ctxCol then -- indent same => insert ';' 
            (pos, LexInsertedSemicolon) : t : addContext pos cc input
        else -- indent less => insert brace, remove context and try again
            (pos, LexInsertedCloseBrace) : lay prevPos cs input
    | otherwise = -- token on same line
        t : addContext pos cc input

lay _ _ [] = []

lay _ [] input@(t@(pos, _):_) = 
    t : addContext pos [] input

addContext :: SourcePos -> [Context] -> [Token] -> [Token]

-- If we see a '{' we add a CtxBrace context
addContext prevPos cs ((_, LexSpecial '{'):ts) = 
    lay prevPos (CtxBrace : cs) ts

-- If we see a 'do', 'where', 'of' or 'let' we add a context
-- and a '{' only if the next token is not a '{'
addContext prevPos cs 
        ((_, LexKeyword keyword):t2@(pos2, lexeme2):ts) 
    | keyword `elem` ["do", "where", "of","let"] =
        if lexeme2 == LexSpecial '{' then
            lay prevPos cs (t2:ts)
        else
            (pos2, LexInsertedOpenBrace) :
            lay prevPos 
                (CtxLay (sourceColumn pos2) (keyword == "let") : cs) 
                (t2:ts)
    | otherwise = 
        lay prevPos cs (t2:ts)

addContext prevPos cs (_:ts) =
    lay prevPos cs ts

addContext _ _ [] = []

-- Make EOF's position equal to the end of the last token before EOF
fixEOF :: [Token] -> [Token]
fixEOF tokens 
    | null revOthers = tokens
    | otherwise = reverse $
                        (newEOFPos, LexEOF) 
                      : (  map (\(_, lexeme) -> (newEOFPos, lexeme)) revSamePos
                        ++ revOthers
                        )
    where
        newEOFPos = incSourceColumn lastPos (lexemeLength lastLexeme)
        (lastPos, lastLexeme) = head revOthers
        (revSamePos, revOthers) = span ((== pos) . fst) revTokens
        ((pos, LexEOF):revTokens) = reverse tokens
