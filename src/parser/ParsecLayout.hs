-----------------------------------------------------------
-- Daan Leijen (c) 2002
--
-- Parser that handles the layout rule.
-----------------------------------------------------------
-- 16-5-2002: AFIE: added state parameter, changed context to getContext and
--                  withLayout to withContext, added getLayoutState and
--                  setLayoutState

module ParsecLayout
    ( LayoutParser
    , runLayoutParser
    , layout
    , onside
    , setLayoutState 
    , getLayoutState
    ) where

import Parsec 

{----------------------------------------------------------
 run a layout parser
----------------------------------------------------------}
runLayoutParser :: LayoutParser tok st a -> st -> FilePath -> [tok] -> Either ParseError a
runLayoutParser p initialState fname input
  = runParser p (Lay 0 0 0 initialState) fname input

{----------------------------------------------------------
 Layout types.
 A "LayoutParser" uses the user-state to store the
 current "Layout" context: 
   the current line, the layout column and finally the 
   line where this layout originated. A zero column is 
   used for explicit layouts.
----------------------------------------------------------}
type LayoutParser tok st a  = GenParser tok (Layout st) a
data Layout st              = Lay !Int !Int !Int st


{----------------------------------------------------------
 use "layout" to add layout processing to some construct.
 for example, in Haskell we could use:

  stmts
    = layout "statement" "\";\""   sepBy lcurly rcurly semi stmt

  decls
    = layout "declaration" "\";\"" sepBy lcurly rcurly semi decl

 the first two arguments are the labels for the things
 seperated (declaration) and the seperator (;). The next
 function is used for parsing when an explicit context is
 entered (sepBy decl semi), the next two arguments give the
 tokens that start and end an explicit context ({ and }),
 and finally the seperator and things to parse are given 
 (semi and decl).
----------------------------------------------------------}
layout ::  String -> String -> (LayoutParser tok st a -> LayoutParser tok st () -> LayoutParser tok st [a]) 
        -> LayoutParser tok st () -> LayoutParser tok st () -> LayoutParser tok st ()
        -> LayoutParser tok st a -> LayoutParser tok st [a]
layout labelp labelsep sepby lbrace rbrace sep p 
  = do{ lbrace
      ; withContext (0, 0, 0)
                (do{ 
                    xs <- p `sepby` sep;
                    rbrace;
                    return xs;
                })
      }
  <|>
    do{ (c,l)          <- columnLine
      ; (cc, cl, dl) <- getContext
      ; if (c <= cc) -- enforce indentation larger than enclosing context
         then fail ("the indentation of the " ++ labelp ++ " is lower than the enclosing context (at: line " ++ show dl ++ ", column " ++ show cc ++ ")")
         else do{ x  <- withContext (c, l, l) p 
                ; xs <- many (offside sep p c l `labels` ["(justified) " ++ labelp,"(indented) " ++ labelsep])
                ; return (x:xs)
                }   
              <|> return []
      }

offside :: LayoutParser tok st () -> LayoutParser tok st a -> Int -> Int -> LayoutParser tok st a
offside sep p cc dl
  = do{ (c,l) <- columnLine
      ; if (c >= cc) then return () else pzero   -- enforce onside         
      ; if (c == cc) then optional sep else sep  -- allow (or require) explicit seperators
      ; withContext (cc, l, dl) p 
      }


{----------------------------------------------------------
 "onside" is used as a guard for every primitive token and
 only succeeds if it is applied 'onside', ie. it belongs
 to the current context.
 For example, in a real parser, you normally define a lexeme
 parser that handles whitespace. In a layout sensitive
 language, you should also apply the "onside" parser.

  lexeme p        
    = do{ onside; x <- p; whiteSpace; return x  }
----------------------------------------------------------}
onside :: LayoutParser tok st ()
onside 
  = do{ (c,l)          <- columnLine
      ; (cc, cl, dl) <- getContext
      ; if (cc == 0 || c > cc || cl == l) -- is this token 'onside'?
         then return () 
         else (if (cc /= 0 && c <= cc && l > cl && cc > 1)
                then let chance = if (c == cc || c+1 == cc) then "probably" else "possibly"
                     in  fail (chance ++ " incorrect layout (enclosing context at: line " ++ show dl ++ ", column " ++ show cc ++ ")")
                else pzero)              
      }

columnLine
  = do{ p <- getPosition
      ; return (sourceColumn p,sourceLine p)
      }

getContext = 
    do { 
        Lay cc cl dl _ <- getState;
        return (cc, cl, dl);
    } 

withContext (cc, cl, dl) p =
    do {
        Lay oldCc oldCl oldDl st <- getState;
        setState (Lay cc cl dl st);
        x <- p;
        setState (Lay oldCc oldCl oldDl st);
        return x;
    }
{-
withLayout ctx p
  = do{ ctx0 <- context
      ; setState ctx 
      ; x <- p
      ; setState ctx0
      ; return x
      }
-}

setLayoutState s =
    do {
        Lay cc cl dl _ <- getState;
        setState (Lay cc cl dl s);
    }

getLayoutState  =
    do {
        Lay _ _ _ s <- getState;
        return s;
    }