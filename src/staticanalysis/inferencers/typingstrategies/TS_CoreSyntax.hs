module TS_CoreSyntax where

import Types
import List

type Core_TypingStrategies = [Core_TypingStrategy]

-- ag-data type with extra derivings
data Core_Judgement = Judgement (String) (Tp)
   deriving Read
-- Core_Judgements ---------------------------------------------
type Core_Judgements = [(Core_Judgement)]
-- Core_TypeRule -----------------------------------------------
data Core_TypeRule = TypeRule (Core_Judgements) (Core_Judgement)
   deriving (Show, Read)
-- Core_TypingStrategy -----------------------------------------
data Core_TypingStrategy = TypingStrategy (Core_TypeRule) (Core_UserStatements)
   deriving (Show, Read)
-- Core_UserStatement ------------------------------------------
data Core_UserStatement = Constraint (Tp) (Tp) (String)
                        | MetaVariableConstraints (String)
                        | Phase (Int)
   deriving Read                     
-- Core_UserStatements -----------------------------------------
type Core_UserStatements = [(Core_UserStatement)]                  

instance Read Tp where 
   readsPrec i string
      | "TVar " `isPrefixOf` string = [ (TVar int, rest)
                                      | (int, rest) <- readsPrec i (drop 5 string) :: [(Int, String)]
                                      ]  
      | "TCon " `isPrefixOf` string = [ (TCon s, rest)
                                      | (s, rest) <- readsPrec i (drop 5 string) :: [(String, String)]
                                      ]                                        
      | "TApp " `isPrefixOf` string = [ (TApp left right, rest')
                                      | (left,  ' ':rest) <- readsPrec i (drop 5 string) :: [(Tp, String)]
                                      , (right, rest') <- readsPrec i rest :: [(Tp, String)]
                                      ]                                      
      | "(" `isPrefixOf` string =  [ (tp, rest') 
                                   | (tp, ')':rest') <- readsPrec i (tail string) :: [(Tp, String)] 
                                   ]  
      | " " `isPrefixOf` string = readsPrec i (tail string)                                   
      | otherwise = error ("instance Read Tp: "++show string)

-- for Tp special show
instance Show Core_Judgement where
  show (Judgement s tp) = "(Judgement "++show s++" ("++showTp tp++"))"
 
instance Show Core_UserStatement where
  show (Constraint t1 t2 s)        = "Constraint ("++showTp t1++") ("++showTp t2++") "++show s
  show (MetaVariableConstraints s) = "MetaVariableConstraints "++show s
  show (Phase i)                   = "Phase "++show i
   
showTp :: Tp -> String
showTp (TVar i)   = "TVar "++show i
showTp (TCon c)   = "TCon "++show c
showTp (TApp l r) = "TApp ("++showTp l++") ("++showTp r++")"
