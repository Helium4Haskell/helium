

-- UUAGC 0.9.42.2 (Helium/StaticAnalysis/Directives/TS_Syntax.ag)
module Helium.StaticAnalysis.Directives.TS_Syntax where

import Helium.Syntax.UHA_Syntax
-- Judgement ---------------------------------------------------
data Judgement = Judgement_Judgement (Expression) (Type)
-- SimpleJudgement ---------------------------------------------
data SimpleJudgement = SimpleJudgement_SimpleJudgement (Name) (Type)
-- SimpleJudgements --------------------------------------------
type SimpleJudgements = [SimpleJudgement]
-- TypeRule ----------------------------------------------------
data TypeRule = TypeRule_TypeRule (SimpleJudgements) (Judgement)
-- TypingStrategies --------------------------------------------
type TypingStrategies = [TypingStrategy]
-- TypingStrategy ----------------------------------------------
data TypingStrategy = TypingStrategy_Siblings (Names)
                    | TypingStrategy_TypingStrategy (TypeRule) (UserStatements)
-- UserStatement -----------------------------------------------
data UserStatement = UserStatement_Equal (Type) (Type) (String)
                   | UserStatement_Pred (Name) (Type) (String)
                   | UserStatement_MetaVariableConstraints (Name)
                   | UserStatement_Phase (Int)
-- UserStatements ----------------------------------------------
type UserStatements = [UserStatement]