module OperatorTable
    (   Assoc(..)
    ,   OperatorTable
    ,   assoc, prio
    ) where

import UHA_Syntax
import UHA_Utils

type OperatorTable = [(Name, (Int, Assoc))]

-- From ParsecExpr
data Assoc              = AssocNone
                        | AssocLeft
                        | AssocRight

assoc :: OperatorTable -> Name -> Assoc
assoc ops name =
    case lookup name ops of
        Nothing -> AssocLeft -- default associativity, if unspecified
        Just (_, a) -> a

prio :: OperatorTable -> Name -> Int
prio ops name =
    case lookup name ops of
        Nothing        -> 9 -- default priority, if unspecified
        Just    (p, _) -> p

instance Eq Assoc where
    AssocLeft  == AssocLeft  = True
    AssocRight == AssocRight = True
    AssocNone  == AssocNone  = True
    _          == _          = False
