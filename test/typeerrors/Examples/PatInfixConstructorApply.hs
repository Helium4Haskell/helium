module PatInfixConstructorApply where

data A = A Int Int

f (3 `A` True) = 42
