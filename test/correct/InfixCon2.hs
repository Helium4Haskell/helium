module InfixCon2 where

data Tree a = Leaf a | (:+:) (Tree a) (Tree a) Int

