{- The overloaded Standard Prelude for the Helium Compiler -}

module Prelude
  ( module Prelude
  , module PreludePrim
  , module HeliumLang
  , module LvmLang
  , module IridiumLang
  ) where 

import PreludePrim
import HeliumLang
import IridiumLang
import LvmLang
import LvmException
                           
infixr 3  &&
infixr 2  ||

{-----------------------------------------------
 -- Bool
 -----------------------------------------------}

not :: Bool -> Bool
not False = True
not _ = False

(||) :: Bool -> Bool -> Bool
(&&) :: Bool -> Bool -> Bool
xor  :: Bool -> Bool -> Bool

x || y = if x then x else y
x && y = if x then y else x

xor True  False = True
xor False True  = True
xor _     _     = False

otherwise :: Bool
otherwise = True

const :: a -> b -> a
const x _ = x