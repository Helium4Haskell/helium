module BgExplicitVarBind where

f :: Bool
f = True

g = if f then 3 else f
