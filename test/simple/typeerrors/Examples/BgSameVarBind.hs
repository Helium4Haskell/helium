module BgSameVarBind where

f = g
g = if f then 3 else f
