module Helium.Top.Top.Implementation.TypeClassDirectives where

import Helium.Top.Top.Types.Primitive
import Helium.Top.Top.Types.Classes

    -- Type class directives
type TypeClassDirectives info = [TypeClassDirective info]

data TypeClassDirective info 
   = NeverDirective     Predicate  info
   | CloseDirective     String     info
   | DisjointDirective  [String]   info
   | DefaultDirective   String Tps info

instance Show (TypeClassDirective info) where
    show (NeverDirective predicate _) = show predicate
    show (CloseDirective n _) = show n
    show (DisjointDirective ns _) = show ns
    show (DefaultDirective n tps _) = show n ++ show tps