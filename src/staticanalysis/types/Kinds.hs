-----------------------------------------------------------------------------
-- The Helium Compiler : Static Analysis : a library for types
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Kinds
--
-----------------------------------------------------------------------------

module Kinds where

import TypeBasics
import TypeSubstitution
import TypeSchemes

type Kind       = Tp
type Kinds      = [Kind]
type KindScheme = TpScheme         

star :: Kind
star = TCon "*"

defaultToStar :: Kind -> Kind
defaultToStar kind = 
   let sub = listToSubstitution [ (i, star) | i <- ftv kind ]
   in sub |-> kind

showKind :: Kind -> String
showKind kind = 
   let sub = listToSubstitution [ (i, TCon ('k':show i)) | i <- ftv kind ]
   in show (sub |-> kind)

showKindScheme :: KindScheme -> String
showKindScheme scheme = 
   let sub = listToSubstitution
                $  [ (i, TCon ('k':show j)) | (i, j) <- zip (getQuantifiers scheme) [1..] ] 
                ++ [ (i, TCon ("_k"++show i)) | i <- ftv scheme ]
   in show (sub |-> getQualifiedType scheme)
