--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Asm.Data
   ( AsmModule
   , AsmDecl
   , Top(..)
   , Atom
   , Expr(..)
   , Note(..)
   , Occur(..)
   , Lit(..)
   , Alt(..)
   , Pat(..)
   , Con(..)
   )
where

import           Prelude                 hiding ( (<$>) )

import           Helium.Lvm.Common.Byte
import           Helium.Lvm.Common.Id
import           Helium.Lvm.Core.Module
import           Text.PrettyPrint.Leijen

{---------------------------------------------------------------
  Asm modules
---------------------------------------------------------------}
type AsmModule = Module Top
type AsmDecl = Decl Top

{---------------------------------------------------------------
  low level "assembly" language
---------------------------------------------------------------}
data Top    = Top ![Id] Expr      -- arguments expression

type Atom = Expr
data Expr   = Eval   !Id Expr Expr
            | Match  !Id ![Alt]
            | Prim   !Id ![Atom]
            -- atomic
            | LetRec ![(Id,Atom)] Expr
            | Let    !Id Atom Expr
            | Ap     !Id ![Atom]
            | Con    !(Con Atom) ![Atom]
            | Lit    !Lit
            | Note   !Note !Expr

data Note   = Occur  !Occur
data Occur  = Never | Once | Many

data Lit    = LitInt   !Int
            | LitFloat !Double
            | LitBytes !Bytes

data Alt    = Alt !Pat Expr

data Pat    = PatVar !Id
            | PatCon !(Con Int) ![Id]
            | PatLit !Lit

data Con tag = ConId !Id
             | ConTag tag !Arity

{---------------------------------------------------------------
  pretty print Asm expressions
---------------------------------------------------------------}

instance Pretty Top where
   pretty (Top args expr) =
      nest 2 (text "\\" <> hsep (map pretty args) <+> text "->" <$> pretty expr)

{---------------------------------------------------------------
  expressions
---------------------------------------------------------------}

instance Pretty Expr where
   pretty = ppExprWith id

ppArg :: Expr -> Doc
ppArg = ppExprWith parens

ppExprWith :: (Doc -> Doc) -> Expr -> Doc
ppExprWith pars expr = case expr of
   Let x atom e ->
      pars
         $   align
         $   hang 3 (text "let" <+> ppBind (x, atom))
         <$> (text "in" <+> pretty e)
   LetRec binds e ->
      pars $ align $ hang 7 (text "letrec" <+> vcat (map ppBind binds)) <$> nest
         3
         (text "in" <+> pretty e)
   Eval x e e' ->
      pars
         $   align
         $   hang 7 (text "let!" <+> pretty x <+> text "=" </> pretty e)
         <$> nest 3 (text "in" <+> pretty e')
   Match x alts -> pars $ align $ hang
      2
      (text "match" <+> pretty x <+> text "with" <$> vcat (map pretty alts))
   Prim x args ->
      pars
         $   text "prim"
         <>  char '['
         <>  pretty x
         <+> hsep (map ppArg args)
         <>  char ']'
   Ap  x   []   -> pretty x
   Ap  x   args -> pars $ pretty x <+> hsep (map ppArg args)
   Con con []   -> pretty con
   Con con args -> pars $ pretty con <+> hsep (map ppArg args)
   Lit lit      -> pretty lit
   Note note e  -> pars $ align $ pretty note </> pretty e

instance Pretty a => Pretty (Con a) where
   pretty con = case con of
      ConId x -> pretty x
      ConTag tag arity ->
         text "(@" <> pretty tag <> char ',' <> pretty arity <> char ')'

instance Pretty Note where
   pretty (Occur occ) = angles (pretty occ)

instance Pretty Occur where
   pretty Never = text "never"
   pretty Once  = text "once"
   pretty Many  = text "many"

{---------------------------------------------------------------
  alternatives
---------------------------------------------------------------}

instance Pretty Alt where
   pretty (Alt pat expr) = hang 2 (pretty pat <+> text "->" </> pretty expr)

instance Pretty Pat where
   pretty pat = case pat of
      PatCon con params -> pretty con <+> hsep (map pretty params)
      PatVar x          -> pretty x
      PatLit lit        -> pretty lit

{---------------------------------------------------------------
  literals and variables
---------------------------------------------------------------}

instance Pretty Lit where
   pretty lit = case lit of
      LitInt   i -> pretty i
      LitFloat d -> pretty d
      LitBytes b -> dquotes (string (stringFromBytes b))

ppBind :: Pretty a => (Id, a) -> Doc
ppBind (x, atom) = pretty x <+> text "=" <+> pretty atom
