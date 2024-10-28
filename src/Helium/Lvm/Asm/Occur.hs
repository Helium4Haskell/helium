--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$
module Helium.Lvm.Asm.Occur (asmOccur) where

import Helium.Lvm.Asm.Data
import Helium.Lvm.Common.Id 
import Helium.Lvm.Common.IdMap

{---------------------------------------------------------------
  Occ: maps identifiers to the number of syntactic
  occurrences
---------------------------------------------------------------}
type Occ  = IdMap Int

addOcc :: Id -> Occ -> Occ
addOcc x = insertMapWith x 1 (+1)

delOcc :: Id -> IdMap Int -> IdMap Int
delOcc = deleteMap

unionOcc :: IdMap Int -> IdMap Int -> IdMap Int
unionOcc = unionMapWith (+)

unionOccs :: [IdMap Int] -> IdMap Int
unionOccs = foldr unionOcc emptyMap

occur :: Id -> Occ -> Occur
occur x occ
  = case lookupMap x occ of
      Just 0  -> Never
      Just 1  -> Once
      Just _  -> Many
      Nothing -> Never

{---------------------------------------------------------------
  asmOccur: annotate every Eval and Let binding with
  the number of syntactic occurrences.
---------------------------------------------------------------}
asmOccur :: AsmModule -> AsmModule
asmOccur = fmap occTop

occTop :: Top -> Top
occTop (Top x expr)
  = let (expr', _) = occExpr expr
    in  Top x expr'

occExpr :: Expr -> (Expr,Occ)
occExpr expr
  = case expr of
      -- TODO: if we determine that a let bound variable is never used, 
      -- we can delete occurrences in its definition *if* an inliner 
      -- removes all dead let bindings. This would make the occurrence 
      -- analysis more precise
      Eval x e1 e2  -> let (e1',occ1)  = occExpr e1
                           (e2',occ2)  = occExpr e2
                           occ         = unionOcc occ1 occ2
                       in (Eval x (Note (Occur (occur x occ)) e1') e2', delOcc x occ)
      Let x e1 e2   -> let (e2',occ2) = occExpr e2  
                           (e1',occ1) = occExpr e1
                           occ        = unionOcc occ1 occ2
                       in (Let x (Note (Occur (occur x occ)) e1') e2', delOcc x occ)
      LetRec bs e   -> let (e',occ1)  = occExpr e
                           (ids,es)   = unzip bs
                           (es',occ2) = occExprs es
                           occ        = unionOcc occ1 occ2
                           bs'        = [(x, Note (Occur (occur x occ)) e2) | (x,e2) <- zip ids es']
                       in (LetRec bs' e', foldr delOcc occ ids)                       

      Match x alts  -> let (alts',occ) = occAlts alts
                       in  (Match x alts',addOcc x occ)
      Ap x atoms    -> let (atoms',occ) = occExprs atoms
                       in (Ap x atoms',addOcc x occ)
      Con con atoms -> let (atoms',occ1) = occExprs atoms
                           (con',occ2)   = occCon con
                       in (Con con' atoms',unionOcc occ1 occ2)
      Prim x atoms  -> let (atoms',occ) = occExprs atoms
                       in (Prim x atoms',occ)
      Lit _         -> (expr,emptyMap)
      Note note e   -> let (expr',occ) = occExpr e 
                       in (Note note expr',occ)

occCon :: Con Expr -> (Con Expr, Occ)  
occCon con
  = case con of
      ConTag tag arity  -> let (tag',occ) = occExpr tag in (ConTag tag' arity,occ)
      _                 -> (con,emptyMap)

occExprs :: [Expr] -> ([Expr],Occ)
occExprs exprs
  = let (exprs',occs) = unzip (map occExpr exprs)
    in (exprs',unionOccs occs)

occAlts :: [Alt] -> ([Alt], IdMap Int)
occAlts alts
  = let (alts',occs) = unzip (map occAlt alts)
    in  (alts',unionOccs occs)

occAlt :: Alt -> (Alt, IdMap Int)
occAlt (Alt pat expr)
  = let (expr',occ) = occExpr expr
    in (Alt pat expr',foldr delOcc occ (patIds pat))
  where
    patIds (PatVar x)     = [x]
    patIds (PatCon _ ids) = ids
    patIds (PatLit _)     = []


                         