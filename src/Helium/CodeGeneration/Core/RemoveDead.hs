--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.CodeGeneration.Core.RemoveDead (coreRemoveDead) where

import qualified Data.Set as Set
import Data.Set (Set)
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.FreeVar
import Helium.Lvm.Core.Utils
import Data.List

----------------------------------------------------------------
-- The identity of a declaration is it's name *and* the kind.
-- i.e. we can have a kind Type and a type Type. Extern declarations
-- are identified as Value declarations since they are not
-- distinguished from normal values inside core expressions.
----------------------------------------------------------------
type Identity   = (DeclKind,Id)
type Used       = Set Identity

declIdentity :: CoreDecl -> Identity
declIdentity decl@(DeclExtern {})
  = (DeclKindValue, declName decl)
declIdentity decl
  = (declKindFromDecl decl, declName decl)



----------------------------------------------------------------
-- Remove all dead declarations
-- TODO: at the moment, the analysis is too conservative and
-- only removes private declarations that are nowhere used.
-- A proper analysis would find all reachable declaratins.
----------------------------------------------------------------
coreRemoveDead :: CoreModule -> CoreModule
coreRemoveDead m
  = m { moduleDecls = filter (isUsed used) (moduleDecls m) }
  where
    -- Retain main$ even though it is private and not used
    -- It cannot be public because it would be imported and clash
    -- in other modules
    used  = foldl' usageDecl alwaysUsed (moduleDecls m)

    alwaysUsed = Set.fromList
                    [ (DeclKindValue, idFromString "main$")
                    , (DeclKindValue, idFromString "main")
                    ]
    
----------------------------------------------------------------
-- Is a declaration used?
----------------------------------------------------------------
isUsed :: Used -> CoreDecl -> Bool
isUsed _ DeclTypeSynonym{} = True
isUsed _ decl@DeclCustom{}
  | declKind decl == DeclKindCustom (idFromString "data") = True
isUsed used decl
  = accessPublic (declAccess decl) || Set.member (declIdentity decl) used


----------------------------------------------------------------
-- Find used declarations
----------------------------------------------------------------
usageDecl :: Used -> CoreDecl -> Used
usageDecl used decl
  = let usedCustoms = usageCustoms used (declCustoms decl)
    in case decl of
         DeclValue{} -> usageValue usedCustoms (valueValue decl)
         _           -> usedCustoms

usageCustoms :: Used -> [Custom] -> Used
usageCustoms = foldl' usageCustom

usageCustom :: Set (DeclKind, Id) -> Custom -> Set (DeclKind, Id)
usageCustom used custom
  = case custom of
      CustomLink x kind     -> Set.insert (kind,x) used
      CustomDecl _ customs  -> usageCustoms used customs
      _                     -> used

----------------------------------------------------------------
-- Find used declarations in expressions
----------------------------------------------------------------

usageValue :: Used -> Expr -> Used
usageValue = usageExpr emptySet

usageExprs :: IdSet -> Used -> [Expr] -> Used
usageExprs = foldl' . usageExpr

usageExpr :: IdSet -> Used -> Expr -> Used
usageExpr locals used expr
 = case expr of
      Let binds e     -> let used'   = usageBinds locals used binds 
                             locals' = unionSet locals (binder binds)
                         in usageExpr locals' used' e
      Lam _ (Variable x _) e -> usageExpr (insertSet x locals) used e
      Match x alts    -> usageAlts locals (usageVar locals used x) alts
      Ap e1 e2        -> usageExpr locals (usageExpr locals used e1) e2
      Var x           -> usageVar locals used x
      Con con         -> usageCon locals used con
      Lit _           -> used
      Forall _ _ e    -> usageExpr locals used e
      ApType e _      -> usageExpr locals used e

usageVar :: IdSet -> Set (DeclKind, Id) -> Id -> Set (DeclKind, Id)
usageVar locals used x
  | elemSet x locals = used
  | otherwise        = Set.insert (DeclKindValue,x) used

usageCon :: IdSet -> Set (DeclKind, Id) -> Con -> Set (DeclKind, Id)
usageCon locals used con
  = case con of
      ConId x    -> Set.insert (DeclKindCon,x) used
      ConTuple _ -> used

usageBinds :: IdSet -> Used -> Binds -> Used
usageBinds locals used binds 
  = case binds of
      NonRec (Bind _ rhs)  -> usageExpr locals used rhs
      Strict (Bind _ rhs)  -> usageExpr locals used rhs
      Rec bs               -> let (ids,rhss) = unzip $ map (\(Bind (Variable x _) rhs) -> (x, rhs)) bs
                                  locals'    = unionSet locals (setFromList ids)
                              in usageExprs locals' used rhss
  

usageAlts :: IdSet -> Set (DeclKind, Id) -> [Alt] -> Set (DeclKind, Id)
usageAlts = foldl' . usageAlt

usageAlt :: IdSet -> Set (DeclKind, Id) -> Alt -> Used
usageAlt locals used (Alt pat expr)
  = case pat of
      PatCon con _ ids  -> let locals' = unionSet locals (setFromList ids)
                               used'   = usageConPat used con
                         in usageExpr locals' used' expr
      _               -> usageExpr locals used expr
      
usageConPat :: Set (DeclKind, Id) -> Con -> Set (DeclKind, Id)
usageConPat used con
  = case con of
      ConId x    -> Set.insert (DeclKindCon,x) used
      ConTuple _ -> used
