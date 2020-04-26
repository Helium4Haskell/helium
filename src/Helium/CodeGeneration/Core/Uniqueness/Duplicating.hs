-- This module does the following:
-- - Duplicate functions uniqueness analysis deems necessary
-- - Rewrite duplicated functions to remove memory reuse and
--   call the correct functions in the duplicated functions

module Helium.CodeGeneration.Core.Uniqueness.Duplicating where

import qualified Data.Set as S
import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- | Takes a set of functions ids and a CoreModule and returns a new
--   CoreModule with duplicated functions
duplicate :: CoreModule -> CoreModule
duplicate (m@Module {moduleDecls = decls}) = m {moduleDecls = duplicateDecls s decls}
  where s = collectUnique decls

collectUnique :: [CoreDecl] -> S.Set Id
collectUnique [] = mempty
collectUnique (DeclValue {declName = name, declType = tp} : xs) =
  let s = collectUnique xs
  in case isUniqueFunction tp of
      True -> S.insert name s
      False -> s
collectUnique (_:xs) = collectUnique xs

isUniqueFunction :: Type -> Bool
isUniqueFunction (TForall _ t) = isUniqueFunction t
isUniqueFunction (TAp (TAp (TCon TConFun) t1) t2) = isUniqueType t1 || isUniqueFunction t2
isUniqueFunction _ = False

isUniqueType :: Type -> Bool
isUniqueType (TAp (TAnn _ UUnique) _) = True
isUniqueType _ = False

-- | Duplicates a declaration if it is a member of the Set
duplicateDecls :: S.Set Id -> [CoreDecl] -> [CoreDecl]
duplicateDecls _ [] = []
duplicateDecls s (d@(DeclValue {declName = name, valueValue = expr, declType = tp}) : xs) =
  case S.member name s of
    True -> d : d {declName = nonMutId name, valueValue = rewriteExpr s expr, declType = rewriteType tp} : duplicateDecls s xs
    False -> d : duplicateDecls s xs
duplicateDecls s (x : xs) = x : duplicateDecls s xs

-- | For every duplicated function we append _nonmut
nonMutId :: Id -> Id
nonMutId i = idFromString (stringFromId i ++ "_nonmut")

rewriteType :: Type -> Type
rewriteType (TAp t1 t2) = TAp (rewriteType t1) (rewriteType t2)
rewriteType (TForall q t) = TForall q (rewriteType t)
rewriteType (TQTy t qs) = TQTy (rewriteType t) qs
rewriteType (TAnn s UUnique) = TAnn s UShared
rewriteType t = t

-- | Walks over the function, if Ap is encountered, it is candidate to be renamed.
rewriteExpr :: S.Set Id -> Expr -> Expr
rewriteExpr s (Let b e) = Let (rewriteBinds s b) (rewriteExpr s e)
rewriteExpr s (Match i a) = Match i (map (rewriteAlt s) a)
rewriteExpr s (Ap e1 e2) = Ap (rewriteApExpr s e1) (rewriteExpr s e2)
rewriteExpr s (ApType e1 t) = ApType (rewriteExpr s e1) t
rewriteExpr s (Lam b v e) = Lam b v (rewriteExpr s e)
rewriteExpr s (Forall q e) = Forall q (rewriteExpr s e)
rewriteExpr _ (Con i _) = Con i Nothing
rewriteExpr _ e = e

rewriteBinds :: S.Set Id -> Binds -> Binds
rewriteBinds s (Rec bs) = Rec (map (rewriteBind s) bs)
rewriteBinds s (Strict b) = Strict (rewriteBind s b)
rewriteBinds s (NonRec b) = NonRec (rewriteBind s b)

rewriteBind :: S.Set Id -> Bind -> Bind
rewriteBind s (Bind v e) = Bind v (rewriteExpr s e)

rewriteAlt :: S.Set Id -> Alt -> Alt
rewriteAlt s (Alt p e) = Alt p (rewriteExpr s e)

-- | If a Var is encountered and is member of the set, rename it.
rewriteApExpr :: S.Set Id -> Expr -> Expr
rewriteApExpr s (Var i) = case S.member i s of
  True -> Var (nonMutId i)
  False -> Var i
rewriteApExpr s (Ap e1 e2) = Ap (rewriteApExpr s e1) (rewriteExpr s e2)
rewriteApExpr s (ApType e1 t) = ApType (rewriteApExpr s e1) t
rewriteApExpr s e = rewriteExpr s e
