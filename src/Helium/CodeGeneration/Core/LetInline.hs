-- Inlines lazy non-recursive let bindings if one of the following holds:
-- * The definition of the variable is an unsaturated call
-- * The result of the thunk is not shared
-- * The variable is not used
--
-- You might not consider the last case as inlining, however, we do inline
-- the definition on all (eg, no) usages.

module Helium.CodeGeneration.Core.LetInline (coreLetInline) where
import Helium.Lvm.Common.Id (Id)
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Module
import Helium.Lvm.Core.Expr
import Data.Maybe (fromMaybe, mapMaybe)

coreLetInline :: CoreModule -> CoreModule
coreLetInline = fmap inline
  where
    arities = emptyMap -- TODO: Gather all arities
    inline expr = inlineInExpr env expr
      where env = createEnv arities expr

data InlineState
  = Inline -- Inline always
  | InlineIfShort -- Inline if the declaration is short, to limit the increase in code size
  | InlineNotShared -- Inline if the declaration does not have to be shared
  | DontInline

data Analysis
  = ANil
  | AValue !Id !InlineState -- Marks an occurence of a variable
  | AAlts !Analysis !Analysis
  | ASequence !Analysis !Analysis
  | ALambda Analysis
  | ABind !Id Analysis -- Represents a non-recursive bind
  | AIgnore !Id Analysis -- Represents that a variable is not part of a lazy non-recursive bind. Only used for performance, not for accuracy or correctness.

aSequence :: [Analysis] -> Analysis
aSequence [] = ANil
aSequence (a:as) = foldr ASequence a as

aAlts :: [Analysis] -> Analysis
aAlts [] = ANil
aAlts (a:as) = foldr AAlts a as

analyseBind :: Bind -> Analysis
analyseBind (Bind (Variable name _) expr) = AIgnore name $ analyse expr

-- TODO: For performance, add AIgnore nodes for all declared variables in the pattern
analyseAlt :: Alt -> Analysis
analyseAlt (Alt _ expr) = analyse expr

analyse :: Expr -> Analysis
analyse (Let (Rec binds) expr) = aSequence $ aexpr : map analyseBind binds
  where
    aexpr = foldr (\(Bind (Variable name _) _) -> AIgnore name) (analyse expr) binds
analyse (Let (NonRec (Bind (Variable name _) e1)) e2) = ASequence (analyse e1) $ ABind name $ analyse e2
analyse (Let (Strict (Bind (Variable name _) e1)) e2) = ASequence (analyse e1) $ AIgnore name $ analyse e2
analyse (Var name) = AValue name Inline
analyse (Match name alts) = ASequence (AValue name DontInline) (aAlts (map analyseAlt alts))
analyse (Ap e1 e2) = ASequence (analyse e1) (analyse e2)
analyse (Lam _ (Variable name _) e) = ALambda $ AIgnore name $ analyse e
analyse (Forall _ _ e) = analyse e
analyse (ApType e1 _) = analyse e1
analyse (Con _) = ANil
analyse (Lit _) = ANil

data Decision
  = Local { decisionName :: !Id, decisionValue :: !InlineState } -- Analysed only locally, not yet final
  | Final { decisionName :: !Id, decisionValue :: !InlineState } -- Analysed till the declaration, the definition is final

-- Merge the two list, similar to merge sort
mergeWith :: (InlineState -> InlineState -> InlineState) -> [Decision] -> [Decision] -> [Decision]
mergeWith f (Local n1 s1 : ds1) (Local n2 s2 : ds2)
  | n1 == n2 = Local n1 (f s1 s2) : mergeWith f ds1 ds2
mergeWith f (d1 : ds1) (d2 : ds2)
  | decisionName d1 < decisionName d2 = d1 : mergeWith f ds1 (d2 : ds2)
  | otherwise = d2 : mergeWith f (d1 : ds1) ds2
mergeWith _ [] ds2 = ds2
mergeWith _ ds1 [] = ds1

-- Inlining the same variable in two alts gives no problems with sharing, as only one branch can be evaluated. However, the branch m
solveAlts :: [Decision] -> [Decision] -> [Decision]
solveAlts = mergeWith f
  where
    f DontInline _ = DontInline
    f _ DontInline = DontInline

    f InlineNotShared _ = InlineNotShared
    f _ InlineNotShared = InlineNotShared

    f _ _ = InlineIfShort

solveSequence :: [Decision] -> [Decision] -> [Decision]
solveSequence = mergeWith f
  where
    f DontInline _ = DontInline
    f _ DontInline = DontInline
    f _ _ = InlineNotShared

solve :: Analysis -> [Decision]
solve ANil = []
solve (AValue name s) = [Local name s]
solve (AAlts left right) = solveAlts (solve left) (solve right)
solve (ASequence left right) = solveSequence (solve left) (solve right)
solve (ALambda a) = map widenDecision $ solve a
  where
    widenDecision (Local name s) = Local name $ widen s
    widenDecision d = d
    widen Inline = InlineNotShared
    widen InlineIfShort = InlineNotShared
    widen s = s
solve (ABind name a) = finalize $ solve a
  where
    finalize [] = [Final name Inline]
    finalize (d@(Local n s) : ds)
      | name == n = Final n s : ds
    finalize (d : ds)
      | decisionName d < name = d : finalize ds
      | otherwise = Final name Inline : d : ds
solve (AIgnore name a) = filter checkName $ solve a
  where
    checkName (Local n _) = n /= name
    checkName _ = True

-- First argument: whether we allow function applications
isShort :: Bool -> Expr -> Bool
isShort _ (Var _) = True
isShort _ (Lit _) = True
isShort _ (Con _) = True
isShort allowAp (Forall _ _ e) = isShort allowAp e
isShort True (Ap e1 e2) = isShort True e1 && isShort True e2
isShort _ _ = False

isUnsaturatedCall :: Arities -> Expr -> Int -> Bool
isUnsaturatedCall arities (Var name) consumed = case lookupMap name arities of
  Nothing -> False
  Just arity -> consumed < arity
isUnsaturatedCall arities (Ap e1 e2) consumed = isShort False e2 && isUnsaturatedCall arities e1 (consumed + 1)
isUnsaturatedCall arities (ApType e _) consumed = isUnsaturatedCall arities e consumed
isUnsaturatedCall arities (Forall _ _ e) consumed = isUnsaturatedCall arities e consumed
isUnsaturatedCall _ _ _ = False

type Arities = IdMap Int
data Env = Env { arities :: !Arities, variables :: !(IdMap InlineState), values :: !(IdMap Expr) }

createEnv :: Arities -> Expr -> Env
createEnv arities expr = Env arities vars emptyMap
  where
    vars = mapFromList $ mapMaybe getDecision $ solve $ analyse expr
    getDecision (Final n s) = Just (n, s)
    getDecision _ = Nothing

inlineInExpr :: Env -> Expr -> Expr
inlineInExpr env e@(Lit _) = e
inlineInExpr env e@(Var name) = fromMaybe e $ lookupMap name $ values env
inlineInExpr env e@(Con _) = e
inlineInExpr env (Lam strict x e) = Lam strict x $ inlineInExpr env e
inlineInExpr env (Ap e1 e2) = Ap (inlineInExpr env e1) (inlineInExpr env e2)
inlineInExpr env (Forall x k e) = Forall x k $ inlineInExpr env e
inlineInExpr env (ApType e t) = ApType (inlineInExpr env e) t
inlineInExpr env (Match x alts) = Match x (map inlineInAlt alts)
  where
    inlineInAlt (Alt pat expr) = Alt pat $ inlineInExpr env expr
inlineInExpr env (Let (NonRec (Bind var@(Variable name _) value)) expr)
  | shouldInline env (findMap name $ variables env) expr =
    let
      env' = env{ values = insertMap name value' $ values env }
    in
      inlineInExpr env' expr
  | otherwise = Let (NonRec (Bind var value')) $ inlineInExpr env expr
  where
    value' = inlineInExpr env value
inlineInExpr env (Let (Strict b) expr) = Let (Strict b') $ inlineInExpr env expr
  where
    b' = inlineInBind env b
inlineInExpr env (Let (Rec bs) expr) = Let (Rec $ map (inlineInBind env) bs) $ inlineInExpr env expr

inlineInBind :: Env -> Bind -> Bind
inlineInBind env (Bind var expr) = Bind var $ inlineInExpr env expr

shouldInline :: Env -> InlineState -> Expr -> Bool
shouldInline _ Inline _ = True
shouldInline _ InlineIfShort expr = isShort True expr
shouldInline env InlineNotShared expr = isShort False expr || isUnsaturatedCall (arities env) expr 0
shouldInline _ DontInline _ = False
