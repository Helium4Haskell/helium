module Helium.Optimization.Types
    ( T(..)
    , Constraint(..)
    , TSub, (-$-)
    , (|=>)
    , (|->)
    , (|^|)
    , (|^^|)
    , arity2T
    , arity2TOld
    , assignT
    , applyT
    , freshT
    , freshTOld
    , freshAnn
    , freshTVar
    , solveConstraints
    , splitCons
    , eqAll
    , tuple) where
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
--import qualified Data.Either as Either
import qualified Data.List as List
import Helium.Utils.Utils

import Helium.Optimization.Annotations
import Helium.Optimization.Utils

data T = TAp T T -- [] a => [a], -> a b => a -> b
       | TCon String -- ->, [], Int
       | TVar Int -- a
       | TPred String T -- Num a|Eq a|Ord a|...
       | TAnn Anno T
    deriving (Eq, Ord)

data Anno   = Anno1 Ann -- demand
            | Anno2 (Ann,Ann) -- usage | demand
            | AnnoD [Ann] --data type
    deriving (Show, Eq, Ord)

--instance Show T where
--    show (TAp (TAp (TCon "=>") t1) t2) = "(" ++ show t1 ++ ") => " ++ show t2
--    show (TAp (TAp (TCon "->") t1) t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
--    show (TAp pred@(TPred s i) t) = show pred ++ ", " ++ show t
--    show (TAp (TCon "[]") t) = "[" ++ show t ++ "]"
--    show (TAp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
--    show (TCon s) = s
--    show (TVar i) = show i
--    show (TPred s t) = s ++ " " ++ show t
instance Show T where
    show (TAp (TAp (TCon "=>") t1) t2) = "([" ++ show t1 ++ "] |=> " ++ show t2 ++ ")"
    show (TAp (TAp (TCon "->") t1) t2) = "(" ++ show t1 ++ " |-> " ++ show t2 ++ ")"
    show (TAp p@(TPred _ _) t) = show p ++ ", " ++ show t
    show (TAp t1 t2) = "(TAp " ++ show t1 ++ " " ++ show t2 ++ ")"
    show (TCon s) = "(TCon \"" ++ s ++ "\")"
    show (TVar i) = "(TVar " ++ show i ++ ")"
    show (TPred s t) = "(TPred \"" ++ s ++ "\" " ++ show t ++ ")"
    show (TAnn ann t) = show t ++ "^" ++ show ann

isFreeIn :: Int -> T -> Bool
isFreeIn i (TAp t1 t2) = i `isFreeIn` t1 || i `isFreeIn` t2
isFreeIn i (TPred _ t) = i `isFreeIn` t
isFreeIn i (TAnn _ t) = i `isFreeIn` t
isFreeIn _ (TCon _) = False
isFreeIn i (TVar x) = i == x

freshT :: T -> Fresh T
freshT t = do
    (_,_,t' )<- freshT' Set.empty t
    return t'

freshT' :: Set Int -> T -> Fresh (Set Int, TSub, T)
freshT' changed (TAp t1 t2) = do
    (changed', subs1, t1') <- freshT' changed t1
    (changed'', subs2, t2') <- freshT' changed' (subs1 -$- t2)
    return (changed'', subs2 -.- subs1, TAp t1' t2')
freshT' changed (TPred s t) = do
    (changed', subs, t') <- freshT' changed t
    return (changed', subs, TPred s t')
freshT' changed (TAnn ann t) = do
    (changed', subs, t') <- freshT' changed t
    return (changed', subs, TAnn ann t')
freshT' changed t@(TCon _) = return (changed, idSub, t)
freshT' changed t@(TVar i)
    | Set.member i changed = return (changed, idSub, t)
    | otherwise = do
        tvar@(TVar uniqueId) <- freshTVar
        return  ( Set.insert uniqueId changed
                , sub i tvar
                , tvar
                )

freshTOld :: Int -> T -> (Int, T)
freshTOld uniqueId t =
    let (uniqueId', _, _, t') = freshTOld' uniqueId Set.empty t
    in  (uniqueId', t')

freshTOld' :: Int -> Set Int -> T -> (Int, Set Int, TSub, T)
freshTOld' uniqueId changed (TAp t1 t2) =
    let (uniqueId', changed', subs1, t1') = freshTOld' uniqueId changed t1
        (uniqueId'', changed'', subs2, t2') = freshTOld' uniqueId' changed' (subs1 -$- t2)
    in (uniqueId'', changed'', subs2 -.- subs1, TAp t1' t2')
freshTOld' uniqueId changed (TPred s t) =
    let (uniqueId', changed', subs, t') = freshTOld' uniqueId changed t
    in  (uniqueId', changed', subs, TPred s t')
freshTOld' uniqueId changed (TAnn ann t) =
    let (uniqueId', changed', subs, t') = freshTOld' uniqueId changed t
    in  (uniqueId', changed', subs, TAnn ann t')
freshTOld' uniqueId changed t@(TCon _) = (uniqueId, changed, idSub, t)
freshTOld' uniqueId changed t@(TVar i)
    | Set.member i changed = (uniqueId, changed, idSub, t)
    | otherwise =
        ( uniqueId + 1
        , Set.insert uniqueId changed
        , sub i (TVar uniqueId)
        , TVar uniqueId
        )

freshTVar :: Fresh T
freshTVar = TVar <$> fresh

{- Substitutions -}
type TSub = Map Int T

idSub :: TSub
idSub = Map.empty

sub :: Int -> T -> TSub
sub a t = Map.singleton a t

(-.-) :: TSub -> TSub -> TSub
(-.-) sub1 sub2 = Map.union sub1 $ Map.map (sub1 -$-) sub2

(-$-) :: TSub -> T -> T
(-$-) subs t = case t of
    TAp t1 t2 -> TAp (subs -$- t1) (subs -$- t2)
    TPred s t1 -> TPred s (subs -$- t1)
    TAnn ann t1 -> TAnn ann (subs -$- t1)
    TCon _ -> t
    a@(TVar i) -> Map.findWithDefault a i subs

(-#-) :: TSub -> Constraint T -> Constraint T
(-#-) subs (EqTy debug t1 t2) = EqTy debug (subs -$- t1) (subs -$- t2)
(-#-) _ eq = eq

data Constraint ty
    = EqTy String ty ty             -- t1   == t2
    | EqAnn String Ann Ann          -- phi1 == phi2
    | EqPlus String Ann Ann Ann     -- phi1 == phi2 (+) phi3
    | EqUnion String Ann Ann Ann    -- phi1 == phi2 (U) phi3
    | EqTimes String Ann Ann Ann    -- phi1 == phi2 (*) phi3
    | EqCond String Ann Ann Ann     -- phi1 == phi2 |> phi3
    deriving (Show, Eq, Ord)


infixr 5 |^|
(|^|) :: T -> Ann -> T
t |^| ann = TAnn (Anno1 ann) t

infixr 5 |^^|
(|^^|) :: T -> (Ann,Ann) -> T
t |^^| anns = TAnn (Anno2 anns) t

infixr 5 |=>
(|=>) :: [T] -> T -> T
[] |=> t = t
preds |=> t = TAp (TAp (TCon "=>") (foldr1 TAp preds)) t

infixr 5 |->
(|->) :: T -> T -> T
t1 |-> t2 = TAp (TAp (TCon "->") t1) t2

splitCons :: T -> ([T],T)
splitCons (TAp (TAp (TCon "->") t1) t2) =
    let (t3,t4) = splitCons t2
    in  (t1:t3, t4)
splitCons t = ([],t)

eqAll :: String -> [T] -> [T] -> [Constraint T]
eqAll s (x:xs) (y:ys) = EqTy s x y : eqAll s xs ys
eqAll _ [] [] = []
eqAll s xs ys = internalError "Types.hs" "eqAll" ("Creating constraints for: " ++ s ++ " | unequal lengths remaining xs: " ++ show xs ++ " | remaining ys: " ++ show ys)

arity2T :: Int -> Fresh T
arity2T 0 = freshTVar
arity2T arity
    | arity > 0 = do
        tvar <- freshTVar
        tarity <- arity2T (arity - 1)
        return $ tvar |-> tarity
    | otherwise = internalError "Types.hs" "arity2T" "n smaller than 0"

arity2TOld :: Int -> Int -> T
arity2TOld start n
    | n >= 0 = foldr (\a b -> (TVar a) |-> b) (TVar (start+n)) [(start)..(start+n-1)]
    | otherwise = internalError "Types.hs" "arity2T" "n smaller than 0"

assignT :: Int -> [a] -> (Int,[(a,T)])
assignT start xs = (start + length xs, zip xs (map TVar [start..]))

applyT :: T -> [T] -> T
applyT start xs = foldl TAp start xs

tuple :: Int -> [T] -> T
tuple 0 [] = TCon "()"
tuple 1 [_] = internalError "Types.hs" "tuple" "Creating a tuple unit. Representation already used for the nullary tuple"
tuple arity ts | arity == length ts = applyT (TCon ("(" ++ replicate (arity - 1) ',' ++ ")")) ts
tuple arity ts = internalError "Types.hs" "tuple" ("Creating a tuple unit. arity: " ++ show arity ++ " != length ts: " ++ show ts)

{- Constraint solver -}
mapSnd :: (b->c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a, f b)

solveConstraints :: Int -> [Constraint T] -> (Int, TSub)
solveConstraints uniqueId [] = (uniqueId, idSub)
solveConstraints uniqueId (c:cs) =
    let (uniqueId', subs) = (solveConstraint uniqueId c)
        cs' = map (subs -#-) cs
    in  mapSnd (-.- subs) (solveConstraints uniqueId' cs')

solveConstraint :: Int -> Constraint T -> (Int, TSub)
solveConstraint uniqueId (EqTy debug t1 t2) = throwPossibleErr debug $ tryUnify uniqueId t1 t2
solveConstraint _ eq = internalError "Types.hs" "solveConstraint" ("Eq not yet supported: " ++ show eq)

throwPossibleErr :: String -> Either String a -> a
throwPossibleErr debug possibleErr = case possibleErr of
    Right subs -> subs
    Left err -> internalError "Types.hs" "solveConstraint" ("Constraint : " ++ debug ++ " : " ++ err)

tryUnify :: Int -> T -> T -> Either String (Int, TSub)
tryUnify uniqueId t1 t2 = traceUnify t1 t2 $ case (t1, t2) of
    (TAp (TAp (TCon "=>") preds1) t3, TAp (TAp (TCon "=>") preds2) t4) -> do
        (uniqueId', subs1) <- tryUnify uniqueId preds1 preds2
        (uniqueId'', subs2) <- tryUnify uniqueId' (subs1 -$- t3) (subs1 -$- t4)
        Right $ (uniqueId'', subs2 -.- subs1)
    (TAp (TAp (TCon "=>") preds1) t3, TAp (TAp (TCon "->") t4) t5) -> do
            (uniqueId', subs1) <- tryUnify uniqueId preds1 t4
            (uniqueId'', subs2) <- tryUnify uniqueId' (subs1 -$- t3) (subs1 -$- t5)
            Right $ (uniqueId'', subs2 -.- subs1)
    (TAp (TAp (TCon "->") _) _, TAp (TAp (TCon "=>") _) _) -> do
        tryUnify uniqueId t2 t1
    (TAp (TAp (TCon "->") t3) t4, TAp (TAp (TCon "->") t5) t6) -> do
        (uniqueId', subs1) <- tryUnify uniqueId t3 t5
        (uniqueId'', subs2) <- tryUnify uniqueId' (subs1 -$- t4) (subs1 -$- t6)
        Right $ (uniqueId'', subs2 -.- subs1)
    (TAp t3 t4, TAp t5 t6) -> do
        (uniqueId', subs1) <- tryUnify uniqueId t3 t5
        (uniqueId'', subs2) <- tryUnify uniqueId' (subs1 -$- t4) (subs1 -$- t6)
        Right $ (uniqueId'', subs2 -.- subs1)
    (TPred s1 t3, TPred s2 t4) ->
        if s1 == s2
         then tryUnify uniqueId t3 t4
         else failUnify "Unequal predicates" t1 t2
    (TCon n1, TCon n2) -> if n1 == n2 then Right (uniqueId, idSub) else failUnify "Unequal typeconstructors" t1 t2
    (TVar a1, a2@(TVar _)) -> Right $ (uniqueId, sub a1 a2)
    (TVar a1, t) -> if not $ a1 `isFreeIn` t then Right $ (uniqueId, sub a1 t) else failUnify "Not free" t1 t2
    (t, a2@(TVar _)) -> tryUnify uniqueId a2 t
    (TCon ('D':'i':'c':'t':_), _) -> tryUnify uniqueId t2 t1
    (TPred s t, TCon ('D':'i':'c':'t':n)) -> case List.stripPrefix s n of
        Just tstr -> tryUnify uniqueId t (TCon tstr)
        Nothing -> failUnify ("stripPrefix s: " ++ s ++ " from n: " ++ n ++ "seems impossible") t1 t2
    (t, TCon ('D':'i':'c':'t':n)) -> case List.reverse n of
        ('t':'s':'i':'L':n') -> let p = List.reverse n' in tryUnify (uniqueId + 1) t ([(TPred p (TVar uniqueId))] |=> (TPred p (TAp (TCon "[]") (TVar uniqueId))))
        _ -> case n of
            ('E':'q':d) -> tryUnify (uniqueId + 1) t ([(TPred "Eq" (TVar uniqueId))] |=> (TPred "Eq" (TAp (TCon d) (TVar uniqueId))))
            ('S':'h':'o':'w':d) -> tryUnify (uniqueId + 1) t ([(TPred "Show" (TVar uniqueId))] |=> (TPred "Show" (TAp (TCon d) (TVar uniqueId))))
            _ -> failUnify "Dict{pred}{data}?" t1 t2
    _ -> failUnify "?" t1 t2

failUnify :: String -> T -> T -> Either String a
failUnify reason t1 t2 = Left $ "\nUnable to unify t1: " ++ show t1 ++ " | with t2: " ++ show t2 ++ " | because : " ++ reason

traceUnify :: T -> T -> Either String (Int, TSub) -> Either String (Int, TSub)
traceUnify t1 t2 trace = do -- creating a stacktrace on a fail
    case trace of
        Left err -> Left $ err ++ "\n=> trace: " ++ (fromLeft $ failUnify "trace" t1 t2)
        _ -> trace
    where
        fromLeft :: Either a b -> a
        fromLeft (Left err) = err
        fromLeft (Right _) = internalError "Types.hs" "fromLeft" "Only use with left..."

    {-
module Lvm.Core.Analyses.Types where

import Lvm.Core.Analyses.Annotations
import Lvm.Core.Analyses.Constraints
import Lvm.Core.Analyses.Utils

import Lvm.Common.Id
import Lvm.Core.Expr

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Text.PrettyPrint.Leijen (Pretty, pretty)

----------------------------------------------------------------
-- typeCheck
----------------------------------------------------------------
--typeCheck cm = const cm exprsCheck
--    where
--        exprs = mapMaybe declValue $ moduleDecls cm
--        declValue decl@(DeclValue _ _ _ expr _) = Just (decl, expr)
--        declValue _ = Nothing
--
--        exprsCheck = map (w envEmpty) exprs

freshPi :: Fresh T
freshPi = Alpha <$> fresh

freshGamma :: Fresh Ts
freshGamma = Gamma <$> fresh

type TSub = Map Pi T
type Env = Map Id Ts
data Ts = Forall (Set Ann) (Set Pi) (Set (Constraint Ann T Ts Env)) T
        | TsAnn1 (Ts) Ann -- Usage annotation
        | TsAnn2 (Ts) (Ann,Ann) -- Usage & Demand annotation
        | Gamma Pi
    deriving (Show, Eq, Ord)
data T = TAp T T
       | TCon String
       | TVar Int
    deriving (Show, Eq, Ord)

{- Type to TypeScheme -}
t2ts :: T -> Ts
t2ts t = Forall Set.empty Set.empty Set.empty t

{- Environment -}
envLookup :: Env -> Id -> Ts
envLookup env x = Map.findWithDefault (error $ show x ++ " : not found in env") x env

envAppend :: Id -> Ts -> Env -> Env
envAppend = Map.insert

envEmpty :: Env
envEmpty = Map.empty

{- Constructors used -}
consInT :: T -> Set Id
consInT (TFn t1 t2) = Set.union (consInT t1) (consInT t2)
consInT (TAp t1 t2) = Set.union (consInT t1) (consInT t2)
consInT (TCon i) = Set.singleton i
consInT (TAnn1 t _) = consInT t
consInT (TAnn2 t _) = consInT t
consInT (Alpha _) = Set.empty

{- Free type variables -}

freeInEnv :: Env -> Set Pi
freeInEnv = foldr (\ts acc -> Set.union acc $ freeInTs ts) Set.empty

freeInTs :: Ts -> Set Pi
freeInTs (Forall annotations alphas constraints t) = freeInT t Set.\\ alphas

freeInT :: T -> Set Pi
freeInT t = case t of
    TFn t1 t2 -> Set.union (freeInT t1) (freeInT t2)
    TAp t1 t2 -> Set.union (freeInT t1) (freeInT t2)
    TCon _ -> Set.empty
    TAnn1 t1 _ -> freeInT t1
    TAnn2 t1 _ -> freeInT t1
    Alpha pi -> Set.singleton pi

{- Generalize -}
-- TODO: annotations & constraints
generalize :: Env -> T -> Ts
generalize env t = Forall betas alphas constraints t
    where
    betas = Set.empty
    alphas = freeInT t Set.\\ freeInEnv env
    constraints = Set.empty


{- Instantiate -}
-- TODO: annotations & constraints
instantiate :: Ts -> Fresh T
instantiate (Forall annotations alphas constraints t) = (-$-) <$> sub <*> pure t
    where
    sub :: Fresh (TSub)
    sub = do
        freshs <- sequence $ take (Set.size alphas) $ repeat freshPi
        return $ Map.fromList $ zip (Set.toList alphas) freshs

{- Substitutions -}
idSub :: TSub
idSub = Map.empty

alphasSub :: Set Pi -> TSub
alphasSub = Map.fromSet Alpha

sub :: Pi -> T -> TSub
sub a t = Map.singleton a t

(-.-) :: TSub -> TSub -> TSub
(-.-) sub1 sub2 = Map.union sub1 $ Map.map (sub1 -$-) sub2

(-$-) :: TSub -> T -> T
(-$-) subs t = case t of
    TFn t1 t2 -> TFn (subs -$- t1) (subs -$- t2)
    TAp t1 t2 -> TAp (subs -$- t1) (subs -$- t2)
    TCon _ -> t
    a@(Alpha pi) -> Map.findWithDefault a pi subs

{- Substitute Environment -}
-- TODO: check annotations & constraints
envSubs :: TSub -> Env -> Env
envSubs sub = Map.map (\(Forall annotations alphas constraints t) -> Forall annotations alphas constraints (alphasSub alphas -.- sub -$- t))


{- W algorithm -}
w :: Env -> Expr -> Fresh (T, TSub)
w env expr = case expr of
    Lit lit -> return (TCon $ case lit of
            LitInt _ -> idFromString "Int"
            LitDouble _ -> idFromString "Double"
            LitBytes _ -> idFromString "Bytes"
        , idSub)
    Var id -> do
        t <- instantiate $ envLookup env id
        return (t, idSub)
    Con (ConId id) -> do
        t <- instantiate $ envLookup env id
        return (t, idSub)
    Con (ConTag expr arity) -> todo $ "need: Con (ConTag expr arity) => expr: " ++ p2s expr ++ " | arity: " ++ p2s arity --TODO:
    Lam id expr -> do
        a <- freshPi
        (t, subs) <- w (envAppend id (t2ts a) env) expr
        return (TFn (subs -$- a) t, subs)
    Ap  expr1 expr2 -> do
        (t1, subs1) <- w env expr1
        (t2, subs2) <- w (envSubs subs1 env) expr2
        a <- freshPi
        let subs3 = unify (subs2 -$- t1) (TFn t2 a)
        return (subs3 -$- a, subs3 -.- subs2 -.- subs1)
    Match id alts -> todo $ "need: Match id alts => id: " ++ p2s id ++ " | alts: " ++ p2s alts --TODO:
    Let binds expr -> case binds of
        Rec bs -> todo $ "need: Rec bs => bs: " ++ p2s bs --TODO:
        Strict b -> todo $ "need: Strict b => b: " ++ p2s b --TODO:
        NonRec b -> todo $ "need: NonRec b => b: " ++ p2s b --TODO:
    where
        p2s :: Pretty a => a -> String
        p2s = show . pretty
        todo :: String -> Fresh (T, TSub)
        todo s = const undefined (error s)
-}