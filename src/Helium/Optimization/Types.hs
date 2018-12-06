module Helium.Optimization.Types where
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
--import qualified Data.Either as Either
--import qualified Data.List as List
import Helium.Utils.Utils

import Helium.Optimization.Annotations
import Helium.Optimization.Utils

import Lvm.Common.Id(Id)

{- Type -}
data T = TAp T T -- [] a => [a], -> a b => a -> b
       | TCon String -- ->, [], Int
       | TVar Int -- a
       | TPred String T -- Num a|Eq a|Ord a|...
       | TAnn Anno T
    deriving (Eq, Ord)

{- TypeScheme -}
data Ts = TsVar Int
        | Ts (Set Int) Constraints T
        | TsAnn Anno Ts
    deriving (Eq, Ord)

{- Annotations -}
data Anno   = Anno1 Ann -- usage
            | Anno2 (Ann,Ann) -- usage | demand
            | AnnoD [Ann] --data type
    deriving (Show, Eq, Ord)

instance Show T where
    show (TAp (TAp (TCon "=>") t1) t2) = "(" ++ show t1 ++ ") => " ++ show t2 ++ ""
    show (TAp (TAp (TCon "->") t1) t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (TAp p@(TPred _ _) t) = show p ++ ", " ++ show t
    show (TAp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    show (TCon s) = show s
    show (TVar i) = show i
    show (TPred s t) = "(" ++ show s ++ " " ++ show t ++ ")"
    show (TAnn ann t) = show t ++ "^" ++ show ann

--instance Show T where
--    show (TAp (TAp (TCon "=>") t1) t2) = "([" ++ show t1 ++ "] |=> " ++ show t2 ++ ")"
--    show (TAp (TAp (TCon "->") t1) t2) = "(" ++ show t1 ++ " |-> " ++ show t2 ++ ")"
--    show (TAp p@(TPred _ _) t) = show p ++ ", " ++ show t
--    show (TAp t1 t2) = "(TAp " ++ show t1 ++ " " ++ show t2 ++ ")"
--    show (TCon s) = "(TCon \"" ++ s ++ "\")"
--    show (TVar i) = "(TVar " ++ show i ++ ")"
--    show (TPred s t) = "(TPred \"" ++ s ++ "\" " ++ show t ++ ")"
--    show (TAnn ann t) = show t ++ "^" ++ show ann

instance Show Ts where
    show (TsVar x) = "forall(" ++ show x ++ ")"
    show (Ts vars ct t) = "forall{" ++ show (Set.toList vars) ++ "}. C{" ++ show ct ++ "}. " ++ show t
    show (TsAnn ann ts) = "(" ++ show ts ++ ")^" ++ show ann

{- Create Types -}
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

eqAll :: String -> [T] -> [T] -> Constraints
eqAll s (x:xs) (y:ys) = EqT s x y : eqAll s xs ys
eqAll _ [] [] = []
eqAll s xs ys = internalError "Types.hs" "eqAll" ("Creating constraints for: " ++ s ++ " | unequal lengths remaining xs: " ++ show xs ++ " | remaining ys: " ++ show ys)

arity2T :: Int -> Int -> T
arity2T start n
    | n >= 0 = foldr (\a b -> (TVar a) |-> b) (TVar (start+n)) [(start)..(start+n-1)]
    | otherwise = internalError "Types.hs" "arity2T" "n smaller than 0"

arity2Tuple :: Int -> Int -> T
arity2Tuple start n
    | n >= 0 =
        let t = map TVar [(start)..(start+n-1)]
        in foldr (\a b -> a |-> b) (tuple n t) t
    | otherwise = internalError "Types.hs" "arity2Tuple" "n smaller than 0"

assignT :: Int -> [a] -> (Int,[(a,T)])
assignT start xs = (start + length xs, zip xs (map TVar [start..]))

applyT :: T -> [T] -> T
applyT start xs = foldl TAp start xs

tuple :: Int -> [T] -> T
tuple 0 [] = TCon "()"
tuple 1 [_] = internalError "Types.hs" "tuple" "Creating a tuple unit. Representation already used for the nullary tuple"
tuple arity ts | arity == length ts = applyT (TCon ("(" ++ replicate (arity - 1) ',' ++ ")")) ts
tuple arity ts = internalError "Types.hs" "tuple" ("Creating a tuple unit. arity: " ++ show arity ++ " != length ts: " ++ show ts)

{- Try direct instantiation-}
instTs2T :: String -> Int -> Ts -> (Int,T,Constraints)
instTs2T d uniqueId (TsAnn ann ts) = let (uniqueId',t,ct) = instTs2T d uniqueId ts in (uniqueId',TAnn ann t,ct) -- TODO: is this correct usage | demand propagation?
instTs2T d uniqueId ts@(TsVar _) = let t = TVar uniqueId in (uniqueId + 1, t, [ EqInst d t ts ] )
instTs2T _ uniqueId (Ts vars ct t) =
    let zippedVars = zip (Set.toList vars) [uniqueId..]
        subT = subm $ Map.map TVar $ Map.fromList zippedVars
        subTs = subm $ Map.map TsVar $ Map.fromList zippedVars
        subAnn = subm $ Map.map AnnVar $ Map.fromList zippedVars
        subs = subT -$- subTs -$- subAnn
        uniqueId' = (snd $ Maybe.fromMaybe (0,uniqueId) $ maybeLast zippedVars) + 1
        t' = subs -$- t
        ct' = subs -$- ct
    in  (uniqueId',t',ct')
    where
    maybeLast :: [a] -> Maybe a
    maybeLast [] = Nothing
    maybeLast [x] = Just x
    maybeLast (_:xs) = maybeLast xs

{- Create and destruct TypeSchemes -}
t2ts :: T -> Ts
t2ts t = Ts Set.empty [] t

ts2t :: Ts -> T
ts2t (Ts _ _ t) = t
ts2t ts = internalError "Types.hs" "ts2t" ("Not supported: " ++ show ts)

t2tsall :: T -> Ts
t2tsall t = Ts (freevars t) [] t

{- Variables -}
class Vars a where
    isfreein :: Int -> a -> Bool
    isfreein i t = Set.member i (freevars t)
    freevars :: a -> Set Int

instance Vars a => Vars [a] where
    freevars as = Set.unions $ map freevars as

instance Vars T where
    freevars (TAp t1 t2) = Set.union (freevars t1) (freevars t2)
    freevars (TPred _ t) = freevars t
    freevars (TCon _) = Set.empty
    freevars (TVar i) = Set.singleton i
    freevars (TAnn ann t) = Set.union (freevars ann) (freevars t)

instance Vars Ts where
    freevars (TsVar i) = Set.singleton i
    freevars (Ts vars ct t) = (Set.union (freevars t) (freevars ct)) Set.\\ vars
    freevars (TsAnn ann ts) = Set.union (freevars ann) (freevars ts)

instance Vars Anno where
    freevars (Anno1 ann) = freevars ann
    freevars (Anno2 (ann1,ann2)) = Set.union (freevars ann1) (freevars ann2)
    freevars (AnnoD anns) = Set.unions $ map freevars anns

instance Vars Ann where
    freevars (AnnVar i) = Set.singleton i
    freevars (AnnVal _) = Set.empty

instance Vars Constraint where
    freevars (EqT _ t1 t2) = Set.union (freevars t1) (freevars t2)
    freevars (EqTs _ ts1 ts2) = Set.union (freevars ts1) (freevars ts2)
    freevars (EqInst _ t ts) = Set.union (freevars t) (freevars ts)
    freevars (EqGen _ ts (t,ct,env)) = Set.unions [freevars ts, freevars env] -- Vars in ts and env will be free. TODO: TAnn will need to be handled.
    freevars (EqAnn _ ann1 ann2) = Set.union (freevars ann1) (freevars ann2)
    freevars (EqPlus _ ann1 ann2 ann3) = Set.unions [freevars ann1, freevars ann2, freevars ann3]
    freevars (EqUnion _ ann1 ann2 ann3) = Set.unions [freevars ann1, freevars ann2, freevars ann3]
    freevars (EqTimes _ ann1 ann2 ann3) = Set.unions [freevars ann1, freevars ann2, freevars ann3]
    freevars (EqCond _ ann1 ann2 ann3) = Set.unions [freevars ann1, freevars ann2, freevars ann3]

instance Vars Env where
    freevars (Env global local) = Set.union (Set.unions $ map (freevars . snd) $ Map.toList global) (Set.unions $ map (freevars . snd) $ Map.toList local)

{- Substitutions -}
data Sub = Sub (Map Int T) (Map Int Ts) (Map Int Ann)
    deriving (Show, Eq, Ord)

idSub :: Sub
idSub = Sub Map.empty Map.empty Map.empty

emptySub :: Sub -> Bool
emptySub (Sub subt subts subann) = Map.null subt && Map.null subts && Map.null subann

withoutSub :: Set Int -> Sub -> Sub
withoutSub vars (Sub subT subTs subAnn) =
    let withoutVars = Map.filterWithKey (\k _ -> k `Set.notMember` vars)
        subT' = withoutVars subT
        subTs' = withoutVars subTs
        subAnn' = withoutVars subAnn
    in  Sub subT' subTs' subAnn'

class SubNew a where
    sub :: Int -> a -> Sub
    subm :: Map Int a -> Sub

class Subs a where
    (-$-) :: Sub -> a -> a

instance Subs a => Subs [a] where
    (-$-) subs = map ((-$-) subs)

instance Subs Sub where
    (-$-) subs1@(Sub subT1 subTs1 subAnn1) (Sub subT2 subTs2 subAnn2) =
        let subT = Map.union subT1 $ Map.map (subs1 -$-) subT2
            subTs = Map.union subTs1 $ Map.map (subs1 -$-) subTs2
            subAnn = Map.union subAnn1 $ Map.map (subs1 -$-) subAnn2
        in  Sub subT subTs subAnn

instance SubNew T where
    sub i t = Sub (Map.singleton i t) Map.empty Map.empty
    subm tm = Sub tm Map.empty Map.empty

instance Subs T where
    (-$-) subs (TAp t1 t2) = TAp (subs -$- t1) (subs -$- t2)
    (-$-) subs (TPred s t1) = TPred s (subs -$- t1)
    (-$-) subs (TAnn ann t1) = TAnn (subs -$- ann) (subs -$- t1)
    (-$-) _ (TCon s) = TCon s
    (-$-) (Sub subT _ _) a@(TVar i) = Map.findWithDefault a i subT

instance SubNew Ts where
    sub i ts = Sub Map.empty (Map.singleton i ts) Map.empty
    subm tsm = Sub Map.empty tsm Map.empty

instance Subs Ts where
    (-$-) (Sub _ subTs _) ts@(TsVar i) = Map.findWithDefault ts i subTs
    (-$-) subs (Ts vars ct t) =
        let subs' = withoutSub vars subs
        in Ts vars ((-$-) subs' ct) ((-$-) subs' t)
    (-$-) subs (TsAnn ann ts) = TsAnn ((-$-) subs ann) ((-$-) subs ts)

instance Subs Anno where
    (-$-) subs (Anno1 ann) = Anno1 $ (-$-) subs ann
    (-$-) subs (Anno2 (ann1,ann2)) = Anno2 ((-$-) subs ann1, (-$-) subs ann2)
    (-$-) subs (AnnoD anns) = AnnoD $ map ((-$-) subs) anns

instance SubNew Ann where
    sub i ann = Sub Map.empty Map.empty (Map.singleton i ann)
    subm annm = Sub Map.empty Map.empty annm

instance Subs Ann where
    (-$-) (Sub _ _ subAnn) a@(AnnVar i) = Map.findWithDefault a i subAnn
    (-$-) _ ann@(AnnVal _) = ann

instance Subs Constraint where
    (-$-) subs (EqT d t1 t2) = EqT d ((-$-) subs t1) ((-$-) subs t2)
    (-$-) subs (EqTs d ts1 ts2) = EqTs d ((-$-) subs ts1) ((-$-) subs ts2)
    (-$-) subs (EqInst d t ts) = EqInst d ((-$-) subs t) ((-$-) subs ts)
    (-$-) subs (EqGen d ts (t,ct,env)) =
        let without = (Set.union (freevars t) (freevars ct)) Set.\\ (Set.union (freevars env) (Set.empty))
            subs' = withoutSub without subs
        in EqGen d ((-$-) subs ts) ((-$-) subs' t, (-$-) subs' ct, (-$-) subs env) -- TODO: TAnn will need to be handled
    (-$-) subs (EqAnn d ann1 ann2) = EqAnn d ((-$-) subs ann1) ((-$-) subs ann2)
    (-$-) subs (EqPlus d ann1 ann2 ann3) = EqPlus d ((-$-) subs ann1) ((-$-) subs ann2) ((-$-) subs ann3)
    (-$-) subs (EqUnion d ann1 ann2 ann3) = EqUnion d ((-$-) subs ann1) ((-$-) subs ann2) ((-$-) subs ann3)
    (-$-) subs (EqTimes d ann1 ann2 ann3) = EqTimes d ((-$-) subs ann1) ((-$-) subs ann2) ((-$-) subs ann3)
    (-$-) subs (EqCond d ann1 ann2 ann3) = EqCond d ((-$-) subs ann1) ((-$-) subs ann2) ((-$-) subs ann3)

instance Subs Env where
    ((-$-) subs) (Env global local) = Env (Map.map ((-$-) subs) global) (Map.map ((-$-) subs) local)

{- Environment -}
data Env = Env (Map Id Ts) (Map Id Ts)
    deriving (Show, Eq, Ord)

empty :: Env
empty = Env Map.empty Map.empty

singletonGlobal :: Id -> Ts -> Env
singletonGlobal key t = insertGlobal key t empty

singletonLocal :: Id -> Ts -> Env
singletonLocal key t = insertLocal key t empty

insertGlobal :: Id -> Ts -> Env -> Env
insertGlobal key t (Env global local) = Env (Map.insert key t global) local

insertLocal :: Id -> Ts -> Env -> Env
insertLocal key t (Env global local) = Env global (Map.insert key t local)

union :: Env -> Env -> Env
union (Env extendGlobal extendLocal) env = unionLocal extendLocal $ unionGlobal extendGlobal env

unionGlobal :: Map Id Ts -> Env -> Env
unionGlobal extendGlobal (Env global local) = Env (Map.union extendGlobal global) local

unionLocal :: Map Id Ts -> Env -> Env
unionLocal extendLocal (Env global local) = Env global (Map.union extendLocal local)

infixr 5 |?|
(|?|) :: (Int, Env) -> (Id, String) -> (Int, T, Constraints)
(uniqueId, env@(Env global local)) |?| (key, err) = case Map.lookup key local of
    Just x -> instTs2T err uniqueId x
    Nothing -> case Map.lookup key global of
        Just x -> instTs2T err uniqueId x
        Nothing -> internalError "LVM_Syntax.ag" "|?|" ("key : " ++ show key ++ " : not found in env : " ++ show env ++ " : " ++ err )

{- Constraints -}
type Constraints = [Constraint]
data Constraint
    = EqT String T T                            -- t1   == t2
    | EqTs String Ts Ts                         -- ts1   == ts2
    | EqInst String T Ts                        -- t1 == Inst(ts2)
    | EqGen String Ts (T, Constraints, Env)     -- ts1 == Gen(t2,ct,env)
    | EqAnn String Ann Ann                      -- phi1 == phi2
    | EqPlus String Ann Ann Ann                 -- phi1 == phi2 (+) phi3
    | EqUnion String Ann Ann Ann                -- phi1 == phi2 (U) phi3
    | EqTimes String Ann Ann Ann                -- phi1 == phi2 (*) phi3
    | EqCond String Ann Ann Ann                 -- phi1 == phi2 |> phi3
    deriving (Show, Eq, Ord)

countCt :: Constraints -> Int
countCt (EqTs _ ts1 ts2:xs) = 1 + countCtTs ts1 + countCtTs ts2 + countCt xs
countCt (EqInst _ _ ts:xs) = 1 + countCtTs ts + countCt xs
countCt (EqGen _ ts (_,ct,_):xs) = 1 + countCtTs ts + countCt ct + countCt xs
countCt (x:xs) = 1 + countCt xs
countCt [] = 0

countCtTs :: Ts -> Int
countCtTs (TsVar _) = 0
countCtTs (Ts _ ct _) = countCt ct
countCtTs (TsAnn _ ts) = countCtTs ts

{- Constraint solver -}
solveConstraints :: Constraints -> Fresh (Sub,Constraints)
solveConstraints ct = do
    let ctOrder = orderConstraints ct
    (subs1, ct') <- solveConstraints' ctOrder
    subs1' <- simplifyTss subs1
    let ct'Order = orderConstraints ct'
    (subs2, ct'') <- solveConstraints' ct'Order
    subs2' <- simplifyTss subs2
    let ct''Order = orderConstraints ct''
    if emptySub subs2' && (null ct''Order || ct'Order == ct''Order)
     then return (subs1',ct''Order)
     else mapFst (-$- (subs2' -$- subs1')) <$> (solveConstraints ct''Order)

{- Order constraints:
   * Generalize before Instantiation constraints -}
orderConstraints :: Constraints -> Constraints
orderConstraints cs = let (cont,conts,conann,congen,coninst) = orderConstraints' cs in concat [cont,conts,conann,congen,coninst]

orderConstraints' :: Constraints ->
    ( Constraints -- T
    , Constraints -- Ts
    , Constraints -- Ann
    , Constraints -- Gen
    , Constraints -- Inst
    )
orderConstraints' [] = ([],[],[],[],[])
orderConstraints' (c:cs) = let (cont,conts,conann,congen,coninst) = orderConstraints' cs in case c of
    EqT     _ _ _   -> (c:cont , conts   , conann   , congen   , coninst   )
    EqTs    _ _ _   -> (cont   , c:conts , conann   , congen   , coninst   )
    EqAnn   _ _ _   -> (cont   , conts   , c:conann , congen   , coninst   )
    EqPlus  _ _ _ _ -> (cont   , conts   , c:conann , congen   , coninst   )
    EqUnion _ _ _ _ -> (cont   , conts   , c:conann , congen   , coninst   )
    EqTimes _ _ _ _ -> (cont   , conts   , c:conann , congen   , coninst   )
    EqCond  _ _ _ _ -> (cont   , conts   , c:conann , congen   , coninst   )
    EqGen   _ _ _   -> (cont   , conts   , conann   , c:congen , coninst   )
    EqInst  _ _ _   -> (cont   , conts   , conann   , congen   , c:coninst )

{- simplifyTss -}
simplifyTss :: Sub -> Fresh Sub
simplifyTss (Sub subt subts subann) = do
    substs <- mapM simplifyTs subts
    let subts' = Map.map snd substs
        subs' = map fst $ Map.elems substs
    return $ foldr (-$-) (Sub subt subts' subann) subs'
    where
        simplifyTs :: Ts -> Fresh (Sub,Ts)
        simplifyTs (TsVar i) = return (idSub, TsVar i)
        simplifyTs (Ts is [] t) = return (idSub, Ts is [] t)
        simplifyTs (Ts is ct t) = do
            (subs1,ct') <- solveConstraints ct
            let t' = subs1 -$- t
                is' = Set.intersection is (Set.union (freevars ct') (freevars t'))
            return (subs1, Ts is' ct' t')
        simplifyTs (TsAnn anno ts) = mapSnd (TsAnn anno) <$> simplifyTs ts

solveConstraints' :: Constraints -> Fresh (Sub,Constraints)
solveConstraints' [] = return (idSub,[])
solveConstraints' (c:cs) = do
    (subs,ct) <- solveConstraint c
    subs' <- simplifyTss subs
    let cs' = map (subs' -$-) cs
    mapSnd (ct ++) <$> (mapFst (-$- subs') <$> (solveConstraints' cs'))

solveConstraint :: Constraint -> Fresh (Sub,Constraints)
solveConstraint (EqT d t1 t2) = return (throwPossibleErr ("EqT:" ++ d) $ tryUnify t1 t2,[])
solveConstraint (EqTs d ts1 ts2) = return (throwPossibleErr ("EqTs:" ++ d) $ tryUnifyTs ts1 ts2,[])
solveConstraint (EqGen d ts (t,ct,env)) = do
    (subs,ct') <- solveConstraints ct
    let t' = subs -$- t
        env' = subs -$- env
        fvctt = (Set.union (freevars ct') (freevars t'))
        fvenvann = (Set.union (freevars env') (Set.empty)) -- TODO: usage | demand Set.empty == t^^(ann1,ann2)
        fv = fvctt Set.\\ fvenvann
    return (subs,[ EqTs d ts (Ts fv ct' t') ])
solveConstraint eq@(EqInst d _ ts@(TsVar _)) = return (idSub, [eq])
solveConstraint (EqInst d t ts@(Ts _ _ st)) = do
    uniqueId <- getFresh
    let (uniqueId',ts2t_,ct) = instTs2T ("EqInst " ++ d) uniqueId ts
    putFresh $ uniqueId' + 1
    return (idSub,[ EqT d t ts2t_ ] ++ ct)
solveConstraint eq = internalError "Types.hs" "solveConstraint" ("Eq not yet supported: " ++ show eq)

throwPossibleErr :: String -> Either String a -> a
throwPossibleErr d possibleErr = case possibleErr of
    Right subs -> subs
    Left err -> internalError "Types.hs" "solveConstraint" ("Constraint : " ++ d ++ " : " ++ err)

tryUnify :: T -> T -> Either String Sub
tryUnify t1 t2 = traceUnify t1 t2 $ case (t1, t2) of
    (TAp (TAp (TCon "->") _) _, TAp (TAp (TCon "=>") _) _) -> tryUnify t2 t1
    (TAp (TAp (TCon "=>") preds1) t3, TAp (TAp (TCon "=>") preds2) t4) -> do
        subs1 <- tryUnify preds1 preds2
        subs2 <- tryUnify (subs1 -$- t3) (subs1 -$- t4)
        Right $ subs2 -$- subs1
    (TAp (TAp (TCon "=>") (TAp p preds)) t3, TAp (TAp (TCon "->") t4) t5) -> do
        subs1 <- tryUnify p t4
        subs2 <- tryUnify (subs1 -$- (TAp (TAp (TCon "=>") preds) t3)) (subs1 -$- t5)
        Right $ subs2 -$- subs1
    (TAp (TAp (TCon "=>") p) t3, TAp (TAp (TCon "->") t4) t5) -> do
            subs1 <- tryUnify p t4
            subs2 <- tryUnify (subs1 -$- t3) (subs1 -$- t5)
            Right $ subs2 -$- subs1
    (TAp (TAp (TCon "->") t3) t4, TAp (TAp (TCon "->") t5) t6) -> do
        subs1 <- tryUnify t3 t5
        subs2 <- tryUnify (subs1 -$- t4) (subs1 -$- t6)
        Right $ subs2 -$- subs1
    (TAp t3 t4, TAp t5 t6) -> do
        subs1 <- tryUnify t3 t5
        subs2 <- tryUnify (subs1 -$- t4) (subs1 -$- t6)
        Right $ subs2 -$- subs1
    (TPred s1 t3, TPred s2 t4) ->
        if s1 == s2
         then tryUnify t3 t4
         else failUnify "Unequal predicates" t1 t2
    (TCon n1, TCon n2) -> if n1 == n2 then Right idSub else failUnify "Unequal typeconstructors" t1 t2
    (TVar a1, a2@(TVar _)) -> Right $ sub a1 a2
    (TVar a1, t) -> if not $ a1 `isfreein` t then Right $ sub a1 t else failUnify "Not free" t1 t2
    (_, TVar _) -> tryUnify t2 t1
    (TPred s1 t3, _) -> case s1 of -- EqTy "Decl"
        "Eq" -> tryUnify (t3 |-> t3 |-> TCon "Bool") t2
        "Show" -> tryUnify (t3 |-> (TAp (TCon "[]") (TCon "Char"))) t2
        _ -> failUnify ("No function for " ++ s1 ++ "?") t1 t2
    (_, TPred _ _) -> tryUnify t2 t1

    _ -> failUnify "?" t1 t2

tryUnifyTs :: Ts -> Ts -> Either String Sub
tryUnifyTs ts1 ts2 = traceUnify ts1 ts2 $ case (ts1,ts2) of
    (TsVar a1, t) -> if not $ a1 `isfreein` t then Right $ sub a1 t else failUnify "Not free" ts1 ts2
    _ -> failUnify "?" ts1 ts2

failUnify :: Show a => String -> a -> a -> Either String b
failUnify reason u1 u2 = Left $ "\nUnable to unify u1: " ++ show u1 ++ " | with u2: " ++ show u2 ++ " | because : " ++ reason

traceUnify :: Show a => a -> a -> Either String b -> Either String b
traceUnify u1 u2 stacktrace = do -- creating a stacktrace on a fail
    case stacktrace of
        Left err -> Left $ err ++ "\n=> stacktrace: " ++ (fromLeft $ failUnify "stacktrace" u1 u2)
        _ -> stacktrace
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