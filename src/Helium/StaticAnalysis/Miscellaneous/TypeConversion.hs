{-| Module      :  TypeConversion
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    The conversion from UHA types to Tp (a simpler representation), and vice versa.
-}

module Helium.StaticAnalysis.Miscellaneous.TypeConversion where


import Helium.Syntax.UHA_Utils (getNameName, nameFromString)
import Helium.Syntax.UHA_Range (noRange)
import Helium.Utils.Utils (internalError)
import Data.Maybe
import qualified Data.Map as M
import Helium.Syntax.UHA_Syntax
import Control.Arrow

import Top.Types
import Data.List
import Control.Monad.State


----------------------------------------------------------------------
-- conversion functions from and to UHA

type ReservedVariables = Names

namesInTypes :: Types -> Names
namesInTypes = foldr (union . namesInType) []

namesInType :: Type -> Names
namesInType uhaType = case uhaType of

      Type_Application _ _ fun args -> namesInTypes (fun : args)
      Type_Variable _ name          -> [name]
      Type_Constructor _ _          -> []
      Type_Parenthesized _ t        -> namesInType t
      Type_Qualified _ _ t          -> namesInType t
      Type_Forall{}                 -> internalError "TypeConversion.hs" "namesInType" "universal types are currently not supported"
      Type_Exists{}                 -> internalError "TypeConversion.hs" "namesInType" "existential types are currently not supported"

-- name maps play an important role in converting since they map UHA type variables (string) to TVar's (int)
makeNameMap :: Names -> [(Name,Tp)]
makeNameMap = flip zip (map TVar [0..])

-- also return the name map
makeTpSchemeFromType' :: Type -> (TpScheme, [(Int, Name)])
makeTpSchemeFromType' uhaType =
   let names   = namesInType uhaType
       nameMap = makeNameMap names
       intMap  = zip [0..] names
       context = predicatesFromContext nameMap uhaType
       tp      = makeTpFromType nameMap uhaType
       scheme  = Quantification (ftv tp, [ (i,getNameName n) | (n,TVar i) <- nameMap], context .=>. tp)
   in (scheme, intMap)



makeTpSchemeFromType :: Type -> TpScheme
makeTpSchemeFromType = fst . makeTpSchemeFromType'

addSimpleTypeContextToType :: SimpleType -> TpScheme -> TpScheme
addSimpleTypeContextToType (SimpleType_SimpleType _ name typevariables ) (Quantification (freeTV, nameMap', Qualification (prep, tp)))  = --(Quantification (freeTV, nameMap, qualif))
    let nameMap = makeNameMap typevariables
        context = concatMap (nameToPredicate nameMap) typevariables
    in Quantification (freeTV, nub $ [ (i,getNameName n) | (n,TVar i) <- nameMap] ++ nameMap', Qualification (prep ++ context, tp))
    where
        nameToPredicate :: [(Name, Tp)] -> Name -> [Predicate]
        nameToPredicate nameMap tv = case lookup tv nameMap of
            Nothing -> []
            Just tpe -> [Predicate (getNameName name) tpe]

addPredicateToType :: Predicate -> TpScheme -> TpScheme
addPredicateToType prd (Quantification (freeTV, nameMap', Qualification (prep, tp))) = Quantification (freeTV, nameMap', Qualification (prd : prep, tp))

classMemberEnvironmentAddContext :: Name -> (Names, [(Name, TpScheme, Bool, Bool)]) -> (Names, [(Name, TpScheme, Bool, Bool)])
classMemberEnvironmentAddContext className members = Control.Arrow.second mapFunctions members
        where   mapFunctions = map updateFunc
                updateFunc (name, tpscheme, b1, b2) = let 
                    tpUpdated = addPredicateToType prd tpscheme
                    prd = Predicate (getNameName className) tvar
                    tvar = TVar $ fst $ fromJust $ find (\x -> snd x == show (head $ fst members)) (getQuantorMap tpscheme)
                    in (name, tpUpdated, b1, b2)
                
addContextToType :: Name -> [(Name, Tp)] -> TpScheme -> TpScheme
addContextToType name nameMap (Quantification (freeTV, nameMap', Qualification (prep, tp)))  = --(Quantification (freeTV, nameMap, qualif))
    let typevariables = map fst nameMap
        context = concatMap (nameToPredicate nameMap) typevariables
    in Quantification (nub freeTV, nub $ [ (i,getNameName n) | (n,TVar i) <- nameMap] ++ nameMap', Qualification (prep ++ context, tp))
    where
        nameToPredicate :: [(Name, Tp)] -> Name -> [Predicate]
        nameToPredicate nmeMap tv = case lookup tv nmeMap of
            Nothing -> []
            Just tpe -> [Predicate (getNameName name) tpe]
{-}
            substituteClassVariables    :: TpScheme -- ^ The type which has to substituted
            -> Name     -- ^ The type variable of the class
            -> Tp       -- ^ The beta which has to be placed in place
            -> TpScheme
substituteClassVariables tps classVariable beta = ntps
where
unqual = unquantify tps 
ntps = quantify (map fst nqmap) ntp
ntp = substitution |-> unqual
nqmap = filter (\x -> snd x /= cvString ) qmap
qmap = getQuantorMap tps
cvString = getNameName classVariable
substitution = listToSubstitution [(numb, beta) | (numb, tvar) <- qmap, tvar == cvString]
-}

-- addSuperClassContext @superClasses @instsType $


superClassToPredicate ::  [(Name, Tp)] -> (String, Name) -> Predicate
superClassToPredicate classBetaVar (superClassName, typeVariable) = prd
    where
        err     = error $  "Invalid type variable" ++ show classBetaVar ++ show typeVariable
        predVar = fromMaybe err $ lookup typeVariable classBetaVar
        prd     = Predicate superClassName predVar


{-superClassToPredicate :: [(Name, Tp)] -> (Name, [TpScheme]) -> Predicate
superClassToPredicate classVariables (superClassName, tpVars) = 
    let
        var = show $ head tpVars
        err = error "Unknown class variable"
        tp = fromMaybe err (lookup var $ map (\(n, tp) -> (getNameName n, tp)) classVariables)
    in Predicate (getNameName superClassName) tp-}


addSuperClassContext :: (String, [TpScheme])-> Tp -> (Name, Tp) -> Tp -> TpScheme -> TpScheme
addSuperClassContext superClass _ classBetaVar _ typeScheme = tpScheme
    where   tpScheme = updateType superClass typeScheme
        --add context where every variable is replaced with type variable in instanceType 
            updateType :: (String, [TpScheme]) -> TpScheme -> TpScheme
            updateType (superClassName, typeVariables) locTpScheme =
                let 
                    nameMap = filter (\x -> snd x == getNameName (fst classBetaVar)) $ concatMap getQuantorMap typeVariables 
                    predVar  | null nameMap = error "Invalid type variable"
                             | otherwise = snd classBetaVar
                    updatedContext = Predicate superClassName predVar
                    substitutedTp = addPredicateToType updatedContext locTpScheme
                in substitutedTp

replaceName :: (Name, Tp) -> TpScheme -> TpScheme
replaceName repVar tpscheme = let
    vartp :: [(Int, String)]
    vartp = filter (\(_, s)-> (s == (getNameName $ fst repVar))) $ getQuantorMap tpscheme
    nqmap = getQuantorMap tpscheme \\ vartp
    vars = quantifiers tpscheme \\ map fst vartp
    in Quantification (vars, nqmap, (M.fromList $ map (\v -> (fst v, snd repVar)) vartp) |-> unquantify tpscheme)


predicatesFromContext :: [(Name,Tp)] -> Type -> Predicates
predicatesFromContext nameMap (Type_Qualified _ is _) =
   concatMap predicateFromContext is
   where
     predicateFromContext (ContextItem_ContextItem _ cn [Type_Variable _ vn]) =
       case lookup vn nameMap of
         Nothing -> []
         Just tp -> [Predicate (getNameName cn) tp]
     predicateFromContext _ = internalError "TypeConversion.hs" "predicateFromContext" "malformed type in context"
predicatesFromContext _ _   = []

makeTpFromType' :: Type -> Tp
makeTpFromType' = makeTpFromType =<< makeNameMap . namesInType

makeTpFromType :: [(Name,Tp)] -> Type -> Tp
makeTpFromType nameMap = rec_
  where
        rec_ :: Type -> Tp
        rec_ uhaType = case uhaType of
             Type_Application _ _ fun args -> foldl TApp (rec_ fun) (map rec_ args)
             Type_Variable _ name          -> fromMaybe (TCon "???") (lookup name nameMap)
             Type_Constructor _ name       -> TCon (getNameName name)
             Type_Parenthesized _ t        -> rec_ t
             Type_Qualified _ _ t          -> rec_ t
             Type_Forall{}                 -> internalError "TypeConversion.hs" "makeTpFromType" "universal types are currently not supported"
             Type_Exists{}                 -> internalError "TypeConversion.hs" "makeTpFromType" "existential types are currently not supported"

convertFromSimpleTypeAndTypes :: SimpleType -> Types -> (Tp,Tps)
convertFromSimpleTypeAndTypes stp  tps =
   let SimpleType_SimpleType _ name typevariables = stp
       nameMap    = makeNameMap (foldr union [] (typevariables : map namesInType tps))
       simpletype = foldl TApp (TCon (getNameName name)) (take (length typevariables) (map TVar [0..]))
   in (simpletype,map (makeTpFromType nameMap) tps)

makeTypeFromTp :: Tp -> Type
makeTypeFromTp t =
    let (x,xs) = leftSpine t
    in if null xs
        then f x
        else Type_Application noRange True (f x) (map makeTypeFromTp xs)
   where f (TVar i) = Type_Variable noRange    (nameFromString ('v' : show i))
         f (TCon s) = Type_Constructor noRange (nameFromString s)
         f (TApp _ _) = error "TApp case in makeTypeFromTp"

         

showInstanceType :: Tp -> String
showInstanceType (TCon c) = c
showInstanceType (TApp f1 f2) = showInstanceType f1 ++ showInstanceType f2
showInstanceType (TVar _) = ""
            

class Freshen a where
    freshen :: Int -> a -> (a, Int)
    freshenWithMapping :: [(Int, Int)] -> Int -> a -> ([(Int, Int)], (a, Int))
    freshen n t = snd $ freshenWithMapping [] n t
   
instance Freshen Tp where
    freshenWithMapping mapping n tp = (\(tp', (n', m'))->(m', (tp', n'))) $ runState (freshenHelper tp) (n, mapping) 
        where
            freshenHelper :: Tp -> State (Int, [(Int, Int)]) Tp
            freshenHelper (TCon cn) = return (TCon cn)
            freshenHelper (TVar v') = do
                    (uniq, locMapping) <- get
                    case lookup v' locMapping of
                        Just v -> return (TVar v)
                        Nothing -> put (uniq + 1, (v', uniq) : locMapping) >> return (TVar uniq)
            freshenHelper (TApp a1 a2) = do
                t1 <- freshenHelper a1
                t2 <- freshenHelper a2
                return $ TApp t1 t2

instance Freshen Predicate where
    freshenWithMapping mapping n (Predicate name tp) = let
        (mapping', (tp', b')) = freshenWithMapping mapping n tp
        in (mapping', (Predicate name tp', b'))
        
instance Freshen a => Freshen [a] where
    freshenWithMapping mapping n [] = (mapping, ([], n))
    freshenWithMapping mapping n (p:ps) = let
        (mapping', (p', n')) = freshenWithMapping mapping n p
        (mapping'', (ps', n'')) = freshenWithMapping mapping' n' ps
        in (mapping'', (p':ps', n''))
        

instance (Freshen a, Freshen b) => Freshen (Qualification a b) where
    freshenWithMapping mapping n (Qualification (prd, tp)) = let
        (mapping', (prd', b')) = freshenWithMapping mapping n prd
        (_mapping'', (tp', b'')) = freshenWithMapping mapping' b' tp
        in (mapping', (Qualification (prd', tp'), b''))

combineTps :: Tp -> TpScheme -> [(String, Tp)]
combineTps tp tpscheme = combineTpsHelper (getQuantorMap tpscheme) tp (unqualify $ unquantify tpscheme)
    where 
        err = error "Error in mapping"
        combineTpsHelper :: [(Int, String)] -> Tp -> Tp -> [(String, Tp)]
        combineTpsHelper _       (TCon _) (TCon _) = []
        combineTpsHelper mapping (TVar v1) (TVar v2) = return (fromMaybe err $ lookup v2 mapping, TVar v1)
        combineTpsHelper mapping (TApp f1 a1) (TApp f2 a2) = let
            f1Mapping = combineTpsHelper mapping f1 f2
            f2Mapping = combineTpsHelper mapping a1 a2
            in nub (f1Mapping ++ f2Mapping)
        combineTpsHelper _ _ _ = err
