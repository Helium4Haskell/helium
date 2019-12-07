{-| Module      :  CoreUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.CoreUtils
    (   custom, customStrategy
    ,   stringToCore, coreList
    ,   let_, if_, app_, letrec_
    ,   cons, nil
    ,   var, decl
    ,   float, packedString, declarationConstructorType
    ,   declarationType, declarationTypeInPattern, addToTypeEnv
    ,   toCoreType, toCoreTypeNotQuantified, typeToCoreType, typeToCoreTypeMapped
    ,   addLambdas, addLambdasForLambdaExpression, TypeClassContext(..)
    ,   findCoreType, createInstantiation, createRecordInstantiation
    ,   createRecordUpdate, createRecordSelector
    ,   constructorsToCase, constructorToCase
    ,   patternMatchFail, patternAlwaysSucceeds, getTVar
    ,   TypeInferenceOutput(TypeInferenceOutput, importEnv), lookupBeta
    ) where

import Top.Types as Top
import Top.Solver(SolveResult(..))
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfo(ConstraintInfo)
import Top.Types.Substitution(FixpointSubstitution, lookupInt)
import Lvm.Core.Expr
import Lvm.Core.Type as Core
import Lvm.Common.Id
import Lvm.Core.Utils
import Data.Char
import Data.Maybe
import Data.List
import Lvm.Common.Byte(bytesFromString)
import qualified Lvm.Core.Expr as Core
import qualified Data.Map as M
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range
import Helium.Utils.Utils
import Debug.Trace
import Text.PrettyPrint.Leijen (pretty)

lookupBeta :: Int -> TypeInferenceOutput -> Top.Tp
lookupBeta beta typeOutput = lookupInt beta $ substitutionFromResult $ solveResult typeOutput

infixl `app_`

custom :: String -> String -> Custom
custom sort text =
    CustomDecl
        (DeclKindCustom (idFromString sort))
        [CustomBytes (bytesFromString text)]


customStrategy :: String -> Decl a
customStrategy text =
    DeclCustom    
        { declName = idFromString ""
        , declAccess = Defined { accessPublic = True }
        , declKind = DeclKindCustom (idFromString "strategy")
        , declCustoms = [custom "strategy" text]
        }

app_ :: Expr -> Expr -> Expr
app_ f x = Ap f x

let_ :: Id -> Core.Type -> Expr -> Expr -> Expr
let_ x t e b = Let (NonRec (Bind (Variable x t) e)) b

letrec_ :: [CoreDecl] -> Expr -> Expr
letrec_ bs e = 
    Let 
        (Rec 
            [ Bind (Variable ident t) expr
            | DeclValue { declName = ident, declType = t, valueValue = expr } <- bs
            ]
        ) 
        e

-- Function "if_" builds a Core expression of the following form
-- let! guardId = <guardExpr> in 
-- match guardId 
--   True -> <thenExpr>
--   _    -> <elseExpr>
if_ :: Expr -> Expr -> Expr -> Expr
if_ guardExpr thenExpr elseExpr =
    Let 
        (Strict (Bind (Variable guardId typeBool) guardExpr))
        (Match guardId
            [ Alt (PatCon (ConId trueId) [] []) thenExpr
            , Alt PatDefault elseExpr
            ]
        )

-- Function "coreList" builds a linked list of the given expressions
-- Example: coreList tp [e1, e2] ==> 
--   Ap (Ap (Con ":" `ApType` tp) e1) 
--           (Ap (Ap (Con ":" `ApType` tp) e2)
--                    (Con "[]" `ApType` tp)
--           )
coreList :: Core.Type -> [Expr] -> Expr
coreList tp = foldr (cons tp) (nil tp)

cons :: Core.Type -> Expr -> Expr -> Expr
cons tp x xs = ApType (Con (ConId consId)) tp `app_` x `app_` xs

nil :: Core.Type -> Expr
nil tp = ApType (Con (ConId nilId)) tp

nilId, consId, trueId, guardId :: Id 
( nilId : consId :  trueId :  guardId : []) =
   map idFromString ["[]", ":", "True", "guard$"]

-- Function "stringToCore" converts a string to a Core expression
stringToCore :: String -> Expr
stringToCore [] = nil tp
  where
    tp = Core.TCon $ Core.TConDataType $ idFromString "Char"
stringToCore [x] = cons tp (Lit (LitInt (ord x) IntTypeChar)) $ nil tp
  where
    tp = Core.TCon $ Core.TConDataType $ idFromString "Char"
stringToCore xs = var "$primPackedToString" `app_` packedString xs

var :: String -> Expr
var x = Var (idFromString x)

--Core.Lit (Core.LitDouble (read @value))   PUSHFLOAT nog niet geimplementeerd
float :: String -> Expr
float f = 
    Core.Ap 
        (Core.Var (idFromString "$primStringToFloat")) 
        ( Core.Lit (Core.LitBytes (bytesFromString f)) )

addToTypeEnv :: TypeEnvironment -> [(Name, TpScheme)] -> TypeEnvironment
addToTypeEnv = foldr (\(name, tpScheme) env -> M.insert name tpScheme env)

decl :: Bool -> String -> Core.Type -> Expr -> CoreDecl
decl isPublic x t e = 
    DeclValue 
        { declName = idFromString x
        , declAccess = Defined { accessPublic = isPublic }
        , declType = t
        , valueValue = e
        , declCustoms = []
        }

getTVar :: Top.Tp -> Maybe Int
getTVar (Top.TVar idx) = Just idx
getTVar _ = Nothing
      
packedString :: String -> Expr
packedString s = Lit (LitBytes (bytesFromString s))

data TypeClassContext
    = TCCNone
    | TCCClass
    | TCCInstance Id Core.Type

data TypeInferenceOutput = TypeInferenceOutput
  { solveResult :: !(SolveResult ConstraintInfo)
  , fullTypeSchemes :: !(M.Map NameWithRange Top.TpScheme)
  , importEnv :: !ImportEnvironment
  }

declarationTpScheme :: TypeInferenceOutput -> TypeClassContext -> Name -> Maybe Top.TpScheme
declarationTpScheme (TypeInferenceOutput solveResult fullTypeSchemes _) TCCNone name = fmap (substitutionFromResult solveResult |->) $ M.lookup (NameWithRange name) fullTypeSchemes
declarationTpScheme (TypeInferenceOutput _ _ importEnv) _ name = M.lookup name (typeEnvironment importEnv)

-- Finds the instantiation of a declaration in a type class instance.
-- E.g. Num a => a -> a
-- For a function in an instance for `Num Int` this will return (a, Int)
instantiationInTypeClassInstance :: TypeClassContext -> Top.TpScheme -> Maybe (Int, Core.Type)
instantiationInTypeClassInstance (TCCInstance className instanceType) (Top.Quantification (_, qmap, (Top.Qualification (Predicate _ (Top.TVar typeVar) : _, _))))
  = Just (typeVar, instanceType)
instantiationInTypeClassInstance _ _ = Nothing

declarationConstructorTypeScheme :: ImportEnvironment -> Name -> Top.TpScheme
declarationConstructorTypeScheme importEnv name = case M.lookup name $ valueConstructors importEnv of
  Just (Quantification (quantors, qmap, qtp)) -> 
    let
      -- We must assure that the order of the quantors matches the order in which the type variables
      -- appear in the data type / return type of the constructor, eg [a, b] in
      -- a -> Either a b
      
      Qualification (_, tp) = qtp

      -- Finds the (order of the) type arguments
      findTypeArgs :: Top.Tp -> [Int]
      findTypeArgs (Top.TApp (Top.TApp (Top.TCon "->") tArg) tReturn) = findTypeArgs tReturn
      findTypeArgs t = consume [] t
        where
          consume accum (Top.TApp t (Top.TVar idx)) = consume (idx : accum) t
          consume accum _ = accum
      
      quantors' = findTypeArgs tp
    in Quantification (quantors', qmap, qtp)
  Nothing -> internalError "CodeGeneration" "declarationConstructorTypeScheme" ("Constructor not found: " ++ show name)

declarationConstructorType :: ImportEnvironment -> Name -> [Bool] -> Core.Type
declarationConstructorType importEnv name strictness = setStrictness strictness $ toCoreType $ declarationConstructorTypeScheme importEnv name
  where
    setStrictness :: [Bool] -> Core.Type -> Core.Type
    setStrictness stricts (TForall quantor kind tp) = TForall quantor kind $ setStrictness stricts tp
    setStrictness (strict : stricts) (Core.TAp (Core.TAp (Core.TCon Core.TConFun) t1) t2) =
      Core.TAp (Core.TAp (Core.TCon Core.TConFun) $ Core.typeSetStrict strict t1) $ setStrictness stricts t2
    setStrictness _ tp = tp

declarationType :: TypeInferenceOutput -> TypeClassContext -> Name -> (Top.TpScheme, Core.Type)
declarationType typeOutput context name =
  case declarationTpScheme typeOutput context name of
    Just ty ->
      let
        coreType = toCoreType ty
      in case instantiationInTypeClassInstance context ty of
        Just (typeVar, instanceType) -> (ty, Core.typeInstantiate typeVar instanceType coreType)
        Nothing -> (ty, coreType)
    Nothing -> internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name)

declarationTypeInPattern :: TypeInferenceOutput -> Name -> Int -> (Top.TpScheme, Core.Type)
declarationTypeInPattern typeOutput name beta = 
  case declarationTpScheme typeOutput TCCNone name of
    Just scheme -> (scheme, toCoreType scheme)
    Nothing ->
      let
        ty = lookupBeta beta $ typeOutput
        scheme = Top.Quantification ([], [], (Top.Qualification ([], ty)))
      in (scheme, typeToCoreType ty)

findCoreType :: TypeInferenceOutput -> Int -> Core.Type
findCoreType typeOutput beta = typeToCoreType $ lookupBeta beta typeOutput

toCoreType :: Top.TpScheme -> Core.Type
toCoreType (Top.Quantification (tvars, qmap, t)) = foldr addTypeVar t' tvars
  where
    t' = qtypeToCoreType qmap t
    addTypeVar index = Core.TForall (typeVarToQuantor qmap index) Core.KStar

toCoreTypeNotQuantified :: Top.TpScheme -> Core.Type
toCoreTypeNotQuantified (Top.Quantification (_, qmap, t)) = qtypeToCoreType qmap t

typeVarToQuantor :: Top.QuantorMap -> Int -> Core.Quantor
typeVarToQuantor qmap index = Core.Quantor index $ lookup index qmap

qtypeToCoreType :: Top.QuantorMap -> Top.QType -> Core.Type
qtypeToCoreType qmap (Top.Qualification (q, t)) = foldr addDictArgument (typeToCoreType' qmap t) q
  where
    addDictArgument predicate = Core.TAp $ Core.TAp (Core.TCon Core.TConFun) arg
      where
        arg = predicateToCoreType qmap predicate

predicateToCoreType :: Top.QuantorMap -> Top.Predicate -> Core.Type
predicateToCoreType qmap (Top.Predicate className tp) =
    Core.TAp (Core.TCon $ TConTypeClassDictionary $ idFromString className) $ typeToCoreType' qmap tp

typeToCoreType :: Top.Tp -> Core.Type
typeToCoreType = typeToCoreType' []

typeToCoreType' :: Top.QuantorMap -> Top.Tp -> Core.Type
typeToCoreType' qmap t = typeToCoreTypeMapped qmap (const Nothing) t

typeToCoreTypeMapped :: Top.QuantorMap -> (Int -> Maybe Core.Type) -> Top.Tp -> Core.Type
typeToCoreTypeMapped qmap f (Top.TVar index) = fromMaybe (Core.TVar index) $ f index
typeToCoreTypeMapped _ _ (Top.TCon name) = Core.TCon c
  where
    c = case name of
        "->" -> Core.TConFun
        "()" -> Core.TConTuple 0
        '(':str
          | dropWhile (==',') str == ")" -> Core.TConTuple (length str)
        _ -> Core.TConDataType $ idFromString name
typeToCoreTypeMapped qmap f (Top.TApp t1 t2) = Core.TAp (typeToCoreTypeMapped qmap f t1) (typeToCoreTypeMapped qmap f t2)

addLambdasForLambdaExpression :: TypeInferenceOutput -> Int -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForLambdaExpression typeOutput beta args expr = addLambdasForType (importEnv typeOutput) [] tp id args [] expr
  where
    tp = lookupBeta beta typeOutput

addLambdas :: TypeInferenceOutput -> TypeClassContext -> Int -> Name -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdas typeOutput context beta name args expr = case declarationTpScheme typeOutput context name of
  Nothing -> internalError "ToCoreDecl" "Declaration" ("Could not find type for declaration " ++ show name)
  Just ty@(Top.Quantification (tvars, qmap, t)) ->
    let
      -- When a binding is annotated with a type, it may have different type variables in the signature
      -- and the body. We use the type variables from the body. We construct a mapping of type variables
      -- of the signatures to type variables used in the body.
      -- Furthermore, in an instance declaration of a type class, a type variable is instantiated with the type
      -- for which the class is implemented. Eg `a -> String` becomes `Int -> String`.
      typeCorrectTVars = lookupBeta beta typeOutput
      instantiation = findInstantiation (importEnv typeOutput) ty typeCorrectTVars
      tvars' = mapMaybe getTVar instantiation
      substitute = Core.typeSubstitutions $ zipWith (\idx typeArg -> (idx, typeToCoreType typeArg)) tvars instantiation
    in foldr (\x e -> Core.Forall (typeVarToQuantor qmap x) Core.KStar e) (addLambdasForQType (importEnv typeOutput) [] t substitute args expr) tvars'

addLambdasForQType :: ImportEnvironment -> QuantorMap -> Top.QType -> (Core.Type -> Core.Type) -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForQType env qmap (Top.Qualification ([], t)) substitute args expr = addLambdasForType env qmap t substitute args [] expr
addLambdasForQType env qmap (Top.Qualification (p : ps, t)) substitute (arg:args) expr =
  Core.Lam False (Core.Variable arg $ substitute $ predicateToCoreType qmap p) $ addLambdasForQType env qmap (Top.Qualification (ps, t)) substitute args expr

addLambdasForType :: ImportEnvironment -> QuantorMap -> Top.Tp -> (Core.Type -> Core.Type) -> [Id] -> [Core.Type] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForType _ qmap retType substitute [] accumArgTypes expr = expr (reverse accumArgTypes) $ substitute $ typeToCoreType' qmap retType
addLambdasForType env qmap (Top.TApp (Top.TApp (Top.TCon "->") argType) retType) substitute (arg:args) accumArgTypes expr =
  Core.Lam False (Core.Variable arg tp)
    $ addLambdasForType env qmap retType substitute args (tp : accumArgTypes) expr
  where
    tp = substitute $ typeToCoreType' qmap argType
addLambdasForType env qmap tp substitute args accumArgTypes expr =
    case tp' of
        -- Verify that the resulting type is a function type
        Top.TApp (Top.TApp (Top.TCon "->") _) _ -> addLambdasForType env qmap tp' substitute args accumArgTypes expr
        _ -> internalError "ToCoreDecl" "Declaration" ("Expected a function type, got " ++ show tp' ++ " instead")
    where
        tp' = applyTypeSynonym env tp []

applyTypeSynonym :: ImportEnvironment -> Top.Tp -> Top.Tps -> Top.Tp
applyTypeSynonym env tp@(Top.TCon name) tps = case M.lookup (nameFromString name) $ typeSynonyms env of
    Just (arity, fn) ->
        let
            tps' = drop arity tps
            tp' = fn (take arity tps)
        in
            applyTypeSynonym env tp' tps'
    _ -> foldl (Top.TApp) tp tps
applyTypeSynonym env (Top.TApp t1 t2) tps = applyTypeSynonym env t1 (t2 : tps)
applyTypeSynonym env (Top.TVar a) tps = foldl (Top.TApp) (Top.TVar a) tps

createInstantiation :: TypeInferenceOutput -> TypeEnvironment -> Name -> Bool -> Int -> Core.Expr
createInstantiation typeOutput typeEnv name isConstructor beta = case maybeScheme of
  Nothing -> expr
  Just scheme -> foldl (\e t -> Core.ApType e $ typeToCoreType t) expr $ findInstantiation (importEnv typeOutput) scheme tp
  where
    expr
      | isConstructor = Core.Con $ Core.ConId $ idFromName name
      | otherwise = Core.Var $ idFromName name
    tp = lookupBeta beta typeOutput
    maybeScheme
      | isConstructor = Just $ declarationConstructorTypeScheme (importEnv typeOutput) name
      | otherwise = M.lookup name typeEnv

findInstantiation :: ImportEnvironment -> Top.TpScheme -> Top.Tp -> [Top.Tp]
findInstantiation importEnv t@(Top.Quantification (tvars, _, Top.Qualification (_, tLeft))) tRight
  = fmap (\a -> fromMaybe (Top.TCon "()") $ lookup a instantiations) tvars
  where
    instantiations = traverse (traceShow ("instantiating " ++ show t ++ " with " ++ show tRight) $ tLeft) tRight []
    traverse :: Top.Tp -> Top.Tp -> [(Int, Top.Tp)] -> [(Int, Top.Tp)]
    traverse (Top.TVar a) t2 = ((a, t2) :)
    traverse (Top.TCon _) _ = id
    traverse t1 t2 = traverseNoTypeSynonym (applyTypeSynonym importEnv t1 []) (applyTypeSynonym importEnv t2 [])
    traverseNoTypeSynonym :: Top.Tp -> Top.Tp -> [(Int, Top.Tp)] -> [(Int, Top.Tp)]
    traverseNoTypeSynonym (Top.TApp tl1 tl2) (Top.TApp tr1 tr2) =
      traverseNoTypeSynonym tl1 tr1 . traverse tl2 tr2
    traverseNoTypeSynonym t1 t2 = traverse t1 t2

{-
Puts the fields in the correct order, 
and applies them in that order to the constructor expression.

Fills the empty fields with `undefined`
-}
createRecordInstantiation :: TypeInferenceOutput 
                            -> Name 
                            {- Field name, argument to pass to field, beta var for the argument -}
                            -> [(Name, Core.Expr, Int)] 
                            -> Int 
                            -> Core.Expr
createRecordInstantiation typeOutput name bindings beta
    = foldl app_
        (foldl (\e t -> Core.ApType e $ typeToCoreType t) constrExpr tvar)
          sortedBinds
  where
    impEnv = importEnv typeOutput
    recordEnv = recordEnvironment impEnv
    recordFields = M.assocs $ fromMaybe (err "constructor could not be found") (M.lookup name recordEnv)
    err = internalError "CoreUtils" "createRecordInstantiation"

    constrExpr = Core.Con $ Core.ConId $ idFromName name
    -- Find an instantiation of the type variables using the type inferred for the
    -- constructor and the defined typescheme of the constructor 
    constrTps = declarationConstructorTypeScheme impEnv name
    outputTp = lookupBeta beta typeOutput
    tvar = findInstantiation impEnv constrTps outputTp

    binds = map (\(i, expr, _) -> (i, expr)) bindings
    sortedFields = zip tvar (sortOn (\(n, (i, _, _, _)) -> i) recordFields)
    sortedBinds
      = map (\(t, (n, x)) -> fieldToExpr (snd4 x) t (lookup n binds)) sortedFields

    strictOrUndefined :: Bool -> Tp -> Core.Expr
    strictOrUndefined strict tp = if strict
      then err "undefined strict field construction"
      else coreUndefined impEnv tp

    fieldToExpr :: Bool -> Tp -> Maybe Core.Expr -> Core.Expr
    fieldToExpr strict tp m = case m of
      Nothing -> strictOrUndefined strict tp
      Just expr -> expr

{-
Transforms

>> data Foo = Foo { a :: Int, b :: Int }
>>          | Bar { a :: Int }
>> 
>> f x = x { a = 1 }

into

>> f x = (\y a -> case y of
                  Foo _ b -> Foo a b
                  _ -> case y of
                      Bar _ -> Bar a
                      _     -> patternMatchFail)
        x 1
-}
-- TODO: Refactor to use constructorsToCase
createRecordUpdate :: TypeInferenceOutput 
                    -> ImportEnvironment 
                    {- Old record -}
                    -> Core.Expr 
                    {- Beta variable of the old expression -}
                    -> Int
                    {- Beta variable of the new expression -}
                    -> Int
                    {- Beta variable containing the type of the emulated constructor -}
                    -> Int
                    {- Field name, argument to pass to field, beta var for the argument -}
                    -> [(Name, Core.Expr, Int)] 
                    {- Range for the overal expression -}
                    -> Range
                    -> Core.Expr
createRecordUpdate typeOutput importEnv old oldBeta beta betaFunc bindings range
    = foldl app_ (func `app_` old) (map thd4 args)
  where
    betaToType :: Int -> Core.Type
    betaToType b = typeToCoreType $ lookupBeta b typeOutput

    oldTp = lookupBeta oldBeta typeOutput
    newTp = betaToType beta
    scrutineeVar = Variable (idFromString "x$") (typeToCoreType oldTp)

    func = setTopArgs (map (\(n, i, e, t) -> (strict n, Variable i (betaToType t))) args) body
    strict n = snd4 $ fromMaybe (coreUtilsError "createRecordUpdate" 
      ("field could not be found" ++ show n)) (M.lookup n allFields)

    constructors = mapMaybe (`M.lookup` fieldLookup importEnv) newFields
    relevantConstructors = if null constructors
      then conNotFound 
      else foldr1 intersect constructors

    recordEnv = recordEnvironment importEnv
    allFields = M.unions $ mapMaybe (`M.lookup` recordEnv) relevantConstructors
    oldFields = map (\n -> (n, idFromString (show n))) $ M.keys $ foldr M.delete allFields newFields
    newFields = map fst3 bindings
    conNotFound = coreUtilsError "createRecordUpdate" "no constructor could be found"
    
    args :: [(Name, Id, Core.Expr, Int)]
    args = map (\(n, e, t) -> (n, idFromString (show n), e, t)) bindings

    body :: Core.Expr
    body = body' relevantConstructors

    body' :: [Name] -> Core.Expr
    body' []     = patternMatchFail "record expression binding" newTp range
    body' (c:cs) = constructorToCase' (variableName scrutineeVar) c oldFields (body' cs)

    -- Chain the arguments
    setTopArgs :: [(Bool, Variable)] -> Core.Expr -> Core.Expr
    setTopArgs xs e = Lam True scrutineeVar (foldr (uncurry Lam) e xs)

    constructorToCase' :: Id -> Name -> [(Name, Id)] -> Core.Expr -> Core.Expr
    constructorToCase' scrutinee c fs
      = constructorToCase importEnv c scrutinee tvars fs exec
      where 
        tvars           = findInstantiation importEnv (generalizeAll $ [] .=>. constrTp) oldTp
        constrTps       = fromMaybe err $ M.lookup c (valueConstructors importEnv)
        constrTp        = snd $ functionSpine $ unqualify $ unquantify constrTps
        err             = coreUtilsError "constructorToCase'" "non-existing constructor"
        fields          = fromMaybe conNotFound $ M.lookup c recordEnv
        sortedFields    = sortOn (fst4 . snd) (M.assocs fields)
        -- constructorFunc = createInstantiation typeOutput (typeEnvironment importEnv) c True beta
        exec            =
          createRecordInstantiation typeOutput c
            (map (\x -> (fst x, Var (idFromString (show (fst x))), undefined)) sortedFields) betaFunc
          -- foldl Ap constructorFunc (map (Var . idFromString . show . fst) sortedFields)

{-
Transforms 

>> data Foo = Foo { a :: Int, b :: Int }
>>          | Bar { a :: Int }
>> 
>> f x = a x

into

>> f x = (\y -> case y of
                  Foo a _ -> a
                  _ -> case y of
                      Bar a -> a
                      _     -> patternMatchFail)
        x
-}
createRecordSelector :: ImportEnvironment
                    -> Range
                    -> Name
                    -> Tp
                    -> Core.Expr
createRecordSelector importEnv r field retTp
  = foldr (\x e -> Core.Forall (typeVarToQuantor qmap x) Core.KStar e) (Lam True scrutVar select) tvars
  where
    ty@(Top.Quantification (_, qmap, _)) = fromMaybe (notFound constr) $ do 
      fields <- M.lookup constr (recordEnvironment importEnv)
      (i, s, t, ts) <- M.lookup field fields
      return ts
    tvars = mapMaybe getTVar $ findInstantiation importEnv ty (unqualify (unquantify ty))

    select = constructorsToCase importEnv scrutId (typeToCoreType retTp) r atEachConstructor
    fieldId = idFromString (show field)
    scrutId = idFromString "x$"
    atEachConstructor = map (\n -> (n, [(field, fieldId)], Var fieldId, instantiated n)) constrs
    instantiated n = fromMaybe (notFound n) $ do
      constrTps <- M.lookup n (valueConstructors importEnv)
      return $ findInstantiation importEnv constrTps (unqualify (unquantify constrTps))


    constrs = fromMaybe (notFound field) $ field `M.lookup` fieldLookup importEnv
    constr = case constrs of
      [] -> notFound "1"
      xs -> head xs
    constrTps
      = fromMaybe (notFound constr) $ M.lookup constr (valueConstructors importEnv)

    scrutTp = unqualify (unquantify constrTps)
    scrutType = snd $ Core.typeExtractFunction $ toCoreTypeNotQuantified constrTps
    scrutVar = Variable scrutId scrutType
    notFound f = coreUtilsError "createRecordSelector" 
      ("no appropriate constructor found for field " ++ show f)

-- Helper function for executing code for a multiple constructors
constructorsToCase :: ImportEnvironment 
                    -> Id           {- Scrutinee's Id -}
                    -> Core.Type    {- Result type -}
                    -> Range        {- Range of the overal expression -}
                    {- (Constructor name, Fields to include, What to execute) -}
                    -> [(Name, [(Name, Id)], Core.Expr, [Tp])]
                    -> Core.Expr
constructorsToCase importEnv scrutId resType r fs 
  = case fs of
    [] -> patternMatchFail "pattern binding" resType r
    ((n, fields, exec, tps):xs) -> constructorToCase importEnv n scrutId tps fields exec $ 
                          constructorsToCase importEnv scrutId resType r xs

-- Helper function for executing code for a specific constructor
constructorToCase :: ImportEnvironment 
                    -> Name           {- Constructor name -}
                    -> Id             {- Scrutinee -}
                    -> [Tp]           {- Typevariables to instantiate the constructor to -} 
                    -> [(Name, Id)]   {- Fields to include -}
                    -> Core.Expr      {- What to execute if it matches -}
                    -> Core.Expr      {- What to execute otherwise -}
                    -> Core.Expr
constructorToCase importEnv constr scrutinee tps fs exec continue
  = Match scrutinee
      [ Alt patt exec
      , Alt PatDefault continue
      ]
  where
    args = map (\(n, _) -> placeholder n fieldsToReuse) sortedFields
    patt = PatCon (ConId constructor) (map typeToCoreType tps) args

    constructor = idFromString (show constr)
    (fields, constrTps) = fromMaybe (err "Constructor not found") $ do
      fields <- M.lookup constr (recordEnvironment importEnv)
      constrTps <- M.lookup constr (valueConstructors importEnv)
      return (fields, constrTps)

    sortedFields = sortOn (fst4 . snd) (M.assocs fields)
    fieldsToReuse = foldr (M.delete . fst) fields fs
    constrTp = unqualify (unquantify constrTps)

    err = coreUtilsError "constructorToCase"
    placeholder n m
      = case M.lookup n m of
          Nothing -> idFromString (show n)
          Just _ -> idFromString "_"

patternAlwaysSucceeds :: Pattern -> Bool
patternAlwaysSucceeds p = 
    case p of
        Pattern_Variable _ _ -> True
        Pattern_Wildcard _ -> True
        Pattern_As _ _ pat -> patternAlwaysSucceeds pat
        Pattern_Parenthesized _ pat -> patternAlwaysSucceeds pat
        _ -> False

patternMatchFail :: String -> Core.Type -> Range -> Core.Expr
patternMatchFail nodeDescription tp range =
    Core.ApType (var "$primPatternFailPacked") tp
        `app_` packedString (
                    nodeDescription ++ " ranging from " ++ 
                    showPosition start ++ " to " ++ 
                    showPosition (getRangeEnd range) ++ " in module " ++
                    moduleFromPosition start
               )
    where
        start = getRangeStart range

coreUndefined :: ImportEnvironment -> Tp -> Core.Expr
coreUndefined importEnv tp
      = foldl (\e t -> Core.ApType e $ typeToCoreType t) undefinedExpr 
          (findInstantiation importEnv undefinedScheme tp)
    where
      undefinedExpr = Var (idFromString "undefined") 
      undefinedName = Name_Identifier (coreUtilsError "coreUndefined" "access non-existing range") ["Prelude"] "undefined"
      undefinedScheme = fromMaybe (coreUtilsError "coreUndefined" "undefined not defined") $
          M.lookup undefinedName (typeEnvironment importEnv)

coreUtilsError :: String -> String -> a
coreUtilsError = internalError "CoreUtils"
