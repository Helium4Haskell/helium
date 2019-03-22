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
    ,   toplevelType, declarationType, declarationTypeInPattern, addToTypeEnv
    ,   toCoreType, toCoreTypeNotQuantified, typeToCoreType, typeToCoreTypeMapped
    ,   addLambdas, addLambdasForLambdaExpression, TypeClassContext(..)
    ,   findCoreType, createInstantiation, TypeInferenceOutput(TypeInferenceOutput, importEnv), lookupBeta
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
import Lvm.Common.Byte(bytesFromString)
import qualified Lvm.Core.Expr as Core
import qualified Data.Map as M
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils

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

declarationConstructorType :: ImportEnvironment -> Name -> Core.Type
declarationConstructorType importEnv name = toCoreType $ declarationConstructorTypeScheme importEnv name

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

toplevelType :: Name -> ImportEnvironment -> Bool -> [Custom]
toplevelType name ie isTopLevel
    | isTopLevel = [custom "type" typeString]
    | otherwise  = []
    where
        typeString = maybe
            (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
            show
            (M.lookup name (typeEnvironment ie))

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
      getTVar (Top.TVar idx) = Just idx
      getTVar _ = Nothing
      tvars' = mapMaybe getTVar instantiation
      substitute = Core.typeSubstitutions $ zipWith (\idx typeArg -> (idx, typeToCoreType typeArg)) tvars instantiation
    in foldr (\x e -> Core.Forall (typeVarToQuantor qmap x) Core.KStar e) (addLambdasForQType (importEnv typeOutput) [] t substitute args expr) tvars'

addLambdasForQType :: ImportEnvironment -> QuantorMap -> Top.QType -> (Core.Type -> Core.Type) -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForQType env qmap (Top.Qualification ([], t)) substitute args expr = addLambdasForType env qmap t substitute args [] expr
addLambdasForQType env qmap (Top.Qualification (p : ps, t)) substitute (arg:args) expr =
  Core.Lam (Core.Variable arg $ substitute $ predicateToCoreType qmap p) $ addLambdasForQType env qmap (Top.Qualification (ps, t)) substitute args expr

addLambdasForType :: ImportEnvironment -> QuantorMap -> Top.Tp -> (Core.Type -> Core.Type) -> [Id] -> [Core.Type] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForType _ qmap retType substitute [] accumArgTypes expr = expr (reverse accumArgTypes) $ substitute $ typeToCoreType' qmap retType
addLambdasForType env qmap (Top.TApp (Top.TApp (Top.TCon "->") argType) retType) substitute (arg:args) accumArgTypes expr =
  Core.Lam (Core.Variable arg tp)
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
findInstantiation importEnv (Top.Quantification (tvars, _, Top.Qualification (_, tLeft))) tRight
  = fmap (\a -> fromMaybe (Top.TCon "()") $ lookup a instantiations) tvars
  where
    instantiations = traverse tLeft tRight []
    traverse :: Top.Tp -> Top.Tp -> [(Int, Top.Tp)] -> [(Int, Top.Tp)]
    traverse (Top.TVar a) t2 = ((a, t2) :)
    traverse (Top.TCon _) _ = id
    traverse t1 t2 = traverseNoTypeSynonym (applyTypeSynonym importEnv t1 []) (applyTypeSynonym importEnv t2 [])
    traverseNoTypeSynonym :: Top.Tp -> Top.Tp -> [(Int, Top.Tp)] -> [(Int, Top.Tp)]
    traverseNoTypeSynonym (Top.TApp tl1 tl2) (Top.TApp tr1 tr2) =
      traverseNoTypeSynonym tl1 tr1 . traverse tl2 tr2
    traverseNoTypeSynonym t1 t2 = traverse t1 t2
