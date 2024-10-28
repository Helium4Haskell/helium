{-# LANGUAGE TupleSections, RecordWildCards #-}

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
    ,   float, packedString, declarationConstructorType, addToTypeEnv
    ,   declarationType, declarationTypeInPattern, declarationConstructorTypeScheme
    ,   toCoreType, toCoreTypeNotQuantified, typeToCoreType, typeToCoreTypeMapped
    ,   addLambdas, addLambdasForLambdaExpression, TypeClassContext(..)
    ,   findCoreType, createInstantiation, createRecordInstantiation
    ,   createRecordUpdate, createRecordSelector
    ,   Quantors, emptyQuantors, quantorsFromList, appendQuantors
    ,   patternMatchFail, patternAlwaysSucceeds, getTVar
    ,   TypeInferenceOutput(TypeInferenceOutput, importEnv), lookupBeta
    ,   setExportsPublic
    ) where

import Helium.Top.Top.Types as Top
import Helium.Top.Top.Solver(SolveResult(..))
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfo(ConstraintInfo)
import Helium.Top.Top.Types.Substitution(FixpointSubstitution, lookupInt)
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type as Core
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Utils
import Data.Char
import Data.Maybe
import Data.List
import Helium.Lvm.Common.Byte(bytesFromString)
import qualified Helium.Lvm.Core.Expr as Core
import qualified Data.Map as M
import Helium.Utils.QualifiedTypes (convertClassNameToQualified, convertTpToQualified)
import Data.List(isPrefixOf)
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range
import Helium.Syntax.UHA_Syntax hiding (Module(..))
import Helium.Utils.Utils
import Helium.Syntax.UHA_Syntax ( Name )

lookupBeta :: Int -> TypeInferenceOutput -> Top.Tp
lookupBeta beta typeOutput = lookupInt beta $ substitutionFromResult $ solveResult typeOutput

custom :: String -> String -> Custom
custom sort text =
    CustomDecl
        (DeclKindCustom (idFromString sort))
        [CustomBytes (bytesFromString text)]

customStrategy :: String -> Decl a
customStrategy text =
    DeclCustom
        { declName = idFromString ""
        , declAccess = Export $ idFromString ""
        , declModule = Nothing
        , declKind = DeclKindCustom (idFromString "strategy")
        , declCustoms = [custom "strategy" text]
        }

infixl `app_`

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
        , declAccess = if isPublic then Export $ idFromString x else Private
        , declModule = Nothing
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
  Just (_, (Quantification (quantors, qmap, qtp)), _) ->
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
declarationConstructorType importEnv name strictness = setStrictness strictness $ toCoreType emptyQuantors $ declarationConstructorTypeScheme importEnv name
  where
    setStrictness :: [Bool] -> Core.Type -> Core.Type
    setStrictness stricts (TForall quantor kind tp) = TForall quantor kind $ setStrictness stricts tp
    setStrictness (strict : stricts) (Core.TAp (Core.TAp (Core.TCon Core.TConFun) t1) t2) =
      Core.TAp (Core.TAp (Core.TCon Core.TConFun) $ Core.typeSetStrict strict t1) $ setStrictness stricts t2
    setStrictness _ tp = tp

-- Mapping from Top's type variables to Debruijn indices for Core.
-- The head of the list is the type variable which gets Debruijn index 0,
-- the second element gets index 1, and so on.
newtype Quantors = Quantors [Int]

appendQuantors :: Quantors -> Quantors -> Quantors
appendQuantors (Quantors parent) (Quantors current) = Quantors $ current ++ parent

emptyQuantors :: Quantors
emptyQuantors = Quantors []

quantorsFromList :: [Int] -> Quantors
quantorsFromList = Quantors . reverse

declarationType :: TypeInferenceOutput -> TypeClassContext -> Quantors -> Name -> (Top.TpScheme, Core.Type)
declarationType typeOutput context parent name =
  case declarationTpScheme typeOutput context name of
    Just ty ->
      let
        coreType = toCoreType parent ty
      in case instantiationInTypeClassInstance context ty of
        Just (typeVar, instanceType) -> (ty, Core.typeApply coreType instanceType)
        Nothing -> (ty, coreType)
    Nothing -> internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name)

declarationTypeInPattern :: TypeInferenceOutput -> Quantors -> Name -> Int -> (Top.TpScheme, Core.Type)
declarationTypeInPattern typeOutput parent name beta =
  case declarationTpScheme typeOutput TCCNone name of
    Just scheme -> (scheme, toCoreType parent scheme)
    Nothing ->
      let
        ty = lookupBeta beta $ typeOutput
        scheme = Top.Quantification ([], [], (Top.Qualification ([], ty)))
      in (scheme, typeToCoreType parent ty)

findCoreType :: TypeInferenceOutput -> Quantors -> Int -> Core.Type
findCoreType typeOutput quantors beta 
  = typeToCoreType quantors $ convertTpToQualified (importEnv typeOutput) $ lookupBeta beta typeOutput

toCoreType :: Quantors -> Top.TpScheme -> Core.Type
toCoreType parent (Top.Quantification (tvars, qmap, t)) = foldr addTypeVar t' tvars
  where
    t' = qtypeToCoreType (appendQuantors parent $ quantorsFromList tvars) t
    addTypeVar index = Core.TForall (typeVarToQuantor qmap index) Core.KStar

toCoreTypeNotQuantified :: Top.TpScheme -> Core.Type
toCoreTypeNotQuantified (Top.Quantification (tvars, _, t)) = qtypeToCoreType (quantorsFromList tvars) t

typeVarToQuantor :: Top.QuantorMap -> Int -> Core.Quantor
typeVarToQuantor qmap index = Core.Quantor $ lookup index qmap

qtypeToCoreType :: Quantors -> Top.QType -> Core.Type
qtypeToCoreType quantors (Top.Qualification (q, t)) = foldr addDictArgument (typeToCoreType quantors t) q
  where
    addDictArgument predicate = Core.TAp $ Core.TAp (Core.TCon Core.TConFun) arg
      where
        arg = predicateToCoreType quantors predicate

predicateToCoreType :: Quantors -> Top.Predicate -> Core.Type
predicateToCoreType quantors (Top.Predicate className tp) =
    Core.TAp (Core.TCon $ TConTypeClassDictionary $ idFromString className) $ typeToCoreType quantors tp

customInfix :: DeclKind
customInfix = customDeclKind "infix"

setExportsPublic :: Bool -> (IdSet,IdSet,IdSet,IdSet,IdSet) -> ImportEnvironment -> Module v -> Module v
setExportsPublic implicit (exports,exportCons,exportData,exportDataCon,exportMods) env m
  = m{ moduleDecls = map setPublic (moduleDecls m) }
  where
    setPublic :: Decl v -> Decl v
    setPublic decl_ | isQual decl_ && (isInstance decl_ || declPublic decl_) =
                        let name = stringFromId $! declName decl_
                            newname = idFromString $! unQualifyString name
                        in if not ("Dict$" `isPrefixOf` name) then
                            decl_{ declAccess = Export newname }
                           else
                            decl_
                    | isQual decl_ =
                        decl_{declAccess = Private}
                    | isInstance decl_ || declPublic decl_ = decl_{ declAccess = Export $ declName decl_ }
                    | otherwise       = decl_{declAccess = Private}

    isExported decl_ elemIdSet =
        let access = declAccess decl_ in
        if implicit then
            case declModule decl_ of
              Just _  -> False -- imported
              Nothing -> True  -- defined in current module
        else
            case declModule decl_ of
                Just x
                    | elemSet x exportMods              -> True
                    | otherwise                         -> elemIdSet
                Nothing
                    | elemSet (moduleName m) exportMods -> True
                    | otherwise                         -> elemIdSet

    declPublic decl_ =
        let name = declName decl_
        in
        case decl_ of
            DeclValue{}     ->  isExported decl_ (elemSet name exports)
            DeclAbstract{}  ->  isExported decl_
                                    (  elemSet name exports
                                    || elem (stringFromId name) classMembers
                                    )
            DeclExtern{}    ->  isExported decl_ (elemSet name exports)
            DeclCon{}       ->  isExported decl_
                                    (  elemSet name exportCons
                                    || (elemSet (conTypeName decl_) exportDataCon)
                                    )
            DeclCustom{}    ->  isExported decl_
                                    (declKind decl_ `elem` [customData, customTypeDecl, customClassDefinition]
                                                && (elemSet name exportData || elemSet name exportDataCon)
                                    || (declKind decl_ `elem` [customInfix] && elemSet name exports)
                                    )
            DeclTypeSynonym{} -> isExported decl_ (elemSet name exports)

    isQual decl_ = let name = stringFromId $ declName decl_ in isQualifiedString name

    -- Get all class members that should be exported
    classMembers     = concat $ map (map (\(n,_,_,_) -> getNameName n) . snd) $ M.elems exportClasses
    exportClasses    = M.filterWithKey (const . (`elem` exportClassNames)) classMemberEnv
    exportClassNames = map (convertClassNameToQualified env . nameFromString . stringFromId) (listFromSet exportDataCon)
    classMemberEnv   = classMemberEnvironment env

    -- Always export dictionaries
    isInstance decl_ = let name = stringFromId $ declName decl_ in "$dict" `isPrefixOf` name
    isTypeSynonym decl_@DeclTypeSynonym{} = True
    isTypeSynonym _ = False

    conTypeName (DeclCon{declCustoms=(_:CustomLink x _:_)}) = x
    conTypeName _ = dummyId

typeToCoreType :: Quantors -> Top.Tp -> Core.Type
typeToCoreType quantors = typeToCoreTypeMapped quantors (const Nothing)

typeToCoreTypeMapped :: Quantors -> (Int -> Maybe Core.Type) -> Top.Tp -> Core.Type
typeToCoreTypeMapped (Quantors quantors) f (Top.TVar index) = case f index of
  Just t -> t
  Nothing -> case index `elemIndex` quantors of -- Convert index from Top to Debruijn index for Core
    Just idx -> Core.TVar idx
    -- Type variable may be instantiated arbitrarily, for instance in `const undefined 1`.
    -- TODO: The type variable may have a different kind than *.
    Nothing  -> Core.TCon $ Core.TConTuple 0
typeToCoreTypeMapped _ _ (Top.TCon name) = Core.TCon c
  where
    c = case name of
        "->" -> Core.TConFun
        "()" -> Core.TConTuple 0
        '(':str
          | dropWhile (==',') str == ")" -> Core.TConTuple (length str)
        _ -> Core.TConDataType $ idFromString name
typeToCoreTypeMapped quantors f (Top.TApp t1 t2) = Core.TAp (typeToCoreTypeMapped quantors f t1) (typeToCoreTypeMapped quantors f t2)

addLambdasForLambdaExpression :: TypeInferenceOutput -> Quantors -> Int -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForLambdaExpression typeOutput quantors beta args expr = addLambdasForType (importEnv typeOutput) quantors tp id args [] expr
  where
    tp = lookupBeta beta typeOutput

addLambdas :: TypeInferenceOutput -> TypeClassContext -> Quantors -> Int -> Name -> [Id] -> (Quantors, ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr)
addLambdas typeOutput context parent beta name args = case declarationTpScheme typeOutput context name of
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
      qmap' = mapMaybe (\(idx, name) -> (, name) <$> (lookup idx (zip tvars instantiation) >>= getTVar)) qmap
      quantors  = appendQuantors parent $ quantorsFromList tvars
      quantors' = appendQuantors parent $ quantorsFromList tvars'
      substitute = Core.typeSubstitutions 0 $ reverse $ map (typeToCoreType quantors') instantiation
    in
      ( quantors'
      , \expr -> foldr (\x e -> Core.Forall (typeVarToQuantor qmap' x) Core.KStar e) (addLambdasForQType (importEnv typeOutput) quantors t substitute args expr) tvars'
      )

addLambdasForQType :: ImportEnvironment -> Quantors -> Top.QType -> (Core.Type -> Core.Type) -> [Id] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForQType env quantors (Top.Qualification ([], t)) substitute args expr = addLambdasForType env quantors t substitute args [] expr
addLambdasForQType env quantors (Top.Qualification (p : ps, t)) substitute (arg:args) expr =
  Core.Lam False (Core.Variable arg $ substitute $ predicateToCoreType quantors p) $ addLambdasForQType env quantors (Top.Qualification (ps, t)) substitute args expr

addLambdasForType :: ImportEnvironment -> Quantors -> Top.Tp -> (Core.Type -> Core.Type) -> [Id] -> [Core.Type] -> ([Core.Type] -> Core.Type -> Core.Expr) -> Core.Expr
addLambdasForType _ quantors retType substitute [] accumArgTypes expr = expr (reverse accumArgTypes) $ substitute $ typeToCoreType quantors retType
addLambdasForType env quantors (Top.TApp (Top.TApp (Top.TCon "->") argType) retType) substitute (arg:args) accumArgTypes expr =
  Core.Lam False (Core.Variable arg tp)
    $ addLambdasForType env quantors retType substitute args (tp : accumArgTypes) expr
  where
    tp = substitute $ typeToCoreType quantors argType
addLambdasForType env quantors tp substitute args accumArgTypes expr =
    case tp' of
        -- Verify that the resulting type is a function type
        Top.TApp (Top.TApp (Top.TCon "->") _) _ -> addLambdasForType env quantors tp' substitute args accumArgTypes expr
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

{-
Given either a Constructor or an identifier present in the type environment generates
the corresponding type correct expression.
-}
createInstantiation :: TypeInferenceOutput -> TypeEnvironment -> Quantors -> Name -> Bool -> Int -> Core.Expr
createInstantiation typeOutput typeEnv quantors name isConstructor beta = case maybeScheme of
  Nothing -> expr
  Just scheme -> foldl (\e t -> Core.ApType e $ typeToCoreType quantors t) expr $ findInstantiation (importEnv typeOutput) scheme tp
  where
    expr
      | isConstructor = case M.lookup name $ valueConstructors $ importEnv typeOutput of
          Just (_, tpScheme, True) -> coreIdentity $ toCoreType emptyQuantors tpScheme
          _ -> Core.Con $ Core.ConId $ idFromName name
      | otherwise = Core.Var $ idFromName name
    tp = lookupBeta beta typeOutput
    maybeScheme
      | isConstructor = Just $ declarationConstructorTypeScheme (importEnv typeOutput) name
      | otherwise = M.lookup name typeEnv
{-
Tries to instantiate the type variables in the type scheme such that it results
in the given Tp.
-}
findInstantiation :: ImportEnvironment -> Top.TpScheme -> Top.Tp -> [Top.Tp]
findInstantiation importEnv t@(Top.Quantification (tvars, _, Top.Qualification (_, tLeft))) tRight
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

{-
Puts the fields in the correct order,
and applies them in that order to the constructor expression.

Fills the empty fields with `undefined`
-}
createRecordInstantiation :: TypeInferenceOutput
                            -> Quantors
                            -> Name       {- Constructor name -}
                            {- Field name, argument to pass to field -}
                            -> [(Name, Core.Expr)]
                            -> TpScheme   {- Typescheme corresponding to the constructor function -}
                            -> Tp         {- Type instantiation corresponding to the constructor function -}
                            -> Core.Expr
createRecordInstantiation typeOutput@TypeInferenceOutput{..} quantors name bindings tps outputTp
    = foldl app_
        (foldl (\e t -> Core.ApType e $ typeToCoreType emptyQuantors t) constrExpr tVars)
          sortedBinds
  where
    ImportEnvironment{..} = importEnv
    recordFields = M.assocs $ fromMaybe (err "constructor could not be found") (M.lookup name recordEnvironment)
    err = internalError "CoreUtils" "createRecordInstantiation"

    constrExpr = Core.Con $ Core.ConId $ idFromName name
    -- Find an instantiation of the type variables using the type inferred for the
    -- constructor and the defined typescheme of the constructor
    tVars = findInstantiation importEnv tps outputTp
    (args, retTp) = functionSpine outputTp

    sortedFields = sortOn (\(n, (i, _, _, _)) -> i) recordFields

    -- If the types of all of the arguments are known we can reuse those types
    --    This is useful in cases where we have a record construction with type 
    --    arguments, but don't fill all of the fields (as we then still have a 
    --    type to assign to the field being omitted)
    -- If we don't, as in the case of when we have a record update where we don't 
    --    know which constructor we are at, we use the types defined in the record 
    --    environment. This is not a problem as we don't have to fill in 'undefined's
    --    for omitted fields, We just reuse the values in the previous version of the record
    argsWithTypes | length args < length sortedFields = zip (map (thd4 . snd) sortedFields) sortedFields
                  | otherwise                         = zip args sortedFields
    sortedBinds
      = map (\(tp, (n, x)) -> fieldToExpr (snd4 x) tp (lookup n bindings)) argsWithTypes

    strictOrUndefined :: Bool -> Tp -> Core.Expr
    strictOrUndefined strict tp = if strict
      then err "undefined strict field construction"
      else coreUndefined importEnv quantors tp

    fieldToExpr :: Bool -> Tp -> Maybe Core.Expr -> Core.Expr
    fieldToExpr strict tp = fromMaybe (strictOrUndefined strict tp)

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
createRecordUpdate :: TypeInferenceOutput
                    -> Quantors
                    {- Old record -}
                    -> Core.Expr
                    {- Beta variable of the old expression -}
                    -> Int
                    {- Beta variable of the new expression -}
                    -> Int
                    {- Field name, argument to pass to field, beta var for the argument -}
                    -> [(Name, Core.Expr, Int)]
                    {- Range for the overal expression -}
                    -> Range
                    -> Core.Expr
createRecordUpdate typeOutput@TypeInferenceOutput{..} quantors old oldBeta beta bindings range
    = foldl app_ (func `app_` old) (map thd4 args)
  where
    ImportEnvironment{..} = importEnv
    error = coreUtilsError "createRecordUpdate"

    -- Needed for the scrutinee and pattern matching
    oldTp = lookupBeta oldBeta typeOutput
    scrutVar = Variable (idFromString "x$") (typeToCoreType quantors oldTp)

    -- Determine which constructors are possible with this field combination
    constructors = mapMaybe (\x -> fst3 x `M.lookup` fieldLookup) bindings
    relevantConstrs = foldr1 intersect constructors
    resultTps = generalizeResult $ snd3 $ fromJust $
      M.lookup (head relevantConstrs) valueConstructors

    -- Build up the inner function which will do the actual 'updating'
    func = createLambdas lambdaArgs body
    body = constructorsToCase importEnv
      quantors
      (variableName scrutVar)
      (typeToCoreType quantors (lookupBeta beta typeOutput))
      range
      (findInstantiation importEnv resultTps oldTp)
      (map (\n -> (n, oldFields, exec n)) relevantConstrs)

    -- Determine the types and strictness for each of the fields to be updated
    args = map (\(n, e, t) -> (n, idFromString (show n), e, t)) bindings
    lambdaArgs = map (\(n, i, e, t) -> (strict n, Variable i (findCoreType typeOutput quantors t))) args
    strict n = snd4 $ fromJust (M.lookup n allFields)

    allFields = M.unions $ mapMaybe (`M.lookup` recordEnvironment) relevantConstrs
    oldFields = map (\n -> (n, idFromString (show n))) $ M.keys $
      foldr (M.delete . fst3) allFields bindings

    fieldToExpr :: Name -> Expr
    fieldToExpr = Var . idFromString . show

    allBinds :: Name -> [(Name, Core.Expr)]
    allBinds n = fromMaybe (error "(n/a)") $ do
      fields <- M.lookup n recordEnvironment
      return $ map (\(x, _) -> (x, fieldToExpr x)) (M.assocs fields)

    exec n = createRecordInstantiation typeOutput quantors n (allBinds n) resultTps (lookupBeta beta typeOutput)

    createLambdas :: [(Bool, Variable)] -> Core.Expr -> Core.Expr
    createLambdas xs e = Lam True scrutVar (foldr (uncurry Lam) e xs)

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
                    -> Quantors
                    -> Range
                    -> Name
                    -> Tp
                    -> Core.Expr
createRecordSelector importEnv quantors r field retTp
  = foldr (\x e -> Core.Forall (typeVarToQuantor qmap x) Core.KStar e) (Lam True scrutVar select) tvars
  where
    ty@(Top.Quantification (_, qmap, _)) = fromMaybe (notFound constr) $ do
      fields <- M.lookup constr (recordEnvironment importEnv)
      (i, s, t, ts) <- M.lookup field fields
      return ts
    tvars = mapMaybe getTVar $ findInstantiation importEnv ty (unqualify (unquantify ty))

    select = constructorsToCase importEnv quantors scrutId (typeToCoreType quantors retTp) r instantiated atEachConstructor
    scrutId = idFromString "x$"
    fieldId = idFromString (show field)
    atEachConstructor = map (, [(field, fieldId)], Var fieldId) constrs

    constrs = fromMaybe (notFound field) $ field `M.lookup` fieldLookup importEnv
    constr = head constrs
    (n, constrTps, _)
      = fromMaybe (notFound constr) $ M.lookup constr (valueConstructors importEnv)
    instantiated = sort $ findInstantiation importEnv constrTps (unqualify (unquantify constrTps))

    scrutTp = unqualify (unquantify constrTps)
    scrutType = snd $ Core.typeExtractFunction $ toCoreTypeNotQuantified constrTps
    scrutVar = Variable scrutId scrutType
    notFound f = coreUtilsError "createRecordSelector"
      ("no appropriate constructor found for field " ++ show f)

generalizeResult :: TpScheme -> TpScheme
generalizeResult constrTps = generalizeAll ([] .=>. constrTp)
  where
    constrTp = snd $ functionSpine $ unqualify $ unquantify constrTps

-- Helper function for executing code for a multiple constructors
constructorsToCase :: ImportEnvironment
                    -> Quantors
                    -> Id           {- Scrutinee's Id -}
                    -> Core.Type    {- Result type -}
                    -> Range        {- Range of the overal expression -}
                    -> [Tp]         {- Scrutinee's type variables -}
                    {- (Constructor name, Fields to include, What to execute) -}
                    -> [(Name, [(Name, Id)], Core.Expr)]
                    -> Core.Expr
constructorsToCase importEnv quantors scrutId resType r tps fs
  = case fs of
    [] -> patternMatchFail "pattern binding" resType r
    ((n, fields, exec):xs) -> constructorToCase importEnv quantors n scrutId tps fields exec $
                          constructorsToCase importEnv quantors scrutId resType r tps xs

-- Helper function for executing code for a specific constructor
constructorToCase :: ImportEnvironment
                    -> Quantors
                    -> Name           {- Constructor name -}
                    -> Id             {- Scrutinee -}
                    -> [Tp]           {- Typevariables to instantiate the pattern to -}
                    -> [(Name, Id)]   {- Fields to include -}
                    -> Core.Expr      {- What to execute if it matches -}
                    -> Core.Expr      {- What to execute otherwise -}
                    -> Core.Expr
constructorToCase importEnv quantors constr scrutinee tps fs exec continue
  | isTransparentNewtype
  , [arg] <- args
  , [tp] <- argTypes
    -- Newtype becomes a type alias in Core
    = Let (Strict (Bind (Variable arg tp) $ Var scrutinee)) exec
  | otherwise
    = Match scrutinee
        [ Alt patt exec
        , Alt PatDefault continue
        ]
  where
    args = map (\(n, _) -> placeholder n fieldsToReuse) sortedFields
    argTypes = map (typeToCoreType quantors) tps
    patt = PatCon (ConId constructor) (map (typeToCoreType quantors) tps) args

    constructor = idFromString (show constr)
    (fields, (n, constrTps, isTransparentNewtype)) = fromMaybe (err "Constructor not found") $ do
      fields <- M.lookup constr (recordEnvironment importEnv)
      constrTps' <- M.lookup constr (valueConstructors importEnv)
      return (fields, constrTps')

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

coreUndefined :: ImportEnvironment -> Quantors -> Tp -> Core.Expr
coreUndefined importEnv quantors tp
      = undefinedExpr `Core.ApType` typeToCoreType quantors tp
    where
      undefinedExpr = Var (idFromString "undefined")

coreUtilsError :: String -> String -> a
coreUtilsError = internalError "CoreUtils"

-- Generates an identity function of the given function type
-- Used to compile a constructor of a transparent newtype
coreIdentity :: Core.Type -> Core.Expr
coreIdentity (Core.TForall quantor kind tp) = Core.Forall quantor kind $ coreIdentity tp
coreIdentity (Core.TAp (Core.TAp (Core.TCon Core.TConFun) argTp) _) =
  Core.Lam False (Core.Variable argName argTp) $ Core.Var argName
  where
    argName = idFromString "x"
coreIdentity _ = coreUtilsError "coreIdentity" "Expected forall or function type"
