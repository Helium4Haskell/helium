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
    ,   float, packedString
    ,   toplevelType, declarationType
    ,   toCoreType, toCoreTypeNotQuantified, typeToCoreType
    ,   addLambdas
    ) where

import Top.Types as Top
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

let_ :: Id -> Expr -> Expr -> Expr
let_ x e b = Let (NonRec (Bind (Variable x TAny) e)) b

letrec_ :: [CoreDecl] -> Expr -> Expr
letrec_ bs e = 
    Let 
        (Rec 
            [ Bind (Variable ident TAny) expr
            | DeclValue { declName = ident, valueValue = expr } <- bs
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
            [ Alt (PatCon (ConId trueId) []) thenExpr
            , Alt PatDefault elseExpr
            ]
        )

-- Function "coreList" builds a linked list of the given expressions
-- Example: coreList [e1, e2] ==> 
--   Ap (Ap (Con ":") e1) 
--           (Ap (Ap (Con ":") e2)
--                    (Con "[]")
--           )
coreList :: [Expr] -> Expr
coreList = foldr cons nil

cons :: Expr -> Expr -> Expr
cons x xs = Con (ConId consId) `app_` x `app_` xs

nil :: Expr
nil = Con (ConId nilId)

nilId, consId, trueId, guardId :: Id 
( nilId : consId :  trueId :  guardId : []) =
   map idFromString ["[]", ":", "True", "guard$"]

-- Function "stringToCore" converts a string to a Core expression
stringToCore :: String -> Expr
stringToCore [] = nil
stringToCore [x] = cons (Lit (LitInt (ord x))) nil
stringToCore xs = var "$primPackedToString" `app_` packedString xs

var :: String -> Expr
var x = Var (idFromString x)

--Core.Lit (Core.LitDouble (read @value))   PUSHFLOAT nog niet geimplementeerd
float :: String -> Expr
float f = 
    Core.Ap 
        (Core.Var (idFromString "$primStringToFloat")) 
        ( Core.Lit (Core.LitBytes (bytesFromString f)) )

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

declarationType :: Name -> ImportEnvironment -> Bool -> Core.Type
declarationType name ie isTopLevel
    | isTopLevel = toCoreType haskellType
    | otherwise = Core.TAny
    where
        haskellType = fromMaybe (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name)) (M.lookup name (typeEnvironment ie))

toCoreType :: Top.TpScheme -> Core.Type
toCoreType (Top.Quantification (tvars, qmap, t)) = foldr addTypeVar t' tvars
  where
    t' = qtypeToCoreType qmap t
    addTypeVar index = Core.TForall (typeVarToId qmap index) Core.KStar

toCoreTypeNotQuantified :: Top.TpScheme -> Core.Type
toCoreTypeNotQuantified (Top.Quantification (_, qmap, t)) = qtypeToCoreType qmap t

typeVarToId :: Top.QuantorMap -> Int -> Id
typeVarToId qmap index = case lookup index qmap of
    Just name -> idFromString name
    _ -> idFromString ("v" ++ show index)

qtypeToCoreType :: Top.QuantorMap -> Top.QType -> Core.Type
qtypeToCoreType qmap (Top.Qualification (q, t)) = foldr addDictArgument (typeToCoreType qmap t) q
  where
    addDictArgument predicate = Core.TAp $ Core.TAp (Core.TCon Core.TConFun) arg
      where
        arg = predicateToCoreType qmap predicate

predicateToCoreType :: Top.QuantorMap -> Top.Predicate -> Core.Type
predicateToCoreType qmap (Top.Predicate className tp) =
    Core.TAp (Core.TCon $ TConTypeClassDictionary $ idFromString className) $ typeToCoreType qmap tp

typeToCoreType :: Top.QuantorMap -> Top.Tp -> Core.Type
typeToCoreType qmap (Top.TVar index) = Core.TVar $ typeVarToId qmap index
typeToCoreType _ (Top.TCon name) = Core.TCon c
  where
    c = case name of
        "->" -> Core.TConFun
        '(':str
          | dropWhile (==',') str == ")" -> Core.TConTuple (length str)
        _ -> Core.TConDataType $ idFromString name
typeToCoreType qmap (Top.TApp t1 t2) = Core.TAp (typeToCoreType qmap t1) (typeToCoreType qmap t2)

toplevelType :: Name -> ImportEnvironment -> Bool -> [Custom]
toplevelType name ie isTopLevel
    | isTopLevel = [custom "type" typeString]
    | otherwise  = []
    where
        typeString = maybe
            (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
            show
            (M.lookup name (typeEnvironment ie))

addLambdas :: Bool -> ImportEnvironment -> Name -> [Id] -> Core.Expr -> Core.Expr
addLambdas False _ _ args expr = foldr Core.Lam expr $ map (`Core.Variable` Core.TAny) args
-- TODO: Add type Lambdas
addLambdas _ env name args expr = addLambdasForQType env qmap t args expr
  where
    Top.Quantification (tvars, qmap, t) = fromMaybe
        (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
        (M.lookup name (typeEnvironment env))

addLambdasForQType :: ImportEnvironment -> QuantorMap -> Top.QType -> [Id] -> Core.Expr -> Core.Expr
addLambdasForQType env qmap (Top.Qualification ([], t)) args expr = addLambdasForType env qmap t args expr
addLambdasForQType env qmap (Top.Qualification (p : ps, t)) (arg:args) expr =
    Core.Lam (Core.Variable arg $ predicateToCoreType qmap p) $ addLambdasForQType env qmap (Top.Qualification (ps, t)) args expr

addLambdasForType :: ImportEnvironment -> QuantorMap -> Top.Tp -> [Id] -> Core.Expr -> Core.Expr
addLambdasForType _ _ _ [] expr = expr
addLambdasForType env qmap (Top.TApp (Top.TApp (Top.TCon "->") argType) retType) (arg:args) expr =
    Core.Lam (Core.Variable arg $ typeToCoreType qmap argType)
        $ addLambdasForType env qmap retType args expr
addLambdasForType env qmap tp args expr =
    case tp' of 
        -- Verify that the resulting type is a function type
        Top.TApp (Top.TApp (Top.TCon "->") _) _ -> addLambdasForType env qmap tp' args expr
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
