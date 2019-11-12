{-| Module      :  DerivingEq
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.DerivingEq
    ( dataDictionary
    )
where

import qualified Data.Map.Strict               as M
import qualified Helium.Syntax.UHA_Syntax      as UHA
import           Helium.Syntax.UHA_Utils
import           Helium.CodeGeneration.CoreUtils
import           Helium.ModuleSystem.ImportEnvironment
import           Lvm.Core.Expr
import qualified Lvm.Core.Type                 as Core
import           Lvm.Core.Utils
import           Lvm.Common.Id
import           Helium.CodeGeneration.DerivingUtils

typeDictEq :: Core.Type
typeDictEq = Core.TCon $ Core.TConTypeClassDictionary $ idFromString "Eq"

-- Eq Dictionary for a data type declaration
dataDictionary :: TypeSynonymEnvironment -> UHA.Declaration -> CoreDecl
dataDictionary tse (UHA.Declaration_Data _ _ (UHA.SimpleType_SimpleType _ name names) constructors _) = DeclValue
    { declName    = idFromString ("Eq$" ++ getNameName name)
    , declAccess  = public
    , declType    = foldr (\(typeArg, idx) -> Core.TForall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
                          (Core.typeFunction argTypes dictType)
                        $ zip names [1 ..]
    , valueValue  = eqDict dictType dataType tse names constructors
    , declCustoms = [custom "type" ("Dict$Eq " ++ getNameName name)]
                    ++ map (custom "typeVariable" . getNameName)                   names
                    ++ map (\n -> custom "superInstance" ("Eq-" ++ getNameName n)) names
    }
  where
    argTypes :: [Core.Type]
    argTypes = zipWith (\_ idx -> Core.TAp typeDictEq $ Core.TVar idx) names [1 ..]
    dictType = Core.TAp typeDictEq dataType
    dataType = Core.typeApplyList (Core.TCon $ Core.typeConFromString $ getNameName name)
        $ zipWith (\_ idx -> Core.TVar idx) names [1 ..]
dataDictionary _ _ = error "pattern match failure in CodeGeneration.Deriving.dataDictionary"

eqDict :: Core.Type -> Core.Type -> TypeSynonymEnvironment -> [UHA.Name] -> [UHA.Constructor] -> Expr
eqDict dictType dataType tse names constructors = foldr
    (\(typeArg, idx) -> Forall (Core.Quantor idx $ Just $ getNameName typeArg) Core.KStar)
    dictBody'
    (zip names [1 ..])
  where
    dictBody' = foldr
        (Lam False)
        dictBody
        (zipWith (\name idx -> Variable (idFromName name) $ Core.TAp typeDictEq $ Core.TVar idx) names [1 ..])
    dictfType = Core.typeFunction [dictType, dataType, dataType] Core.typeBool
    dictBody  = let_
        (idFromString "func$eq")
        dictfType
        (eqFunction dictType dataType tse typeArgs constructors)
        (Ap (Ap (ApType (Con $ ConId $ idFromString "Dict$Eq") dataType) (ApType (var "default$Eq$/=") dataType))
            (var "func$eq")
        )
    typeArgs = M.fromList (zipWith (\name idx -> (name, Core.TVar idx)) names [1 ..])

-- Example: data X a b = C a b Int | D Char b
eqFunction :: Core.Type -> Core.Type -> TypeSynonymEnvironment -> M.Map UHA.Name Core.Type -> [UHA.Constructor] -> Expr
eqFunction dictType dataType tse typeArgs constructors =
    let body = Let
            (Strict (Bind (Variable fstArg dataType) (Var fstArg))) -- evaluate both
            (Let
                (Strict (Bind (Variable sndArg dataType) (Var sndArg)))
                (Match fstArg -- case $fstArg of ...
                       (map (makeAlt dataType tse typeArgs) constructors)
                )
            )
    in  foldr (Lam False)
              body
              [Variable (idFromString "dict") dictType, Variable fstArg dataType, Variable sndArg dataType]
             -- \$fstArg $sndArg ->

fstArg, sndArg :: Id
[fstArg, sndArg] = map idFromString ["$fstArg", "$sndArg"]

makeAlt :: Core.Type -> TypeSynonymEnvironment -> M.Map UHA.Name Core.Type -> UHA.Constructor -> Alt
makeAlt altType tse typeArgs constructor =
        -- C $v0 $v1 $v2 -> ...
                                           Alt
    (PatCon (ConId ident) elems vs)
            --             case $sndArg of
            --                  C $w0 $w1 $w2 -> ...
            --                      ?? $v0 $w0 &&
            --                      ?? $v1 $w1 &&
            --                      ?? $v2 $w2
            --                  _ -> False
    (Match
        sndArg
        [ Alt
            (PatCon (ConId ident) elems ws)
            (if null types
                then Con (ConId (idFromString "True"))
                else foldr1
                    andCore
                    [ Ap (Ap (Ap (ApType (var "==") tp) expr) (Var v)) (Var w)
                    | (v, w, (tp, expr)) <- zip3 vs ws types
                    ]
            )
        , Alt PatDefault (Con (ConId (idFromString "False")))
        ]
    )
  where
    elems          = M.elems typeArgs
    (ident, types) = nameAndTypes "Eq$" tse typeArgs constructor
    vs             = [ idFromString ("$r" ++ show i) | i <- [0 .. length types - 1] ]
    ws             = [ idFromString ("$w" ++ show i) | i <- [0 .. length types - 1] ]
{-  constructorToPat :: Id -> [UHA.Type] -> Pat
    constructorToPat id ts =
        PatCon (ConId ident) [ idFromNumber i | i <- [1..length ts] ] -}
    andCore x y = Ap (Ap (Var (idFromString "&&")) x) y
