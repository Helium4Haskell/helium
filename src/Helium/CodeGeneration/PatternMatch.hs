{-| Module      :  PatternMatch
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.PatternMatch(patternToCore, patternsToCore, nextClauseId, freshIds) where

import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Type as Core
import qualified Top.Types as Top
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range
import Lvm.Common.Id
import Data.Char
import Helium.Utils.Utils
import Helium.ModuleSystem.ImportEnvironment
import Helium.CodeGeneration.CoreUtils
import qualified Data.Map as M
import Data.Maybe

patternsToCore :: ImportEnvironment -> M.Map Name Core.Type -> [(Id, Core.Type, Pattern)] -> Core.Expr -> Core.Expr
patternsToCore env types nps continue = fst (patternsToCore' env types nps continue 0)

patternsToCore' :: ImportEnvironment -> M.Map Name Core.Type -> [(Id, Core.Type, Pattern)] -> Core.Expr -> Int -> (Core.Expr, Int)
patternsToCore' _ _ [] continue nr = (continue, nr)
patternsToCore' env types (np:nps) continue nr =
    let (expr, nr') = patternsToCore' env types nps continue nr
    in patternToCore' env types np expr nr'

patternToCore :: ImportEnvironment -> M.Map Name Core.Type -> (Id, Core.Type, Pattern) -> Core.Expr -> Core.Expr
patternToCore env types np continue = fst (patternToCore' env types np continue 0)


withNr :: a -> b -> (b, a)
withNr nr e = (e, nr)

findType :: Name -> M.Map Name Core.Type -> Core.Type
findType name types = fromMaybe (internalError "PatternMatch" "patternToCore'" $ "Could not find type for variable in pattern: " ++ show name) $ M.lookup name types

patternToCore' :: ImportEnvironment -> M.Map Name Core.Type -> (Id, Core.Type, Pattern) -> Core.Expr -> Int -> (Core.Expr, Int)
patternToCore' env types (name, tp, pat) continue nr = 
    case pat of
        -- let x = _u1 in ...
        Pattern_Variable _ n -> withNr nr $
            if name == wildcardId || name == idFromName n then
                continue
            else 
                let_ (idFromName n) (findType n types) (Core.Var name) continue
        
        -- case _u1 of C _l1 _l2 -> ...
        --             _         -> _next
        Pattern_Constructor _ n ps -> 
            let 
                (ids, nr') =
                    if all isSimple ps then 
                        (map getIdOfSimplePattern ps, nr)
                    else 
                        freshIds' "l$" nr (length ps)
                (expr, nr'') =
                    patternsToCore' env types (zip3 ids (constructorFieldTypes env n tp) ps) continue nr'
            in withNr nr'' $
                case_ name tp
                [ Core.Alt 
                    (Core.PatCon (Core.ConId (idFromName n)) ids) 
                    expr
                ]

        -- case _u1 of _l1 : _l2 -> ...
        --             _         -> _next
        Pattern_InfixConstructor _ p1 n p2 ->
            let ie = internalError "PatternMatch" "patternToCore'" "shouldn't look at range"
            in patternToCore' env types (name, tp, Pattern_Constructor ie n [p1, p2]) continue nr
                
        Pattern_Parenthesized _ p ->
            patternToCore' env types (name, tp, p) continue nr

        -- let n = _u1 in ...
        Pattern_As _ n p -> 
            let (expr, nr') = patternToCore' env types (name, tp, p) continue nr
            in withNr nr' $
                let_ 
                    (idFromName n) (findType n types) (Core.Var name) 
                    expr

        Pattern_Wildcard _ -> withNr nr continue
                
        -- case _u1 of 42 -> ...
        --             _  -> _next        

        Pattern_Literal _ l ->  
            case l of
                Literal_Int _ i -> withNr nr $
                    case_ name tp [ Core.Alt (Core.PatLit (Core.LitInt (read i))) continue ]
                Literal_Char _ c -> withNr nr $
                    case_ name tp
                    [ Core.Alt  
                        (Core.PatLit 
                            (Core.LitInt (ord (read ("'" ++ c ++ "'"))))
                        )
                        continue 
                    ]
                Literal_Float _ f -> withNr nr $
                    if_ (var "$primEqFloat" `app_` float f `app_` Core.Var name)
                        continue
                        (Core.Var nextClauseId)
-- !!! if we would have MATCHFLOAT instruction it could be: 
--  case_ name tp [ Core.Alt (Core.PatLit (Core.LitDouble (read f))) continue ]
                Literal_String _ s -> 
                    patternToCore'
                        env
                        types
                        ( name
                        , tp
                        , Pattern_List noRange 
                            (map (Pattern_Literal noRange . Literal_Int noRange . show . ord) characters) 
                        )
                        continue
                        nr
                  where
                    characters = read ("\"" ++ s ++ "\"") :: String
            
        Pattern_List _ ps -> 
            patternToCore' env types (name, tp, expandPatList ps) continue nr
        
        Pattern_Tuple _ ps ->
            let
                (ids, nr') =
                    if all isSimple ps then 
                        (map getIdOfSimplePattern ps, nr)
                    else 
                        freshIds' "l$" nr (length ps)
                (expr, nr'') = 
                    patternsToCore' env types (zip3 ids (Core.typeTupleElements tp) ps) continue nr'
            in withNr nr'' $
                case_ name tp
                [ Core.Alt 
                    (Core.PatCon (Core.ConTag 0 (length ps)) ids) 
                    expr
                ]
            
        
        Pattern_Negate _ (Literal_Int r v) -> 
            patternToCore'
                env
                types
                (name, tp, Pattern_Literal r (Literal_Int r neg))
                continue
                nr
            where
                neg = show (-(read v :: Int))

        Pattern_Negate _ (Literal_Float r v) -> 
            patternToCore'
                env
                types
                (name, tp, Pattern_Literal r (Literal_Float r neg))
                continue
                nr
            where
                neg = show (-(read v :: Float))
            
        Pattern_NegateFloat _ (Literal_Float r v) -> 
            patternToCore'
                env
                types
                (name, tp, Pattern_Literal r (Literal_Float r neg))
                continue
                nr
            where
                neg = show (-(read v :: Float))

        -- ~p  ====>
        --   let x = case _u1 of p -> x
        --       y = case _u1 of p -> y   (for each var in p)
        --   in continue
        Pattern_Irrefutable _ p -> 
            withNr nr $ foldr 
                (\v r -> let_ (idFromName v) (findType v types) (patternToCore env types (name, tp, p) (Core.Var $ idFromName v)) r)
                continue
                $ patternVars p
        
        _ -> internalError "PatternMatch" "patternToCore'" "unknown pattern kind"

-- [1, 2, 3] ==> 1 : (2 : (3 : [] ) )
expandPatList :: [Pattern] -> Pattern
expandPatList [] = 
    Pattern_Constructor noRange (Name_Special noRange [] "[]") [] -- !!!Name
expandPatList (p:ps) =
    Pattern_InfixConstructor 
        noRange 
        p
        (Name_Identifier noRange [] ":")  -- !!!Name
        (expandPatList ps)
    
isSimple :: Pattern -> Bool
isSimple p = 
    case p of
        Pattern_Variable _ _ -> True
        Pattern_Wildcard _ -> True
        _ -> False

getIdOfSimplePattern :: Pattern -> Id
getIdOfSimplePattern p =
    case p of
        Pattern_Variable _ n -> idFromName n
        Pattern_Wildcard _ -> wildcardId
        _ -> internalError "PatternMatch" "getIdOfSimplePattern" "not a simple pattern"
        
freshIds :: String -> Int -> [Id]
freshIds prefix number = fst (freshIds' prefix 0 number)

freshIds' :: String -> Int -> Int -> ([Id], Int)
freshIds' prefix start number = 
    ( take number [ idFromString (prefix ++ show i) | i <- [start..] ]
    , number + start
    )

nextClauseAlternative :: Core.Alt
nextClauseAlternative =
    Core.Alt Core.PatDefault (Core.Var nextClauseId)

wildcardId, nextClauseId :: Id
( wildcardId :  nextClauseId : [] ) = map idFromString ["_", "nextClause$"] 

case_ :: Id -> Core.Type -> [Core.Alt] -> Core.Expr
case_ ident tp alts = 
    Core.Let 
        (Core.Strict (Core.Bind (Core.Variable ident $ Core.typeToStrict tp) (Core.Var ident)))      -- let! id = id in
        (Core.Match ident (alts++[nextClauseAlternative]))    -- match id { alt; ...; alt; _ -> _nextClause }

constructorFieldTypes :: ImportEnvironment -> Name -> Core.Type -> [Core.Type]
constructorFieldTypes _ _ Core.TAny = repeat Core.TAny
constructorFieldTypes env conName tp = map (Core.typeSubstitutions $ zipWith (\(Core.TVar typeArg) t -> (typeArg, t)) (getDataTypeArgs retType []) typeArgs) args
  where
    typeArgs = getDataTypeArgs tp []
    consTpScheme = fromMaybe (internalError "ToCorePat" "Pattern" $ "Could not find constructor " ++ show conName) $ M.lookup conName $ valueConstructors env
    (args, retType) = Core.typeExtractFunction $ toCoreTypeNotQuantified consTpScheme

    getDataTypeArgs :: Core.Type -> [Core.Type] -> [Core.Type]
    getDataTypeArgs (Core.TCon (Core.TConDataType name)) accum = case M.lookup (nameFromId name) $ typeSynonyms env of
      Nothing -> accum
      Just (arity, fn)
        | arity > length accum -> internalError "ToCorePat" "Pattern" "Expected data type, got partially applied type synonym"
        | otherwise ->
          let
            args = take arity accum
            remaining = drop arity accum
            f idx
              | idx < 0 = Just $ args !! (-1 - idx)
              | otherwise = Nothing
            tp' = typeToCoreType' [] f $ fn $ map Top.TVar [-1, -2 .. -arity]
          in
            getDataTypeArgs tp' remaining
    getDataTypeArgs (Core.TAp t1 t2) accum = getDataTypeArgs t1 (t2 : accum)
    getDataTypeArgs tp _ = internalError "ToCorePat" "Pattern" $ "Unexpected type " ++ show tp ++ ", expected a data type"
