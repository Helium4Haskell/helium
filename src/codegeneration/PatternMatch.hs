module PatternMatch(patternToCore, patternsToCore, nextClauseId, freshIds) where

import qualified Core
import UHA_Syntax
import UHA_Utils
import Id
import Char
import IOExts -- trace
import Utils
import CoreUtils

patternsToCore :: [(Id, Pattern)] -> Core.Expr -> Core.Expr
patternsToCore nps continue =
    foldr patternToCore continue nps
    
patternToCore :: (Id, Pattern) -> Core.Expr -> Core.Expr
patternToCore (name, pat) continue = 
    case pat of
        -- let x = _u1 in ...
        Pattern_Variable _ n -> 
            if name == wildcardId || name == idFromName n then
                continue
            else 
                let_ (idFromName n) (Core.Var name) continue
        
        -- case _u1 of C _l1 _l2 -> ...
        --             _         -> _next
        Pattern_Constructor _ n ps -> 
            let 
                ids =
                    if all isSimple ps then 
                        map getIdOfSimplePattern ps 
                    else 
                        freshIds "l$" (length ps)
            in
                case_ name
                [ Core.Alt 
                    (Core.PatCon (Core.ConId (idFromName n)) ids) 
                    (patternsToCore (zip ids ps) continue)
                ]

        -- case _u1 of _l1 : _l2 -> ...
        --             _         -> _next
        Pattern_InfixConstructor _ p1 n p2 ->
            let 
                ps = [p1, p2]
                ids =
                    if all isSimple ps then 
                        map getIdOfSimplePattern ps 
                    else freshIds "l$" (length ps)
            in
                case_ name
                [ Core.Alt 
                    (Core.PatCon (Core.ConId (idFromName n)) ids) 
                    (patternsToCore (zip ids [p1, p2]) continue)
                ]
                
        Pattern_Parenthesized _ p ->
            patternToCore (name, p) continue

        -- let n = _u1 in ...
        Pattern_As _ n p -> 
            let_ 
                (idFromName n) (Core.Var name) 
                (patternToCore (name, p) continue)

        Pattern_Wildcard _ ->
            continue
                
        -- case _u1 of 42 -> ...
        --             _  -> _next        

        Pattern_Literal _ l ->  
            case l of
                Literal_Int _ i -> 
                    case_ name [ Core.Alt (Core.PatLit (Core.LitInt (read i))) continue ]
                Literal_Char _ [c] -> 
                    case_ name 
                    [ Core.Alt 
                        (Core.PatLit (Core.LitInt (ord c)))
                        continue 
                    ]
                Literal_Float _ f -> 
                    if_ (var "primEqFloat" `app_` float f `app_` Core.Var name)
                        continue
                        (Core.Var nextClauseId)
-- !!! if we would have MATCHFLOAT instruction it could be: 
--  case_ name [ Core.Alt (Core.PatLit (Core.LitDouble (read f))) continue ]
                Literal_String _ s -> 
                    patternToCore 
                        ( name
                        , Pattern_List undefined 
                            (map (\c -> Pattern_Literal undefined (Literal_Char undefined [c])) s) 
                        )
                        continue
            
        Pattern_List _ ps -> 
            patternToCore (name, expandPatList ps) continue
        
        Pattern_Tuple _ ps ->
            let
                ids =
                    if all isSimple ps then 
                        map getIdOfSimplePattern ps 
                    else 
                        freshIds "l$" (length ps)
            in
                case_ name
                [ Core.Alt 
                    (Core.PatCon (Core.ConTag 0 (length ps)) ids) 
                    (patternsToCore (zip ids ps) continue)
                ]
            
        
        Pattern_Negate _ (Literal_Int r v) ->
            patternToCore 
                (name, Pattern_Literal r (Literal_Int r neg))
                continue
            where
                neg = show (-(read v :: Int))
            
        Pattern_NegateFloat _ (Literal_Float r v) -> 
            patternToCore 
                (name, Pattern_Literal r (Literal_Float r neg))
                continue
            where
                neg = show (-(read v :: Float))
        
        _ -> internalError "PatternMatch" "patternToCore" "unknown pattern kind"

-- [1, 2, 3] ==> 1 : (2 : (3 : [] ) )
expandPatList :: [Pattern] -> Pattern
expandPatList [] = 
    Pattern_Constructor undefined (Name_Special undefined [] "[]") []
expandPatList (p:ps) =
    Pattern_InfixConstructor 
        undefined 
        p
        (Name_Identifier undefined [] ":") 
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
freshIds prefix nr = 
    [ idFromString (prefix ++ show i)
    | i <- [1..nr]
    ]

nextClauseAlternative :: Core.Alt
nextClauseAlternative =
    Core.Alt Core.PatDefault (Core.Var nextClauseId)

( wildcardId :  nextClauseId : [] ) = map idFromString $
  "_"        : "nextClause$" : [] 

case_ :: Id -> [Core.Alt] -> Core.Expr
case_ id alts = 
    Core.Let 
        (Core.Strict (Core.Bind id (Core.Var id)))      -- let! id = id in
        (Core.Match id (alts++[nextClauseAlternative])) -- match id { alt; ...; alt; _ -> _nextClause }
    
