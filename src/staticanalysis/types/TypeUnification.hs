-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeUnification.hs : A unification algorithm for types, which can take a
--    list of (ordered) type synonyms into account.
--
-------------------------------------------------------------------------------

module TypeUnification where

import TypeSubstitution
import TypeRepresentation
import TypeBasics
import TypeSynonyms
import Utils               ( internalError )

----------------------------------------------------------------------
-- unification (and similar operations)
       
data UnificationError  = ConstantClash
                       | InfiniteType
  deriving (Show,Eq)       

mgu :: Tp -> Tp -> Either UnificationError SubstAssocList 
mgu t1 t2 = case mguWithTypeSynonyms [] t1 t2 of
               Left uError -> Left uError
               Right (b,s) -> Right s

-- Expand type synonyms as lazy as possible
-- example: 
--   if String => [Char]
--   then   v11 -> [v11]  `mgu`  String -> [[v14]]
--   should be:
--      [ v11 := [Char] , v14 := Char ]
--
-- Note: the boolean indicates whether exansions where performed       
mguWithTypeSynonyms :: OrderedTypeSynonyms -> Tp -> Tp -> Either UnificationError (Bool,SubstAssocList)
mguWithTypeSynonyms typesynonyms = rec emptySubst

    where
        rec :: SubstAssocList -> Tp -> Tp -> Either UnificationError (Bool,SubstAssocList)
        rec sub t1 t2 =
        
            case (leftSpine t1,leftSpine t2) of
 
               ((TVar i,[]),_          ) -> recVar sub i t2               
               (_          ,(TVar i,[])) -> recVar sub i t1
               ((TCon s,ss),(TCon t,tt)) 
                             | s == t    -> recList sub ss tt
                             | otherwise -> case expandTypeConstructorsOneStep typesynonyms [t1,t2] of 
                                               Just [t1',t2'] -> case rec sub t1' t2' of
                                                                    Left  uError   -> Left uError
                                                                    Right (_,sub') -> Right (True,sub') 
                                               Nothing        -> Left ConstantClash
                                                                          
               _ -> internalError "SATypes.hs" "mguWithTypeSynonyms" "illegal type"            

        recVar :: SubstAssocList -> Int -> Tp -> Either UnificationError (Bool,SubstAssocList)
        recVar sub i tp = case lookupInt i sub of
                             Just t2 -> case rec sub tp t2 of
                                           Right (True,sub') -> let newTP = equalUnderTypeSynonyms typesynonyms (sub' |-> tp) (sub' |-> t2)
                                                                in Right (True,singleSubstitution i newTP @@ removeDom [i] sub')
                                           answer            -> answer
                             Nothing -> case sub |-> tp of 
                                           TVar j | i == j           -> Right (False,sub)
                                           tp'    | i `elem` ftv tp' -> Left InfiniteType
                                                  | otherwise        -> Right (False,singleSubstitution i tp' @@ sub)                                     
            
        recList :: SubstAssocList -> Tps -> Tps -> Either UnificationError (Bool,SubstAssocList)
        recList sub [] [] = Right (False,sub)
        recList sub (s:ss) (t:tt) = 
           case rec sub s t of
              Left uError    -> Left uError
              Right (b,sub') -> case recList sub' ss tt of
                                   Left uError      -> Left uError
                                   Right (b',sub'') -> Right (b || b', sub'')
        recList _ _ _ = internalError "SATypes.hs" "mguWithTypeSynonyms" "illegal type"  

-- Find the most general type for two types that are equal under type synonyms
-- (i.e., the least number of expansions)
equalUnderTypeSynonyms :: OrderedTypeSynonyms -> Tp -> Tp -> Tp
equalUnderTypeSynonyms typesynonyms t1 t2 = 
   case (leftSpine t1,leftSpine t2) of 
      ((TVar i,[]),(TVar j,[])) -> TVar i
      ((TCon s,ss),(TCon t,tt)) 
                    | s == t    -> foldl TApp (TCon s) $ map (uncurry (equalUnderTypeSynonyms typesynonyms)) (zip ss tt)
                    | otherwise -> case expandTypeConstructorsOneStep typesynonyms [t1,t2] of
                                      Just [t1',t2'] -> equalUnderTypeSynonyms  typesynonyms t1' t2'
                                      Nothing        -> internalError "SATypes.hs" "equalUnderTypeSynonyms" "invalid types"

genericInstanceOf :: OrderedTypeSynonyms -> TpScheme -> TpScheme -> Bool
genericInstanceOf typesynonyms scheme1@(Scheme qs1 nm1 t1) scheme2@(Scheme qs2 nm2 t2) =
      let [Scheme qs1 _ tp1,scheme2'] = freezeMonosInTypeSchemes [scheme1,scheme2]
          sub    = listToSubstitution (zip (ftv [scheme1,scheme2]) [ TCon ('_':show i) | i <- [0..]])
          sub'   = listToSubstitution (zip qs1 [ TCon ('+':show i) | i <- [0..]])
          t1'    = sub' |-> tp1
          t2'    = unsafeInstantiate scheme2'
      in unifiable typesynonyms t1' t2'

freezeMonosInTypeSchemes :: [TpScheme] -> [TpScheme]
freezeMonosInTypeSchemes xs = let sub = listToSubstitution (zip (ftv xs) [ TCon ('_':show i) | i <- [1..]] )
                              in sub |-> xs
unifiable :: OrderedTypeSynonyms -> Tp -> Tp -> Bool
unifiable typesynonyms t1 t2 =
   case mguWithTypeSynonyms typesynonyms t1 t2 of
      Left  _ -> False
      Right _ -> True


unifiableTypeSchemes :: OrderedTypeSynonyms -> TpScheme -> TpScheme -> Bool
unifiableTypeSchemes typesynonyms s1 s2 =
   let i       = maximum (0 : ftv s1 ++ ftv s2) + 1
       (i',t1) = instantiate i  s1
       (_ ,t2) = instantiate i' s2
   in unifiable typesynonyms t1 t2
