-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveGreedy.hs : An instance of the class ConstraintSolver. The type 
--    constraints are solved one after another. When an inconsistency is 
--    detected, the constraint at hand (that caused the problem) is marked
--    as "erroneous", and the algorithm will continue solving the 
--    remaining constraints.
--
-------------------------------------------------------------------------------

module SolveGreedy (Greedy, evalGreedy, solveGreedy, buildSubstitutionGreedy) where

import Types
import Constraints
import SolveState
import IsSolver
import Utils (internalError)
import FixpointSolveState
import ConstraintInfo
import FiniteMap
import Maybe
import List

type Greedy info = Fix info FixpointFMSubstitution Maybe
     
evalGreedy :: Greedy info result -> result
evalGreedy x = fst . fromJust . runFix x . extend $ (F emptyFM)

solveGreedy :: ( ConstraintInfo info
               , SolvableConstraint constraint (Greedy info)
               , Show constraint
               ) => OrderedTypeSynonyms -> Int -> [constraint]  
                 -> (Int, WrappedSubstitution, Predicates, [info], IO ())
solveGreedy synonyms unique constraints = 
   evalGreedy $
   do setTypeSynonyms synonyms
      solveConstraints unique (liftConstraints constraints)
      uniqueAtEnd <- getUnique
      errors      <- getErrors
      subst       <- buildSubstitutionGreedy
      predicates  <- getReducedPredicates
      debug       <- getDebug
      return (uniqueAtEnd, subst, predicates, errors, putStrLn debug)

instance ConstraintInfo info => IsSolver (Greedy info) info where
 
   unifyTerms info t1 t2 = 
     do t1'      <- applySubst t1
        t2'      <- applySubst t2
        synonyms <- getTypeSynonyms
        case mguWithTypeSynonyms synonyms t1' t2' of
        
           Left _           -> addError info
        
           Right (used,sub) -> 
             let utp = equalUnderTypeSynonyms synonyms (sub |-> t1') (sub |-> t2') 
                 f (F fm) = F (addListToFM fm [ (i, lookupInt i sub) | i <- dom sub ])                          
                 g        = writeExpandedType synonyms t2 utp 
                          . writeExpandedType synonyms t1 utp 
                 h        = if used then g . f else f
             in modify (liftFunction h)

   findSubstForVar i =
     do s <- get
        let sub = getWith id s
        return (lookupInt i sub)

------------------------------------------------
-- Array Substitution

newtype FixpointFMSubstitution = F (FiniteMap Int Tp)

instance Substitution FixpointFMSubstitution where
   lookupInt i original@(F fm) = 
      case lookupFM fm i of
         Just tp | tp == TVar i -> TVar i
                 | otherwise    -> original |-> tp
         Nothing                -> TVar i
   removeDom   is (F fm) = F (delListFromFM fm is)
   restrictDom is (F fm) = let js = keysFM fm \\ is
                           in F (delListFromFM fm js)
   dom (F fm) = keysFM fm
   cod (F fm) = eltsFM fm
   
instance Show FixpointFMSubstitution where
   show (F fm) = "Fixpoint FiniteMap Substitution: " ++ show (fmToList fm)
   
-- The key idea is as follows:
-- try to minimize the number of expansions by type synonyms.
-- If a type is expanded, then this should be recorded in the substitution. 
-- Invariant of this function should be that "atp" (the first type) can be
-- made equal to "utp" (the second type) with a number of type synonym expansions             
writeExpandedType :: OrderedTypeSynonyms -> Tp -> Tp -> FixpointFMSubstitution ->  FixpointFMSubstitution
writeExpandedType synonyms = writeTypeType where

   writeTypeType :: Tp -> Tp -> FixpointFMSubstitution -> FixpointFMSubstitution
   writeTypeType atp utp original@(F fm) = 
      case (leftSpine atp,leftSpine utp) of        
         ((TVar i,[]),_)                    -> writeIntType i utp original
         ((TCon s,as),(TCon t,bs)) | s == t -> foldr (uncurry writeTypeType) original (zip as bs)                   
         ((TCon s,as),_) -> 
            case expandTypeConstructorOneStep (snd synonyms) atp of
               Just atp' -> writeTypeType atp' utp original
               Nothing   -> internalError "SolveGreedy.hs" "writeTypeType" "inconsistent types(1)"      
         _               -> internalError "SolveGreedy.hs" "writeTypeType" "inconsistent types(2)"   
      
   writeIntType :: Int -> Tp -> FixpointFMSubstitution -> FixpointFMSubstitution     
   writeIntType i utp original@(F fm) = 
      case lookupFM fm i of 
         
         Nothing  -> 
            case utp of
               TVar j | i == j -> original
               otherwise       -> F (addToFM fm i utp)
               
         Just atp ->
            case (leftSpine atp,leftSpine utp) of
               ((TVar j,[]),_) -> writeIntType j utp original
               ((TCon s,as),(TCon t,bs)) | s == t -> foldr (uncurry writeTypeType) original (zip as bs)
               ((TCon s,as),_) -> case expandTypeConstructorOneStep (snd synonyms) atp of
                                     Just atp' -> writeIntType i utp (F (addToFM fm i atp'))
                                     Nothing   -> internalError "SolveGreedy.hs" "writeIntType" "inconsistent types(1)"
               _               -> internalError "SolveGreedy.hs" "writeIntType" "inconsistent types(2)"      


buildSubstitutionGreedy :: ConstraintInfo info => Greedy info WrappedSubstitution
buildSubstitutionGreedy = do s <- get                       
                             let sub = getWith id s
                             return (wrapSubstitution sub)
                             
{-
lookupAndFix :: Int -> FixpointFMSubstitution -> (Tp, FixpointFMSubstitution)
lookupAndFix i original@(F fm) = 
   case lookupFM fm i of
      Nothing -> (TVar i, original)
      Just tp | tp == TVar i -> (tp, F (delFromFM fm i))
              | otherwise    -> let (tp', F fm') = lookupAndFixTp tp original
                                in (tp', F (addToFM fm' i tp'))


lookupAndFixTp :: Tp -> FixpointFMSubstitution -> (Tp, FixpointFMSubstitution)
lookupAndFixTp tp original@(F fm) = 
   case tp of
      TVar i   -> lookupAndFix i original
      TCon s   -> (tp, original)
      TApp l r -> let (tp1, fm1) = lookupAndFixTp l original
                      (tp2, fm2) = lookupAndFixTp r fm1
                  in (TApp tp1 tp2, fm2) -}                             
