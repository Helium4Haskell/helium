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

module SolveGreedy ( solveGreedy ) where

import Array
import Types 
import SolveConstraints
import ST
import SolverOptions    ( getTypeSynonyms )
import ConstraintInfo   ( ConstraintInfo )
import Monad            ( when )
import Utils            ( internalError, doubleSizeOfSTArray )

--------------------------------------
-- SolveGreedy: biased constraint solving

solveGreedy :: ConstraintInfo info => RunnableSolver info
solveGreedy = runSolver buildSubstitution where

   buildSubstitution :: ConstraintInfo info => SolveState ArraySubstitution info WrappedSubstitution
   buildSubstitution = do arraysubstitution <- useSolver (\(A starray) -> freezeSTArray starray) 
                          return (wrapSubstitution arraysubstitution)

newtype ArraySubstitution info state = A (STArray state Int (Maybe Tp))

instance ConstraintInfo info => ConstraintSolver ArraySubstitution info where

    initialize = 
      do unique <- getUnique
         setSolver 
           ( do starray <- newSTArray (0,2*unique) Nothing 
                return (A starray) )  

    unifyTerms info t1 t2 =
        do  t1'     <- applySubst t1
            t2'     <- applySubst t2
            options <- getSolverOptions
            let synonyms = getTypeSynonyms options
            case mguWithTypeSynonyms synonyms t1' t2' of
                Right (used,sub) -> 
                    do useSolver
                        (\(A starray) -> do
                            let f i = writeSTArray starray i (lookupInt i sub)
                            mapM_ f (dom sub)
                            when used (do
                                   let utp = equalUnderTypeSynonyms synonyms (sub |-> t1') (sub |-> t2')
                                   writeExpandedType synonyms starray t1 utp 
                                   writeExpandedType synonyms starray t2 utp) )
                Left _ -> addError info      

    findSubstForVar i =
      do maybetp <- useSolver (\(A starray) -> readSTArray starray i)
         case maybetp of 
            Nothing                   -> return (TVar i)
            Just tp@(TVar j) | i == j -> return tp
            Just tp                   -> applySubst tp

    newVariables is = 
      do resize <- useSolver (\(A starray) -> return $ not (null is) && last is > snd (boundsSTArray starray)) 
         when resize $ 
            updateSolver 
               (\(A old) -> do new <- doubleSizeOfSTArray Nothing old 
                               return (A new))

-- The key idea is as follows:
-- try to minimize the number of expansions by type synonyms.
-- If a type is expanded, then this should be recorded in the substitution. 
-- Invariant of this function should be that "atp" (the first type) can be
-- made equal to "utp" (the second type) with a number of type synonym expansions
writeExpandedType :: OrderedTypeSynonyms -> STArray state Int (Maybe Tp) ->  Tp -> Tp -> ST state ()
writeExpandedType synonyms starray = writeTypeType where

   writeTypeType atp utp = case (leftSpine atp,leftSpine utp) of
        
      ((TVar i,[]),_)                    -> writeIntType i utp
      ((TCon s,as),(TCon t,bs)) | s == t -> mapM_ (uncurry writeTypeType) (zip as bs)                             
      ((TCon s,as),_) -> case expandTypeConstructorOneStep (snd synonyms) atp of
                            Just atp' -> do writeTypeType atp' utp
                            Nothing   -> internalError "SolveGreedy.hs" "writeTypeType" "inconsistent types(1)"      
      _                                  -> internalError "SolveGreedy.hs" "writeTypeType" "inconsistent types(2)"
      
   writeIntType i utp = 

      do mtp <- readSTArray starray i
         case mtp of 
         
            Nothing  -> case utp of
                            TVar j | i == j -> return ()
                            otherwise       -> writeSTArray starray i (Just utp)         
            Just atp ->
                case (leftSpine atp,leftSpine utp) of
                    ((TVar j,[]),_) -> writeIntType j utp
                    ((TCon s,as),(TCon t,bs)) | s == t -> mapM_ (uncurry writeTypeType) (zip as bs)
                    ((TCon s,as),_) -> case expandTypeConstructorOneStep (snd synonyms) atp of
                                          Just atp' -> do writeSTArray starray i (Just atp')
                                                          writeIntType i utp
                                          Nothing   -> internalError "SolveGreedy.hs" "writeIntType" "inconsistent types(1)"
                    _               -> internalError "SolveGreedy.hs" "writeIntType" "inconsistent types(2)"
