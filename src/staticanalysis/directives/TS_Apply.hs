
-- UUAGC 0.9.5 (TS_Apply.ag)
module TS_Apply where

import UHA_Syntax
import TypeConstraints
import ConstraintInfo
import Top.Types
import List
import Utils (internalError)
import Messages
import TypeErrors
import ImportEnvironment
import BindingGroupAnalysis (Assumptions, combine, noAssumptions)
import OperatorTable (OperatorTable)
import Parser (exp_)
import Lexer (strategiesLexer)
import ParseLibrary (runHParser)
import qualified ResolveOperators
import qualified Data.Map as M
import TS_Attributes
import TS_CoreSyntax
import Top.Ordering.Tree


import Top.Types

applyTypingStrategy :: Core_TypingStrategy -> MetaVariableInfo -> MetaVariableTable -> Int 
                          -> (Assumptions, ConstraintSet, IO (), Int)
applyTypingStrategy = sem_Core_TypingStrategy

matchInformation :: ImportEnvironment -> Core_TypingStrategy -> [(Expression, [String])]
matchInformation importEnvironment typingStrategy = 
   case typingStrategy of 
      TypingStrategy _ (TypeRule premises conclusion) _ -> 
         let Judgement exprstring _ = conclusion
             expression = expressionParser (operatorTable importEnvironment) exprstring
             metas      = [ s | Judgement s t <- premises ]
         in [(expression, metas)]
      _ -> []
      
expressionParser :: OperatorTable -> String -> Expression
expressionParser operatorTable string = 
    case strategiesLexer "TS_Apply" string of
        Left lexErr -> intErr
        Right (tokens, _) ->
            case runHParser exp_ "TS_Apply" tokens True {- wait for EOF -} of
                Left parseError  -> intErr
                Right expression -> 
                    ResolveOperators.expression operatorTable expression
  where
    intErr = internalError "TS_Apply.ag" "n/a" ("unparsable expression: "++show string)

       
exactlyOnce :: Eq a => [a] -> [a]
exactlyOnce []     = []
exactlyOnce (x:xs) | x `elem` xs = exactlyOnce . filter (/= x) $ xs
                   | otherwise   = x : exactlyOnce xs


type Core_TypingStrategies = [Core_TypingStrategy]
-- Core_Judgement ----------------------------------------------
-- cata
sem_Core_Judgement :: Core_Judgement ->
                      T_Core_Judgement
sem_Core_Judgement (Judgement _expression _type )  =
    (sem_Core_Judgement_Judgement _expression _type )
-- semantic domain
type T_Core_Judgement = MetaVariableInfo ->
                        MetaVariableTable ->
                        MapSubstitution ->
                        ( ([Int]),([(String, Tp)]))
sem_Core_Judgement_Judgement :: String ->
                                Tp ->
                                T_Core_Judgement
sem_Core_Judgement_Judgement expression_ type_  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOjudgements :: ([(String, Tp)])
              _lhsOftv =
                  ftv type_
              _lhsOjudgements =
                  [(expression_, type_)]
          in  ( _lhsOftv,_lhsOjudgements)))
-- Core_Judgements ---------------------------------------------
-- cata
sem_Core_Judgements :: Core_Judgements ->
                       T_Core_Judgements
sem_Core_Judgements list  =
    (Prelude.foldr sem_Core_Judgements_Cons sem_Core_Judgements_Nil (Prelude.map sem_Core_Judgement list) )
-- semantic domain
type T_Core_Judgements = MetaVariableInfo ->
                         MetaVariableTable ->
                         MapSubstitution ->
                         ( ([Int]),([(String, Tp)]))
sem_Core_Judgements_Cons :: T_Core_Judgement ->
                            T_Core_Judgements ->
                            T_Core_Judgements
sem_Core_Judgements_Cons hd_ tl_  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOjudgements :: ([(String, Tp)])
              _hdOinfoTuple :: MetaVariableInfo
              _hdOmetaVariableTable :: MetaVariableTable
              _hdOsubstitution :: MapSubstitution
              _tlOinfoTuple :: MetaVariableInfo
              _tlOmetaVariableTable :: MetaVariableTable
              _tlOsubstitution :: MapSubstitution
              _hdIftv :: ([Int])
              _hdIjudgements :: ([(String, Tp)])
              _tlIftv :: ([Int])
              _tlIjudgements :: ([(String, Tp)])
              _lhsOftv =
                  _hdIftv `union` _tlIftv
              _lhsOjudgements =
                  _hdIjudgements ++ _tlIjudgements
              _hdOinfoTuple =
                  _lhsIinfoTuple
              _hdOmetaVariableTable =
                  _lhsImetaVariableTable
              _hdOsubstitution =
                  _lhsIsubstitution
              _tlOinfoTuple =
                  _lhsIinfoTuple
              _tlOmetaVariableTable =
                  _lhsImetaVariableTable
              _tlOsubstitution =
                  _lhsIsubstitution
              ( _hdIftv,_hdIjudgements) =
                  (hd_ _hdOinfoTuple _hdOmetaVariableTable _hdOsubstitution )
              ( _tlIftv,_tlIjudgements) =
                  (tl_ _tlOinfoTuple _tlOmetaVariableTable _tlOsubstitution )
          in  ( _lhsOftv,_lhsOjudgements)))
sem_Core_Judgements_Nil :: T_Core_Judgements
sem_Core_Judgements_Nil  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOjudgements :: ([(String, Tp)])
              _lhsOftv =
                  []
              _lhsOjudgements =
                  []
          in  ( _lhsOftv,_lhsOjudgements)))
-- Core_TypeRule -----------------------------------------------
-- cata
sem_Core_TypeRule :: Core_TypeRule ->
                     T_Core_TypeRule
sem_Core_TypeRule (TypeRule _premises _conclusion )  =
    (sem_Core_TypeRule_TypeRule (sem_Core_Judgements _premises ) (sem_Core_Judgement _conclusion ) )
-- semantic domain
type T_Core_TypeRule = MetaVariableInfo ->
                       MetaVariableTable ->
                       MapSubstitution ->
                       ( (TypeConstraints ConstraintInfo),([Int]),([(String, Tp)]))
sem_Core_TypeRule_TypeRule :: T_Core_Judgements ->
                              T_Core_Judgement ->
                              T_Core_TypeRule
sem_Core_TypeRule_TypeRule premises_ conclusion_  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIsubstitution ->
         (let _lhsOconstraints :: (TypeConstraints ConstraintInfo)
              _lhsOftv :: ([Int])
              _lhsOjudgements :: ([(String, Tp)])
              _premisesOinfoTuple :: MetaVariableInfo
              _premisesOmetaVariableTable :: MetaVariableTable
              _premisesOsubstitution :: MapSubstitution
              _conclusionOinfoTuple :: MetaVariableInfo
              _conclusionOmetaVariableTable :: MetaVariableTable
              _conclusionOsubstitution :: MapSubstitution
              _premisesIftv :: ([Int])
              _premisesIjudgements :: ([(String, Tp)])
              _conclusionIftv :: ([Int])
              _conclusionIjudgements :: ([(String, Tp)])
              _lhsOconstraints =
                  let conclusionSource = self       (getLocalInfo _lhsIinfoTuple)
                      conclusionType   = getType _lhsIinfoTuple
                  in [ (stp1 .==. conclusionType)
                          (addProperty FolkloreConstraint $ defaultConstraintInfo (conclusionSource, Nothing))
                     | (_, tp1) <- _conclusionIjudgements
                     , let stp1 = _lhsIsubstitution |-> tp1
                     , stp1 /= conclusionType
                     ] ++
                     [ (getType mvinfo .==. stp1)
                          (defaultConstraintInfo (conclusionSource, Just (self (getLocalInfo mvinfo))))
                     | (s1, tp1)    <- _premisesIjudgements
                     , (s2, mvinfo) <- _lhsImetaVariableTable
                     , s1 == s2
                     , let stp1 = _lhsIsubstitution |-> tp1
                     , getType mvinfo /= stp1
                     ]
              _lhsOftv =
                  _premisesIftv `union` _conclusionIftv
              _lhsOjudgements =
                  _premisesIjudgements ++ _conclusionIjudgements
              _premisesOinfoTuple =
                  _lhsIinfoTuple
              _premisesOmetaVariableTable =
                  _lhsImetaVariableTable
              _premisesOsubstitution =
                  _lhsIsubstitution
              _conclusionOinfoTuple =
                  _lhsIinfoTuple
              _conclusionOmetaVariableTable =
                  _lhsImetaVariableTable
              _conclusionOsubstitution =
                  _lhsIsubstitution
              ( _premisesIftv,_premisesIjudgements) =
                  (premises_ _premisesOinfoTuple _premisesOmetaVariableTable _premisesOsubstitution )
              ( _conclusionIftv,_conclusionIjudgements) =
                  (conclusion_ _conclusionOinfoTuple _conclusionOmetaVariableTable _conclusionOsubstitution )
          in  ( _lhsOconstraints,_lhsOftv,_lhsOjudgements)))
-- Core_TypingStrategy -----------------------------------------
-- cata
sem_Core_TypingStrategy :: Core_TypingStrategy ->
                           T_Core_TypingStrategy
sem_Core_TypingStrategy (Siblings _functions )  =
    (sem_Core_TypingStrategy_Siblings _functions )
sem_Core_TypingStrategy (TypingStrategy _typeEnv _typerule _statements )  =
    (sem_Core_TypingStrategy_TypingStrategy _typeEnv (sem_Core_TypeRule _typerule ) (sem_Core_UserStatements _statements ) )
-- semantic domain
type T_Core_TypingStrategy = MetaVariableInfo ->
                             MetaVariableTable ->
                             Int ->
                             ( Assumptions,ConstraintSet,(IO ()),Int)
sem_Core_TypingStrategy_Siblings :: ([String]) ->
                                    T_Core_TypingStrategy
sem_Core_TypingStrategy_Siblings functions_  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIunique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintSet :: ConstraintSet
              _lhsOdebugIO :: (IO ())
              _lhsOunique :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOconstraintSet =
                  emptyTree
              _lhsOdebugIO =
                  return ()
              _lhsOunique =
                  _lhsIunique
          in  ( _lhsOassumptions,_lhsOconstraintSet,_lhsOdebugIO,_lhsOunique)))
sem_Core_TypingStrategy_TypingStrategy :: ([(String, Tp)]) ->
                                          T_Core_TypeRule ->
                                          T_Core_UserStatements ->
                                          T_Core_TypingStrategy
sem_Core_TypingStrategy_TypingStrategy typeEnv_ typerule_ statements_  =
    (\ _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsIunique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintSet :: ConstraintSet
              _lhsOunique :: Int
              _lhsOdebugIO :: (IO ())
              _statementsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _statementsOcurrentPhase :: (Maybe Int)
              _statementsOcurrentPosition :: ((Int, Int))
              _statementsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _statementsOfromAttribute :: (Attribute -> MessageBlock)
              _typeruleOinfoTuple :: MetaVariableInfo
              _typeruleOmetaVariableTable :: MetaVariableTable
              _typeruleOsubstitution :: MapSubstitution
              _statementsOinfoTuple :: MetaVariableInfo
              _statementsOmetaVariableTable :: MetaVariableTable
              _statementsOsubstitution :: MapSubstitution
              _typeruleIconstraints :: (TypeConstraints ConstraintInfo)
              _typeruleIftv :: ([Int])
              _typeruleIjudgements :: ([(String, Tp)])
              _statementsIcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _statementsIcurrentPhase :: (Maybe Int)
              _statementsIcurrentPosition :: ((Int, Int))
              _statementsIftv :: ([Int])
              _statementsImetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOassumptions =
                  foldr combine noAssumptions (map (getAssumptions . snd) _lhsImetaVariableTable)
              _lhsOconstraintSet =
                  Node _allConstraintTrees
              _lhsOunique =
                  length _normalTV + _lhsIunique
              _lhsOdebugIO =
                  putStrLn "applying typing strategy"
              _substitution =
                  listToSubstitution (_standardSubst ++ _specialSubst)
              _allTV =
                  _typeruleIftv `union` _statementsIftv `union` ftv (map snd typeEnv_)
              _specialTV =
                  concat . exactlyOnce . map ftv . filter isTVar . map snd $ _typeruleIjudgements
              _normalTV =
                  _allTV \\ _specialTV
              _standardSubst =
                  zip _normalTV (map TVar [_lhsIunique..])
              _specialSubst =
                  let conclusionVar = case snd (last _typeruleIjudgements) of
                                         TVar i -> Just i
                                         _      -> Nothing
                      find i | Just i == conclusionVar = [ (i, getType _lhsIinfoTuple) ]
                             | otherwise               = [ (i, getType infoTuple)
                                                         | (s1, TVar j) <- _typeruleIjudgements
                                                         , i == j
                                                         , (s2,infoTuple) <- _lhsImetaVariableTable
                                                         , s1 == s2
                                                         ]
                  in concatMap find _specialTV
              _allConstraintTrees =
                  listTree (reverse _typeruleIconstraints) :
                  Phase 999 _patchConstraints :
                  (map snd _statementsImetavarConstraints) ++
                  (reverse _statementsIcollectConstraints)
              _patchConstraints =
                  let parent     = concat (M.elems (getAssumptions _lhsIinfoTuple))
                      children   = concat (concatMap (M.elems . getAssumptions . snd) _lhsImetaVariableTable)
                      (ns, tps1) = unzip (parent \\ children)
                      (ss, tps2) = unzip typeEnv_
                      zipF t1 t2 = (t1 .==. _substitution |-> t2) infoF
                      infoF      = emptyConstraintInfo
                                          { location   = "Typing Strategy (patch)" }
                      err = internalError "TS_Apply.ag" "n/a" "the type environments do not match"
                  in if (map show ns /= ss) then err else
                       zipWith zipF tps1 tps2
              _statementsOcollectConstraints =
                  []
              _statementsOcurrentPhase =
                  Nothing
              _statementsOcurrentPosition =
                  (_lhsIunique, 0)
              _statementsOmetavarConstraints =
                  [ (s, getConstraintSet info) | (s, info) <- _lhsImetaVariableTable ]
              _statementsOfromAttribute =
                  let locals = map f (dom _substitution)
                      f i    = (show i, MessageType (toTpScheme (lookupInt i _substitution)))
                  in toMessageBlock locals _lhsIinfoTuple _lhsImetaVariableTable
              _typeruleOinfoTuple =
                  _lhsIinfoTuple
              _typeruleOmetaVariableTable =
                  _lhsImetaVariableTable
              _typeruleOsubstitution =
                  _substitution
              _statementsOinfoTuple =
                  _lhsIinfoTuple
              _statementsOmetaVariableTable =
                  _lhsImetaVariableTable
              _statementsOsubstitution =
                  _substitution
              ( _typeruleIconstraints,_typeruleIftv,_typeruleIjudgements) =
                  (typerule_ _typeruleOinfoTuple _typeruleOmetaVariableTable _typeruleOsubstitution )
              ( _statementsIcollectConstraints,_statementsIcurrentPhase,_statementsIcurrentPosition,_statementsIftv,_statementsImetavarConstraints) =
                  (statements_ _statementsOcollectConstraints _statementsOcurrentPhase _statementsOcurrentPosition _statementsOfromAttribute _statementsOinfoTuple _statementsOmetaVariableTable _statementsOmetavarConstraints _statementsOsubstitution )
          in  ( _lhsOassumptions,_lhsOconstraintSet,_lhsOdebugIO,_lhsOunique)))
-- Core_UserStatement ------------------------------------------
-- cata
sem_Core_UserStatement :: Core_UserStatement ->
                          T_Core_UserStatement
sem_Core_UserStatement (CorePhase _phase )  =
    (sem_Core_UserStatement_CorePhase _phase )
sem_Core_UserStatement (Equal _leftType _rightType _message )  =
    (sem_Core_UserStatement_Equal _leftType _rightType _message )
sem_Core_UserStatement (MetaVariableConstraints _name )  =
    (sem_Core_UserStatement_MetaVariableConstraints _name )
sem_Core_UserStatement (Pred _predClass _predType _message )  =
    (sem_Core_UserStatement_Pred _predClass _predType _message )
-- semantic domain
type T_Core_UserStatement = (Trees (TypeConstraint ConstraintInfo)) ->
                            (Maybe Int) ->
                            ((Int, Int)) ->
                            (Attribute -> MessageBlock) ->
                            MetaVariableInfo ->
                            MetaVariableTable ->
                            ([(String,Tree (TypeConstraint ConstraintInfo))]) ->
                            MapSubstitution ->
                            ( (Trees (TypeConstraint ConstraintInfo)),(Maybe Int),((Int, Int)),([Int]),([(String,Tree (TypeConstraint ConstraintInfo))]))
sem_Core_UserStatement_CorePhase :: Int ->
                                    T_Core_UserStatement
sem_Core_UserStatement_CorePhase phase_  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOcurrentPhase :: (Maybe Int)
              _lhsOftv :: ([Int])
              _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOcurrentPhase =
                  Just phase_
              _lhsOftv =
                  []
              _lhsOcollectConstraints =
                  _lhsIcollectConstraints
              _lhsOcurrentPosition =
                  _lhsIcurrentPosition
              _lhsOmetavarConstraints =
                  _lhsImetavarConstraints
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))
sem_Core_UserStatement_Equal :: Tp ->
                                Tp ->
                                String ->
                                T_Core_UserStatement
sem_Core_UserStatement_Equal leftType_ rightType_ message_  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOcurrentPhase :: (Maybe Int)
              _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOftv =
                  ftv [leftType_, rightType_]
              _lhsOcurrentPosition =
                  (\(x, y) -> (x, y+1)) _lhsIcurrentPosition
              _lhsOcollectConstraints =
                  case _lhsIcurrentPhase of
                     Just phase | phase /= 5
                                -> Phase phase [ _newConstraint ] : _lhsIcollectConstraints
                     _          -> unitTree _newConstraint : _lhsIcollectConstraints
              _newConstraint =
                  let cinfo   = setTypeError (TypeError [] message [] [])
                              $ addProperty (uncurry IsUserConstraint _lhsIcurrentPosition)
                              $ inPhase emptyConstraintInfo
                      inPhase = case _lhsIcurrentPhase of
                                   Just phase | phase /= 5
                                      -> addProperty (ConstraintPhaseNumber phase)
                                   _  -> id
                      message = let f = MessageOneLiner . substituteAttributes _lhsIfromAttribute
                                in map f (lines message_)
                  in (_lhsIsubstitution |-> leftType_ .==. _lhsIsubstitution |-> rightType_) cinfo
              _lhsOcurrentPhase =
                  _lhsIcurrentPhase
              _lhsOmetavarConstraints =
                  _lhsImetavarConstraints
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))
sem_Core_UserStatement_MetaVariableConstraints :: String ->
                                                  T_Core_UserStatement
sem_Core_UserStatement_MetaVariableConstraints name_  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOftv :: ([Int])
              _lhsOcurrentPhase :: (Maybe Int)
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOmetavarConstraints =
                  filter ((name_ /=) . fst) _lhsImetavarConstraints
              _lhsOcollectConstraints =
                  case lookup name_ _lhsImetavarConstraints of
                      Just tree -> tree : _lhsIcollectConstraints
                      Nothing   -> internalError "TS_Apply.ag" "n/a" "unknown constraint set"
              _lhsOftv =
                  []
              _lhsOcurrentPhase =
                  _lhsIcurrentPhase
              _lhsOcurrentPosition =
                  _lhsIcurrentPosition
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))
sem_Core_UserStatement_Pred :: String ->
                               Tp ->
                               String ->
                               T_Core_UserStatement
sem_Core_UserStatement_Pred predClass_ predType_ message_  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOftv :: ([Int])
              _lhsOcurrentPhase :: (Maybe Int)
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOcollectConstraints =
                  unitTree _newConstraint : _lhsIcollectConstraints
              _newConstraint =
                  let cinfo = setTypeError (TypeError [] message [] [])
                            $ addProperty (ReductionErrorInfo thePred)
                            $ emptyConstraintInfo
                      thePred = Predicate predClass_ (_lhsIsubstitution |-> predType_)
                      message = let f = MessageOneLiner . substituteAttributes _lhsIfromAttribute
                                in map f (lines message_)
                  in predicate thePred cinfo
              _lhsOftv =
                  []
              _lhsOcurrentPhase =
                  _lhsIcurrentPhase
              _lhsOcurrentPosition =
                  _lhsIcurrentPosition
              _lhsOmetavarConstraints =
                  _lhsImetavarConstraints
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))
-- Core_UserStatements -----------------------------------------
-- cata
sem_Core_UserStatements :: Core_UserStatements ->
                           T_Core_UserStatements
sem_Core_UserStatements list  =
    (Prelude.foldr sem_Core_UserStatements_Cons sem_Core_UserStatements_Nil (Prelude.map sem_Core_UserStatement list) )
-- semantic domain
type T_Core_UserStatements = (Trees (TypeConstraint ConstraintInfo)) ->
                             (Maybe Int) ->
                             ((Int, Int)) ->
                             (Attribute -> MessageBlock) ->
                             MetaVariableInfo ->
                             MetaVariableTable ->
                             ([(String,Tree (TypeConstraint ConstraintInfo))]) ->
                             MapSubstitution ->
                             ( (Trees (TypeConstraint ConstraintInfo)),(Maybe Int),((Int, Int)),([Int]),([(String,Tree (TypeConstraint ConstraintInfo))]))
sem_Core_UserStatements_Cons :: T_Core_UserStatement ->
                                T_Core_UserStatements ->
                                T_Core_UserStatements
sem_Core_UserStatements_Cons hd_ tl_  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOcurrentPhase :: (Maybe Int)
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _hdOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _hdOcurrentPhase :: (Maybe Int)
              _hdOcurrentPosition :: ((Int, Int))
              _hdOfromAttribute :: (Attribute -> MessageBlock)
              _hdOinfoTuple :: MetaVariableInfo
              _hdOmetaVariableTable :: MetaVariableTable
              _hdOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _hdOsubstitution :: MapSubstitution
              _tlOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _tlOcurrentPhase :: (Maybe Int)
              _tlOcurrentPosition :: ((Int, Int))
              _tlOfromAttribute :: (Attribute -> MessageBlock)
              _tlOinfoTuple :: MetaVariableInfo
              _tlOmetaVariableTable :: MetaVariableTable
              _tlOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _tlOsubstitution :: MapSubstitution
              _hdIcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _hdIcurrentPhase :: (Maybe Int)
              _hdIcurrentPosition :: ((Int, Int))
              _hdIftv :: ([Int])
              _hdImetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _tlIcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _tlIcurrentPhase :: (Maybe Int)
              _tlIcurrentPosition :: ((Int, Int))
              _tlIftv :: ([Int])
              _tlImetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOftv =
                  _hdIftv `union` _tlIftv
              _lhsOcollectConstraints =
                  _tlIcollectConstraints
              _lhsOcurrentPhase =
                  _tlIcurrentPhase
              _lhsOcurrentPosition =
                  _tlIcurrentPosition
              _lhsOmetavarConstraints =
                  _tlImetavarConstraints
              _hdOcollectConstraints =
                  _lhsIcollectConstraints
              _hdOcurrentPhase =
                  _lhsIcurrentPhase
              _hdOcurrentPosition =
                  _lhsIcurrentPosition
              _hdOfromAttribute =
                  _lhsIfromAttribute
              _hdOinfoTuple =
                  _lhsIinfoTuple
              _hdOmetaVariableTable =
                  _lhsImetaVariableTable
              _hdOmetavarConstraints =
                  _lhsImetavarConstraints
              _hdOsubstitution =
                  _lhsIsubstitution
              _tlOcollectConstraints =
                  _hdIcollectConstraints
              _tlOcurrentPhase =
                  _hdIcurrentPhase
              _tlOcurrentPosition =
                  _hdIcurrentPosition
              _tlOfromAttribute =
                  _lhsIfromAttribute
              _tlOinfoTuple =
                  _lhsIinfoTuple
              _tlOmetaVariableTable =
                  _lhsImetaVariableTable
              _tlOmetavarConstraints =
                  _hdImetavarConstraints
              _tlOsubstitution =
                  _lhsIsubstitution
              ( _hdIcollectConstraints,_hdIcurrentPhase,_hdIcurrentPosition,_hdIftv,_hdImetavarConstraints) =
                  (hd_ _hdOcollectConstraints _hdOcurrentPhase _hdOcurrentPosition _hdOfromAttribute _hdOinfoTuple _hdOmetaVariableTable _hdOmetavarConstraints _hdOsubstitution )
              ( _tlIcollectConstraints,_tlIcurrentPhase,_tlIcurrentPosition,_tlIftv,_tlImetavarConstraints) =
                  (tl_ _tlOcollectConstraints _tlOcurrentPhase _tlOcurrentPosition _tlOfromAttribute _tlOinfoTuple _tlOmetaVariableTable _tlOmetavarConstraints _tlOsubstitution )
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))
sem_Core_UserStatements_Nil :: T_Core_UserStatements
sem_Core_UserStatements_Nil  =
    (\ _lhsIcollectConstraints
       _lhsIcurrentPhase
       _lhsIcurrentPosition
       _lhsIfromAttribute
       _lhsIinfoTuple
       _lhsImetaVariableTable
       _lhsImetavarConstraints
       _lhsIsubstitution ->
         (let _lhsOftv :: ([Int])
              _lhsOcollectConstraints :: (Trees (TypeConstraint ConstraintInfo))
              _lhsOcurrentPhase :: (Maybe Int)
              _lhsOcurrentPosition :: ((Int, Int))
              _lhsOmetavarConstraints :: ([(String,Tree (TypeConstraint ConstraintInfo))])
              _lhsOftv =
                  []
              _lhsOcollectConstraints =
                  _lhsIcollectConstraints
              _lhsOcurrentPhase =
                  _lhsIcurrentPhase
              _lhsOcurrentPosition =
                  _lhsIcurrentPosition
              _lhsOmetavarConstraints =
                  _lhsImetavarConstraints
          in  ( _lhsOcollectConstraints,_lhsOcurrentPhase,_lhsOcurrentPosition,_lhsOftv,_lhsOmetavarConstraints)))