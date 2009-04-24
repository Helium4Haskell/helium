
-- UUAGC 0.9.5 (ResolveOperators.ag)
module ResolveOperators where

import UHA_Utils
import UHA_Syntax 
import UHA_Range
import OperatorTable
import Char
import Utils
import Messages
import qualified Data.Map as M


data ResolveError = 
    Ambiguous Assoc Name Assoc Name

instance HasMessage ResolveError where
    getRanges (Ambiguous _ n1 _ n2) = 
        [ getNameRange n1, getNameRange n2 ]
    
    getMessage (Ambiguous assoc1 op1 assoc2 op2) = 
        let 
            assocString AssocRight = "right-associative"
            assocString AssocLeft  = "left-associative"
            assocString AssocNone  = "non-associative"

            firstLine =
                    "Ambiguous use of "
                ++  assocString (assoc1)
                ++  " operator "
                ++  show op1
            secondLine = 
                    " with "
                ++  assocString (assoc2)
                ++  " operator "
                ++  show op2
        in [ MessageOneLiner ( MessageString $ firstLine ++ secondLine ) ]
        
resolveOperators :: OperatorTable -> Module -> (Module, [ResolveError])
resolveOperators opTable m = 
    let (errs, newModule) = sem_Module m opTable []
    in (newModule, errs)

expression opTable e = -- !!! errors ignored
    let (errs, newE) = sem_Expression e opTable [] 
    in newE

operatorsFromModule :: Module -> OperatorTable
operatorsFromModule m =
    M.fromList (concatMap declToOps (collectInfixdecls m))
  where
    declToOps (Declaration_Fixity _ f (MaybeInt_Just p) os) = 
        [ (o, (p, fixityToAssoc f)) | o <- os ]
    fixityToAssoc f = case f of
        Fixity_Infixl _ -> AssocLeft
        Fixity_Infixr _ -> AssocRight
        Fixity_Infix  _ -> AssocNone

collectInfixdecls :: Module -> [Declaration]
collectInfixdecls 
    (Module_Module _ _ _ (Body_Body _ _ ds)) = filter isInfixdecl ds
    where
        isInfixdecl (Declaration_Fixity _ _ _ _) = True
        isInfixdecl _ = False

            
type State expr = 
    ( [Name] -- operator stack
    , [expr] -- expression/pattern stack
    , [ResolveError]
    )

resolveExpression :: OperatorTable -> [Expression] -> (Expression, [ResolveError])
resolveExpression opTable es = resolve opTable es (getOp, applyMinus, applyBinary) ([], [], []) 
  where
    getOp (Expression_Variable (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp (Expression_Constructor (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp _ = Nothing
    
    applyMinus :: Name -> Expression -> Expression
    applyMinus n e
        | n == intUnaryMinusName =
            Expression_Negate      (mergeRanges (getNameRange n) (getExprRange e)) e
        | n == floatUnaryMinusName = 
            Expression_NegateFloat (mergeRanges (getNameRange n) (getExprRange e)) e
        | otherwise = internalError 
            "ResolveOperators.hs" "resolveExpression.applyMinus" "unknown unary operator"        
            
    applyBinary :: Name -> Expression -> Expression -> Expression
    applyBinary n e1 e2 =
        Expression_InfixApplication 
            (mergeRanges (getExprRange e1) (getExprRange e2)) 
            (MaybeExpression_Just e1) 
            ((if isConstructor n then Expression_Constructor else Expression_Variable) (getNameRange n) n)
            (MaybeExpression_Just e2)
        
resolvePattern :: OperatorTable -> [Pattern] -> (Pattern, [ResolveError])
resolvePattern opTable ps = resolve opTable ps (getOp, applyMinus, applyBinary) ([], [], []) 
  where
    getOp (Pattern_Variable (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp _ = Nothing
    
    applyMinus :: Name -> Pattern -> Pattern
    applyMinus n p@(Pattern_Literal r l) 
        | n == intUnaryMinusName =
            Pattern_Negate (mergeRanges (getNameRange n) r) l
        | n == floatUnaryMinusName = 
            Pattern_NegateFloat (mergeRanges (getNameRange n) r) l            
        | otherwise = internalError 
                "ResolveOperators.hs" "resolvePattern.applyMinus" "unknown unary operator"        
    applyMinus n _ =
        internalError "ResolveOperators" "resolvePattern" "in patterns unary minus is only allowed in front of literals"         
        
    applyBinary :: Name -> Pattern -> Pattern -> Pattern
    applyBinary n p1 p2 =
        Pattern_InfixConstructor 
            (mergeRanges (getPatRange p1) (getPatRange p2)) 
            p1 n p2

resolve :: 
    OperatorTable -> 
    [expr] -> 
    ( expr -> Maybe Name -- get operator name (if it is one)
    , Name -> expr -> expr -- apply minus
    , Name -> expr -> expr -> expr -- apply binary
    ) 
    -> State expr -> (expr, [ResolveError])
resolve opTable exprs fs@(getOp, applyMinus, applyBinary) state = 
    case exprs of 
        [] -> cleanup state
        (expr:exprs) ->
            let newState = 
                    case getOp expr of
                        Nothing   -> pushExpr expr state
                        Just name -> pushOp opTable name state
            in
                resolve opTable exprs fs newState
  where
--    popOp :: State expr -> State expr
    popOp (op:ops, exprs, errs) 
        | isUnary op =
            case exprs of
                (expr:rest) -> (ops, applyMinus op expr : rest, errs)
                _ -> internalError "ResolveOperators" "popOp" "1"
        | otherwise =
            case exprs of
                (expr2:expr1:rest) -> (ops, applyBinary op expr1 expr2 : rest, errs)
                _ -> internalError "ResolveOperators" "popOp" "2"
--    pushOp :: Name -> State expr -> State expr
    pushOp opTable op state@(top:ops, exprs, errs) =
        case strongerOp opTable top op of
            Left True -> pushOp opTable op (popOp state)
            Left False -> (op:top:ops, exprs, errs)
            Right err -> (op:top:ops, exprs, err : errs) -- arbitrary choice
    pushOp _ op ([], exprs, errs) =
        ([op], exprs, errs)
--    cleanup :: State expr -> expr
    cleanup state@(_:_, _, _)       = cleanup (popOp state)
    cleanup state@(_, [expr], errs) = (expr, errs)
    cleanup _ = internalError "ResolveOperators" "cleanup" "invalid state"
    

pushExpr :: expr -> State expr -> State expr
pushExpr expr (ops, exprs, errs) =
    (ops, expr:exprs, errs)
                
strongerOp :: OperatorTable -> Name -> Name -> Either Bool ResolveError
strongerOp opTable op1 op2
    | isBinary op1 && isBinary op2 =
        if prio1 == prio2 then
            if assoc1 == AssocLeft && assoc2 == AssocLeft then
                Left True
            else if assoc1 == AssocRight && assoc2 == AssocRight then
                Left False
            else
                Right (Ambiguous assoc1 op1 assoc2 op2)
        else
            Left (prio1 > prio2)
    | isUnary  op1 && isBinary op2 = 
        Left (prio1 >= prio2)
    | isUnary  op2 = 
        Left False
    | otherwise = internalError "ResolveOperators" "strongerOp" "unable to determine which operator binds stronger"
  where
    assoc1 = assoc opTable op1
    assoc2 = assoc opTable op2
    prio1 = prio opTable op1
    prio2 = prio opTable op2

isUnary :: Name -> Bool
isUnary name = name `elem` [ intUnaryMinusName, floatUnaryMinusName ]

isBinary :: Name -> Bool
isBinary = not . isUnary

-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside )  =
    (sem_Alternative_Alternative (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Alternative (Alternative_Empty _range )  =
    (sem_Alternative_Empty (sem_Range _range ) )
-- semantic domain
type T_Alternative = OperatorTable ->
                     ( [ResolveError] ) ->
                     ( ( [ResolveError] ),Alternative)
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Alternative
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _righthandsideOopTable :: OperatorTable
              _righthandsideOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _righthandsideIresolveErrors :: ( [ResolveError] )
              _righthandsideIself :: RightHandSide
              _self =
                  Alternative_Alternative _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _righthandsideIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              _righthandsideOopTable =
                  _lhsIopTable
              _righthandsideOresolveErrors =
                  _patternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
              ( _righthandsideIresolveErrors,_righthandsideIself) =
                  (righthandside_ _righthandsideOopTable _righthandsideOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Alternative
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _self =
                  Alternative_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list  =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list) )
-- semantic domain
type T_Alternatives = OperatorTable ->
                      ( [ResolveError] ) ->
                      ( ( [ResolveError] ),Alternatives)
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Alternatives
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Alternative
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Alternatives
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Alternatives
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- AnnotatedType -----------------------------------------------
-- cata
sem_AnnotatedType :: AnnotatedType ->
                     T_AnnotatedType
sem_AnnotatedType (AnnotatedType_AnnotatedType _range _strict _type )  =
    (sem_AnnotatedType_AnnotatedType (sem_Range _range ) _strict (sem_Type _type ) )
-- semantic domain
type T_AnnotatedType = ( AnnotatedType)
sem_AnnotatedType_AnnotatedType :: T_Range ->
                                   Bool ->
                                   T_Type ->
                                   T_AnnotatedType
sem_AnnotatedType_AnnotatedType range_ strict_ type_  =
    (let _lhsOself :: AnnotatedType
         _rangeIself :: Range
         _typeIself :: Type
         _self =
             AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
-- AnnotatedTypes ----------------------------------------------
-- cata
sem_AnnotatedTypes :: AnnotatedTypes ->
                      T_AnnotatedTypes
sem_AnnotatedTypes list  =
    (Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list) )
-- semantic domain
type T_AnnotatedTypes = ( AnnotatedTypes)
sem_AnnotatedTypes_Cons :: T_AnnotatedType ->
                           T_AnnotatedTypes ->
                           T_AnnotatedTypes
sem_AnnotatedTypes_Cons hd_ tl_  =
    (let _lhsOself :: AnnotatedTypes
         _hdIself :: AnnotatedType
         _tlIself :: AnnotatedTypes
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes
sem_AnnotatedTypes_Nil  =
    (let _lhsOself :: AnnotatedTypes
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body ->
            T_Body
sem_Body (Body_Body _range _importdeclarations _declarations )  =
    (sem_Body_Body (sem_Range _range ) (sem_ImportDeclarations _importdeclarations ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Body = OperatorTable ->
              ( [ResolveError] ) ->
              ( ( [ResolveError] ),Body)
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Body
              _lhsOresolveErrors :: ( [ResolveError] )
              _declarationsOopTable :: OperatorTable
              _declarationsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _importdeclarationsIself :: ImportDeclarations
              _declarationsIresolveErrors :: ( [ResolveError] )
              _declarationsIself :: Declarations
              _self =
                  Body_Body _rangeIself _importdeclarationsIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _declarationsIresolveErrors
              _declarationsOopTable =
                  _lhsIopTable
              _declarationsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _importdeclarationsIself) =
                  (importdeclarations_ )
              ( _declarationsIresolveErrors,_declarationsIself) =
                  (declarations_ _declarationsOopTable _declarationsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Constructor -------------------------------------------------
-- cata
sem_Constructor :: Constructor ->
                   T_Constructor
sem_Constructor (Constructor_Constructor _range _constructor _types )  =
    (sem_Constructor_Constructor (sem_Range _range ) (sem_Name _constructor ) (sem_AnnotatedTypes _types ) )
sem_Constructor (Constructor_Infix _range _leftType _constructorOperator _rightType )  =
    (sem_Constructor_Infix (sem_Range _range ) (sem_AnnotatedType _leftType ) (sem_Name _constructorOperator ) (sem_AnnotatedType _rightType ) )
sem_Constructor (Constructor_Record _range _constructor _fieldDeclarations )  =
    (sem_Constructor_Record (sem_Range _range ) (sem_Name _constructor ) (sem_FieldDeclarations _fieldDeclarations ) )
-- semantic domain
type T_Constructor = ( Constructor)
sem_Constructor_Constructor :: T_Range ->
                               T_Name ->
                               T_AnnotatedTypes ->
                               T_Constructor
sem_Constructor_Constructor range_ constructor_ types_  =
    (let _lhsOself :: Constructor
         _rangeIself :: Range
         _constructorIself :: Name
         _typesIself :: AnnotatedTypes
         _self =
             Constructor_Constructor _rangeIself _constructorIself _typesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _constructorIself) =
             (constructor_ )
         ( _typesIself) =
             (types_ )
     in  ( _lhsOself))
sem_Constructor_Infix :: T_Range ->
                         T_AnnotatedType ->
                         T_Name ->
                         T_AnnotatedType ->
                         T_Constructor
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_  =
    (let _lhsOself :: Constructor
         _rangeIself :: Range
         _leftTypeIself :: AnnotatedType
         _constructorOperatorIself :: Name
         _rightTypeIself :: AnnotatedType
         _self =
             Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftTypeIself) =
             (leftType_ )
         ( _constructorOperatorIself) =
             (constructorOperator_ )
         ( _rightTypeIself) =
             (rightType_ )
     in  ( _lhsOself))
sem_Constructor_Record :: T_Range ->
                          T_Name ->
                          T_FieldDeclarations ->
                          T_Constructor
sem_Constructor_Record range_ constructor_ fieldDeclarations_  =
    (let _lhsOself :: Constructor
         _rangeIself :: Range
         _constructorIself :: Name
         _fieldDeclarationsIself :: FieldDeclarations
         _self =
             Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _constructorIself) =
             (constructor_ )
         ( _fieldDeclarationsIself) =
             (fieldDeclarations_ )
     in  ( _lhsOself))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors ->
                    T_Constructors
sem_Constructors list  =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list) )
-- semantic domain
type T_Constructors = ( Constructors)
sem_Constructors_Cons :: T_Constructor ->
                         T_Constructors ->
                         T_Constructors
sem_Constructors_Cons hd_ tl_  =
    (let _lhsOself :: Constructors
         _hdIself :: Constructor
         _tlIself :: Constructors
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Constructors_Nil :: T_Constructors
sem_Constructors_Nil  =
    (let _lhsOself :: Constructors
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ContextItem -------------------------------------------------
-- cata
sem_ContextItem :: ContextItem ->
                   T_ContextItem
sem_ContextItem (ContextItem_ContextItem _range _name _types )  =
    (sem_ContextItem_ContextItem (sem_Range _range ) (sem_Name _name ) (sem_Types _types ) )
-- semantic domain
type T_ContextItem = ( ContextItem)
sem_ContextItem_ContextItem :: T_Range ->
                               T_Name ->
                               T_Types ->
                               T_ContextItem
sem_ContextItem_ContextItem range_ name_ types_  =
    (let _lhsOself :: ContextItem
         _rangeIself :: Range
         _nameIself :: Name
         _typesIself :: Types
         _self =
             ContextItem_ContextItem _rangeIself _nameIself _typesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _typesIself) =
             (types_ )
     in  ( _lhsOself))
-- ContextItems ------------------------------------------------
-- cata
sem_ContextItems :: ContextItems ->
                    T_ContextItems
sem_ContextItems list  =
    (Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list) )
-- semantic domain
type T_ContextItems = ( ContextItems)
sem_ContextItems_Cons :: T_ContextItem ->
                         T_ContextItems ->
                         T_ContextItems
sem_ContextItems_Cons hd_ tl_  =
    (let _lhsOself :: ContextItems
         _hdIself :: ContextItem
         _tlIself :: ContextItems
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_ContextItems_Nil :: T_ContextItems
sem_ContextItems_Nil  =
    (let _lhsOself :: ContextItems
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Declaration -------------------------------------------------
-- cata
sem_Declaration :: Declaration ->
                   T_Declaration
sem_Declaration (Declaration_Class _range _context _simpletype _where )  =
    (sem_Declaration_Class (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_MaybeDeclarations _where ) )
sem_Declaration (Declaration_Data _range _context _simpletype _constructors _derivings )  =
    (sem_Declaration_Data (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_Constructors _constructors ) (sem_Names _derivings ) )
sem_Declaration (Declaration_Default _range _types )  =
    (sem_Declaration_Default (sem_Range _range ) (sem_Types _types ) )
sem_Declaration (Declaration_Empty _range )  =
    (sem_Declaration_Empty (sem_Range _range ) )
sem_Declaration (Declaration_Fixity _range _fixity _priority _operators )  =
    (sem_Declaration_Fixity (sem_Range _range ) (sem_Fixity _fixity ) (sem_MaybeInt _priority ) (sem_Names _operators ) )
sem_Declaration (Declaration_FunctionBindings _range _bindings )  =
    (sem_Declaration_FunctionBindings (sem_Range _range ) (sem_FunctionBindings _bindings ) )
sem_Declaration (Declaration_Instance _range _context _name _types _where )  =
    (sem_Declaration_Instance (sem_Range _range ) (sem_ContextItems _context ) (sem_Name _name ) (sem_Types _types ) (sem_MaybeDeclarations _where ) )
sem_Declaration (Declaration_Newtype _range _context _simpletype _constructor _derivings )  =
    (sem_Declaration_Newtype (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_Constructor _constructor ) (sem_Names _derivings ) )
sem_Declaration (Declaration_PatternBinding _range _pattern _righthandside )  =
    (sem_Declaration_PatternBinding (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Declaration (Declaration_Type _range _simpletype _type )  =
    (sem_Declaration_Type (sem_Range _range ) (sem_SimpleType _simpletype ) (sem_Type _type ) )
sem_Declaration (Declaration_TypeSignature _range _names _type )  =
    (sem_Declaration_TypeSignature (sem_Range _range ) (sem_Names _names ) (sem_Type _type ) )
-- semantic domain
type T_Declaration = OperatorTable ->
                     ( [ResolveError] ) ->
                     ( ( [ResolveError] ),Declaration)
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _whereOopTable :: OperatorTable
              _whereOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIself :: SimpleType
              _whereIresolveErrors :: ( [ResolveError] )
              _whereIself :: MaybeDeclarations
              _self =
                  Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _whereIresolveErrors
              _whereOopTable =
                  _lhsIopTable
              _whereOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIself) =
                  (simpletype_ )
              ( _whereIresolveErrors,_whereIself) =
                  (where_ _whereOopTable _whereOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIself :: SimpleType
              _constructorsIself :: Constructors
              _derivingsIself :: Names
              _self =
                  Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIself) =
                  (simpletype_ )
              ( _constructorsIself) =
                  (constructors_ )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _typesIself :: Types
              _self =
                  Declaration_Default _rangeIself _typesIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _typesIself) =
                  (types_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _self =
                  Declaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _fixityIself :: Fixity
              _priorityIself :: MaybeInt
              _operatorsIself :: Names
              _self =
                  Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _fixityIself) =
                  (fixity_ )
              ( _priorityIself) =
                  (priority_ )
              ( _operatorsIself) =
                  (operators_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _bindingsOopTable :: OperatorTable
              _bindingsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _bindingsIresolveErrors :: ( [ResolveError] )
              _bindingsIself :: FunctionBindings
              _self =
                  Declaration_FunctionBindings _rangeIself _bindingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _bindingsIresolveErrors
              _bindingsOopTable =
                  _lhsIopTable
              _bindingsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _bindingsIresolveErrors,_bindingsIself) =
                  (bindings_ _bindingsOopTable _bindingsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _whereOopTable :: OperatorTable
              _whereOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _contextIself :: ContextItems
              _nameIself :: Name
              _typesIself :: Types
              _whereIresolveErrors :: ( [ResolveError] )
              _whereIself :: MaybeDeclarations
              _self =
                  Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _whereIresolveErrors
              _whereOopTable =
                  _lhsIopTable
              _whereOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _nameIself) =
                  (name_ )
              ( _typesIself) =
                  (types_ )
              ( _whereIresolveErrors,_whereIself) =
                  (where_ _whereOopTable _whereOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIself :: SimpleType
              _constructorIself :: Constructor
              _derivingsIself :: Names
              _self =
                  Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIself) =
                  (simpletype_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _righthandsideOopTable :: OperatorTable
              _righthandsideOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _righthandsideIresolveErrors :: ( [ResolveError] )
              _righthandsideIself :: RightHandSide
              _self =
                  Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _righthandsideIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              _righthandsideOopTable =
                  _lhsIopTable
              _righthandsideOresolveErrors =
                  _patternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
              ( _righthandsideIresolveErrors,_righthandsideIself) =
                  (righthandside_ _righthandsideOopTable _righthandsideOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _simpletypeIself :: SimpleType
              _typeIself :: Type
              _self =
                  Declaration_Type _rangeIself _simpletypeIself _typeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _simpletypeIself) =
                  (simpletype_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declaration
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _namesIself :: Names
              _typeIself :: Type
              _self =
                  Declaration_TypeSignature _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _namesIself) =
                  (names_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list  =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list) )
-- semantic domain
type T_Declarations = OperatorTable ->
                      ( [ResolveError] ) ->
                      ( ( [ResolveError] ),Declarations)
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declarations
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Declaration
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Declarations
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Declarations
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Export ------------------------------------------------------
-- cata
sem_Export :: Export ->
              T_Export
sem_Export (Export_Module _range _name )  =
    (sem_Export_Module (sem_Range _range ) (sem_Name _name ) )
sem_Export (Export_TypeOrClass _range _name _names )  =
    (sem_Export_TypeOrClass (sem_Range _range ) (sem_Name _name ) (sem_MaybeNames _names ) )
sem_Export (Export_TypeOrClassComplete _range _name )  =
    (sem_Export_TypeOrClassComplete (sem_Range _range ) (sem_Name _name ) )
sem_Export (Export_Variable _range _name )  =
    (sem_Export_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Export = ( Export)
sem_Export_Module :: T_Range ->
                     T_Name ->
                     T_Export
sem_Export_Module range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Module _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Export_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Export
sem_Export_TypeOrClass range_ name_ names_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Export_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_Export_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Export
sem_Export_TypeOrClassComplete range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Export_Variable :: T_Range ->
                       T_Name ->
                       T_Export
sem_Export_Variable range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports ->
               T_Exports
sem_Exports list  =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list) )
-- semantic domain
type T_Exports = ( Exports)
sem_Exports_Cons :: T_Export ->
                    T_Exports ->
                    T_Exports
sem_Exports_Cons hd_ tl_  =
    (let _lhsOself :: Exports
         _hdIself :: Export
         _tlIself :: Exports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Exports_Nil :: T_Exports
sem_Exports_Nil  =
    (let _lhsOself :: Exports
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Expression --------------------------------------------------
-- cata
sem_Expression :: Expression ->
                  T_Expression
sem_Expression (Expression_Case _range _expression _alternatives )  =
    (sem_Expression_Case (sem_Range _range ) (sem_Expression _expression ) (sem_Alternatives _alternatives ) )
sem_Expression (Expression_Comprehension _range _expression _qualifiers )  =
    (sem_Expression_Comprehension (sem_Range _range ) (sem_Expression _expression ) (sem_Qualifiers _qualifiers ) )
sem_Expression (Expression_Constructor _range _name )  =
    (sem_Expression_Constructor (sem_Range _range ) (sem_Name _name ) )
sem_Expression (Expression_Do _range _statements )  =
    (sem_Expression_Do (sem_Range _range ) (sem_Statements _statements ) )
sem_Expression (Expression_Enum _range _from _then _to )  =
    (sem_Expression_Enum (sem_Range _range ) (sem_Expression _from ) (sem_MaybeExpression _then ) (sem_MaybeExpression _to ) )
sem_Expression (Expression_If _range _guardExpression _thenExpression _elseExpression )  =
    (sem_Expression_If (sem_Range _range ) (sem_Expression _guardExpression ) (sem_Expression _thenExpression ) (sem_Expression _elseExpression ) )
sem_Expression (Expression_InfixApplication _range _leftExpression _operator _rightExpression )  =
    (sem_Expression_InfixApplication (sem_Range _range ) (sem_MaybeExpression _leftExpression ) (sem_Expression _operator ) (sem_MaybeExpression _rightExpression ) )
sem_Expression (Expression_Lambda _range _patterns _expression )  =
    (sem_Expression_Lambda (sem_Range _range ) (sem_Patterns _patterns ) (sem_Expression _expression ) )
sem_Expression (Expression_Let _range _declarations _expression )  =
    (sem_Expression_Let (sem_Range _range ) (sem_Declarations _declarations ) (sem_Expression _expression ) )
sem_Expression (Expression_List _range _expressions )  =
    (sem_Expression_List (sem_Range _range ) (sem_Expressions _expressions ) )
sem_Expression (Expression_Literal _range _literal )  =
    (sem_Expression_Literal (sem_Range _range ) (sem_Literal _literal ) )
sem_Expression (Expression_Negate _range _expression )  =
    (sem_Expression_Negate (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_NegateFloat _range _expression )  =
    (sem_Expression_NegateFloat (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_NormalApplication _range _function _arguments )  =
    (sem_Expression_NormalApplication (sem_Range _range ) (sem_Expression _function ) (sem_Expressions _arguments ) )
sem_Expression (Expression_Parenthesized _range _expression )  =
    (sem_Expression_Parenthesized (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_RecordConstruction _range _name _recordExpressionBindings )  =
    (sem_Expression_RecordConstruction (sem_Range _range ) (sem_Name _name ) (sem_RecordExpressionBindings _recordExpressionBindings ) )
sem_Expression (Expression_RecordUpdate _range _expression _recordExpressionBindings )  =
    (sem_Expression_RecordUpdate (sem_Range _range ) (sem_Expression _expression ) (sem_RecordExpressionBindings _recordExpressionBindings ) )
sem_Expression (Expression_Tuple _range _expressions )  =
    (sem_Expression_Tuple (sem_Range _range ) (sem_Expressions _expressions ) )
sem_Expression (Expression_Typed _range _expression _type )  =
    (sem_Expression_Typed (sem_Range _range ) (sem_Expression _expression ) (sem_Type _type ) )
sem_Expression (Expression_Variable _range _name )  =
    (sem_Expression_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Expression = OperatorTable ->
                    ( [ResolveError] ) ->
                    ( ( [ResolveError] ),Expression)
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _alternativesOopTable :: OperatorTable
              _alternativesOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _alternativesIresolveErrors :: ( [ResolveError] )
              _alternativesIself :: Alternatives
              _self =
                  Expression_Case _rangeIself _expressionIself _alternativesIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _alternativesIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              _alternativesOopTable =
                  _lhsIopTable
              _alternativesOresolveErrors =
                  _expressionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
              ( _alternativesIresolveErrors,_alternativesIself) =
                  (alternatives_ _alternativesOopTable _alternativesOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _qualifiersOopTable :: OperatorTable
              _qualifiersOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _qualifiersIresolveErrors :: ( [ResolveError] )
              _qualifiersIself :: Qualifiers
              _self =
                  Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _qualifiersIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              _qualifiersOopTable =
                  _lhsIopTable
              _qualifiersOresolveErrors =
                  _expressionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
              ( _qualifiersIresolveErrors,_qualifiersIself) =
                  (qualifiers_ _qualifiersOopTable _qualifiersOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _self =
                  Expression_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _statementsOopTable :: OperatorTable
              _statementsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _statementsIresolveErrors :: ( [ResolveError] )
              _statementsIself :: Statements
              _self =
                  Expression_Do _rangeIself _statementsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _statementsIresolveErrors
              _statementsOopTable =
                  _lhsIopTable
              _statementsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _statementsIresolveErrors,_statementsIself) =
                  (statements_ _statementsOopTable _statementsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _fromOopTable :: OperatorTable
              _fromOresolveErrors :: ( [ResolveError] )
              _thenOopTable :: OperatorTable
              _thenOresolveErrors :: ( [ResolveError] )
              _toOopTable :: OperatorTable
              _toOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _fromIresolveErrors :: ( [ResolveError] )
              _fromIself :: Expression
              _thenIresolveErrors :: ( [ResolveError] )
              _thenIself :: MaybeExpression
              _toIresolveErrors :: ( [ResolveError] )
              _toIself :: MaybeExpression
              _self =
                  Expression_Enum _rangeIself _fromIself _thenIself _toIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _toIresolveErrors
              _fromOopTable =
                  _lhsIopTable
              _fromOresolveErrors =
                  _lhsIresolveErrors
              _thenOopTable =
                  _lhsIopTable
              _thenOresolveErrors =
                  _fromIresolveErrors
              _toOopTable =
                  _lhsIopTable
              _toOresolveErrors =
                  _thenIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _fromIresolveErrors,_fromIself) =
                  (from_ _fromOopTable _fromOresolveErrors )
              ( _thenIresolveErrors,_thenIself) =
                  (then_ _thenOopTable _thenOresolveErrors )
              ( _toIresolveErrors,_toIself) =
                  (to_ _toOopTable _toOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _guardExpressionOopTable :: OperatorTable
              _guardExpressionOresolveErrors :: ( [ResolveError] )
              _thenExpressionOopTable :: OperatorTable
              _thenExpressionOresolveErrors :: ( [ResolveError] )
              _elseExpressionOopTable :: OperatorTable
              _elseExpressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _guardExpressionIresolveErrors :: ( [ResolveError] )
              _guardExpressionIself :: Expression
              _thenExpressionIresolveErrors :: ( [ResolveError] )
              _thenExpressionIself :: Expression
              _elseExpressionIresolveErrors :: ( [ResolveError] )
              _elseExpressionIself :: Expression
              _self =
                  Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _elseExpressionIresolveErrors
              _guardExpressionOopTable =
                  _lhsIopTable
              _guardExpressionOresolveErrors =
                  _lhsIresolveErrors
              _thenExpressionOopTable =
                  _lhsIopTable
              _thenExpressionOresolveErrors =
                  _guardExpressionIresolveErrors
              _elseExpressionOopTable =
                  _lhsIopTable
              _elseExpressionOresolveErrors =
                  _thenExpressionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _guardExpressionIresolveErrors,_guardExpressionIself) =
                  (guardExpression_ _guardExpressionOopTable _guardExpressionOresolveErrors )
              ( _thenExpressionIresolveErrors,_thenExpressionIself) =
                  (thenExpression_ _thenExpressionOopTable _thenExpressionOresolveErrors )
              ( _elseExpressionIresolveErrors,_elseExpressionIself) =
                  (elseExpression_ _elseExpressionOopTable _elseExpressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _leftExpressionOopTable :: OperatorTable
              _leftExpressionOresolveErrors :: ( [ResolveError] )
              _operatorOopTable :: OperatorTable
              _operatorOresolveErrors :: ( [ResolveError] )
              _rightExpressionOopTable :: OperatorTable
              _rightExpressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _leftExpressionIresolveErrors :: ( [ResolveError] )
              _leftExpressionIself :: MaybeExpression
              _operatorIresolveErrors :: ( [ResolveError] )
              _operatorIself :: Expression
              _rightExpressionIresolveErrors :: ( [ResolveError] )
              _rightExpressionIself :: MaybeExpression
              _self =
                  Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _rightExpressionIresolveErrors
              _leftExpressionOopTable =
                  _lhsIopTable
              _leftExpressionOresolveErrors =
                  _lhsIresolveErrors
              _operatorOopTable =
                  _lhsIopTable
              _operatorOresolveErrors =
                  _leftExpressionIresolveErrors
              _rightExpressionOopTable =
                  _lhsIopTable
              _rightExpressionOresolveErrors =
                  _operatorIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _leftExpressionIresolveErrors,_leftExpressionIself) =
                  (leftExpression_ _leftExpressionOopTable _leftExpressionOresolveErrors )
              ( _operatorIresolveErrors,_operatorIself) =
                  (operator_ _operatorOopTable _operatorOresolveErrors )
              ( _rightExpressionIresolveErrors,_rightExpressionIself) =
                  (rightExpression_ _rightExpressionOopTable _rightExpressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Expression_Lambda _rangeIself _patternsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lhsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _patternsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _declarationsOopTable :: OperatorTable
              _declarationsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _declarationsIresolveErrors :: ( [ResolveError] )
              _declarationsIself :: Declarations
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Expression_Let _rangeIself _declarationsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _declarationsOopTable =
                  _lhsIopTable
              _declarationsOresolveErrors =
                  _lhsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _declarationsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIresolveErrors,_declarationsIself) =
                  (declarations_ _declarationsOopTable _declarationsOresolveErrors )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOresolveErrors :: ( [ResolveError] )
              _lhsOself :: Expression
              _expressionsOopTable :: OperatorTable
              _expressionsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionsIresolveErrors :: ( [ResolveError] )
              _expressionsIself :: Expressions
              _lhsOresolveErrors =
                  _errs ++ _expressionsIresolveErrors
              __tup1 =
                  case _rangeIself of
                      Range_Range Position_Unknown Position_Unknown ->
                          resolveExpression _lhsIopTable _expressionsIself
                      _ -> (Expression_List _rangeIself _expressionsIself, [])
              (_self,_) =
                  __tup1
              (_,_errs) =
                  __tup1
              _lhsOself =
                  _self
              _expressionsOopTable =
                  _lhsIopTable
              _expressionsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIresolveErrors,_expressionsIself) =
                  (expressions_ _expressionsOopTable _expressionsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _literalIself :: Literal
              _self =
                  Expression_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIself) =
                  (literal_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Expression_Negate _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Expression_NegateFloat _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _functionOopTable :: OperatorTable
              _functionOresolveErrors :: ( [ResolveError] )
              _argumentsOopTable :: OperatorTable
              _argumentsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _functionIresolveErrors :: ( [ResolveError] )
              _functionIself :: Expression
              _argumentsIresolveErrors :: ( [ResolveError] )
              _argumentsIself :: Expressions
              _self =
                  Expression_NormalApplication _rangeIself _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _argumentsIresolveErrors
              _functionOopTable =
                  _lhsIopTable
              _functionOresolveErrors =
                  _lhsIresolveErrors
              _argumentsOopTable =
                  _lhsIopTable
              _argumentsOresolveErrors =
                  _functionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _functionIresolveErrors,_functionIself) =
                  (function_ _functionOopTable _functionOresolveErrors )
              ( _argumentsIresolveErrors,_argumentsIself) =
                  (arguments_ _argumentsOopTable _argumentsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Expression_Parenthesized _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _recordExpressionBindingsOopTable :: OperatorTable
              _recordExpressionBindingsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _recordExpressionBindingsIresolveErrors :: ( [ResolveError] )
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _self =
                  Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _recordExpressionBindingsIresolveErrors
              _recordExpressionBindingsOopTable =
                  _lhsIopTable
              _recordExpressionBindingsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordExpressionBindingsIresolveErrors,_recordExpressionBindingsIself) =
                  (recordExpressionBindings_ _recordExpressionBindingsOopTable _recordExpressionBindingsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _recordExpressionBindingsOopTable :: OperatorTable
              _recordExpressionBindingsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _recordExpressionBindingsIresolveErrors :: ( [ResolveError] )
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _self =
                  Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _recordExpressionBindingsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              _recordExpressionBindingsOopTable =
                  _lhsIopTable
              _recordExpressionBindingsOresolveErrors =
                  _expressionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
              ( _recordExpressionBindingsIresolveErrors,_recordExpressionBindingsIself) =
                  (recordExpressionBindings_ _recordExpressionBindingsOopTable _recordExpressionBindingsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionsOopTable :: OperatorTable
              _expressionsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionsIresolveErrors :: ( [ResolveError] )
              _expressionsIself :: Expressions
              _self =
                  Expression_Tuple _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionsIresolveErrors
              _expressionsOopTable =
                  _lhsIopTable
              _expressionsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIresolveErrors,_expressionsIself) =
                  (expressions_ _expressionsOopTable _expressionsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _typeIself :: Type
              _self =
                  Expression_Typed _rangeIself _expressionIself _typeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expression
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _self =
                  Expression_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list  =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list) )
-- semantic domain
type T_Expressions = OperatorTable ->
                     ( [ResolveError] ) ->
                     ( ( [ResolveError] ),Expressions)
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expressions
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Expression
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Expressions
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Expressions
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- FieldDeclaration --------------------------------------------
-- cata
sem_FieldDeclaration :: FieldDeclaration ->
                        T_FieldDeclaration
sem_FieldDeclaration (FieldDeclaration_FieldDeclaration _range _names _type )  =
    (sem_FieldDeclaration_FieldDeclaration (sem_Range _range ) (sem_Names _names ) (sem_AnnotatedType _type ) )
-- semantic domain
type T_FieldDeclaration = ( FieldDeclaration)
sem_FieldDeclaration_FieldDeclaration :: T_Range ->
                                         T_Names ->
                                         T_AnnotatedType ->
                                         T_FieldDeclaration
sem_FieldDeclaration_FieldDeclaration range_ names_ type_  =
    (let _lhsOself :: FieldDeclaration
         _rangeIself :: Range
         _namesIself :: Names
         _typeIself :: AnnotatedType
         _self =
             FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _namesIself) =
             (names_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
-- FieldDeclarations -------------------------------------------
-- cata
sem_FieldDeclarations :: FieldDeclarations ->
                         T_FieldDeclarations
sem_FieldDeclarations list  =
    (Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list) )
-- semantic domain
type T_FieldDeclarations = ( FieldDeclarations)
sem_FieldDeclarations_Cons :: T_FieldDeclaration ->
                              T_FieldDeclarations ->
                              T_FieldDeclarations
sem_FieldDeclarations_Cons hd_ tl_  =
    (let _lhsOself :: FieldDeclarations
         _hdIself :: FieldDeclaration
         _tlIself :: FieldDeclarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_FieldDeclarations_Nil :: T_FieldDeclarations
sem_FieldDeclarations_Nil  =
    (let _lhsOself :: FieldDeclarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Fixity ------------------------------------------------------
-- cata
sem_Fixity :: Fixity ->
              T_Fixity
sem_Fixity (Fixity_Infix _range )  =
    (sem_Fixity_Infix (sem_Range _range ) )
sem_Fixity (Fixity_Infixl _range )  =
    (sem_Fixity_Infixl (sem_Range _range ) )
sem_Fixity (Fixity_Infixr _range )  =
    (sem_Fixity_Infixr (sem_Range _range ) )
-- semantic domain
type T_Fixity = ( Fixity)
sem_Fixity_Infix :: T_Range ->
                    T_Fixity
sem_Fixity_Infix range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infix _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Fixity_Infixl :: T_Range ->
                     T_Fixity
sem_Fixity_Infixl range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixl _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Fixity_Infixr :: T_Range ->
                     T_Fixity
sem_Fixity_Infixr range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixr _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
-- FunctionBinding ---------------------------------------------
-- cata
sem_FunctionBinding :: FunctionBinding ->
                       T_FunctionBinding
sem_FunctionBinding (FunctionBinding_FunctionBinding _range _lefthandside _righthandside )  =
    (sem_FunctionBinding_FunctionBinding (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_RightHandSide _righthandside ) )
-- semantic domain
type T_FunctionBinding = OperatorTable ->
                         ( [ResolveError] ) ->
                         ( ( [ResolveError] ),FunctionBinding)
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: FunctionBinding
              _lhsOresolveErrors :: ( [ResolveError] )
              _lefthandsideOopTable :: OperatorTable
              _lefthandsideOresolveErrors :: ( [ResolveError] )
              _righthandsideOopTable :: OperatorTable
              _righthandsideOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _lefthandsideIresolveErrors :: ( [ResolveError] )
              _lefthandsideIself :: LeftHandSide
              _righthandsideIresolveErrors :: ( [ResolveError] )
              _righthandsideIself :: RightHandSide
              _self =
                  FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _righthandsideIresolveErrors
              _lefthandsideOopTable =
                  _lhsIopTable
              _lefthandsideOresolveErrors =
                  _lhsIresolveErrors
              _righthandsideOopTable =
                  _lhsIopTable
              _righthandsideOresolveErrors =
                  _lefthandsideIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIresolveErrors,_lefthandsideIself) =
                  (lefthandside_ _lefthandsideOopTable _lefthandsideOresolveErrors )
              ( _righthandsideIresolveErrors,_righthandsideIself) =
                  (righthandside_ _righthandsideOopTable _righthandsideOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list  =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list) )
-- semantic domain
type T_FunctionBindings = OperatorTable ->
                          ( [ResolveError] ) ->
                          ( ( [ResolveError] ),FunctionBindings)
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: FunctionBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: FunctionBinding
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: FunctionBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: FunctionBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression )  =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range ) (sem_Expression _guard ) (sem_Expression _expression ) )
-- semantic domain
type T_GuardedExpression = OperatorTable ->
                           ( [ResolveError] ) ->
                           ( ( [ResolveError] ),GuardedExpression)
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: GuardedExpression
              _lhsOresolveErrors :: ( [ResolveError] )
              _guardOopTable :: OperatorTable
              _guardOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _guardIresolveErrors :: ( [ResolveError] )
              _guardIself :: Expression
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _guardOopTable =
                  _lhsIopTable
              _guardOresolveErrors =
                  _lhsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _guardIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _guardIresolveErrors,_guardIself) =
                  (guard_ _guardOopTable _guardOresolveErrors )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list  =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list) )
-- semantic domain
type T_GuardedExpressions = OperatorTable ->
                            ( [ResolveError] ) ->
                            ( ( [ResolveError] ),GuardedExpressions)
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: GuardedExpressions
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: GuardedExpression
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: GuardedExpressions
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: GuardedExpressions
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Import ------------------------------------------------------
-- cata
sem_Import :: Import ->
              T_Import
sem_Import (Import_TypeOrClass _range _name _names )  =
    (sem_Import_TypeOrClass (sem_Range _range ) (sem_Name _name ) (sem_MaybeNames _names ) )
sem_Import (Import_TypeOrClassComplete _range _name )  =
    (sem_Import_TypeOrClassComplete (sem_Range _range ) (sem_Name _name ) )
sem_Import (Import_Variable _range _name )  =
    (sem_Import_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Import = ( Import)
sem_Import_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Import
sem_Import_TypeOrClass range_ name_ names_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Import_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_Import_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Import
sem_Import_TypeOrClassComplete range_ name_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Import_Variable :: T_Range ->
                       T_Name ->
                       T_Import
sem_Import_Variable range_ name_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- ImportDeclaration -------------------------------------------
-- cata
sem_ImportDeclaration :: ImportDeclaration ->
                         T_ImportDeclaration
sem_ImportDeclaration (ImportDeclaration_Empty _range )  =
    (sem_ImportDeclaration_Empty (sem_Range _range ) )
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification )  =
    (sem_ImportDeclaration_Import (sem_Range _range ) _qualified (sem_Name _name ) (sem_MaybeName _asname ) (sem_MaybeImportSpecification _importspecification ) )
-- semantic domain
type T_ImportDeclaration = ( ImportDeclaration)
sem_ImportDeclaration_Empty :: T_Range ->
                               T_ImportDeclaration
sem_ImportDeclaration_Empty range_  =
    (let _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _self =
             ImportDeclaration_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_ImportDeclaration_Import :: T_Range ->
                                Bool ->
                                T_Name ->
                                T_MaybeName ->
                                T_MaybeImportSpecification ->
                                T_ImportDeclaration
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_  =
    (let _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _nameIself :: Name
         _asnameIself :: MaybeName
         _importspecificationIself :: MaybeImportSpecification
         _self =
             ImportDeclaration_Import _rangeIself qualified_ _nameIself _asnameIself _importspecificationIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _asnameIself) =
             (asname_ )
         ( _importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOself))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations ->
                          T_ImportDeclarations
sem_ImportDeclarations list  =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list) )
-- semantic domain
type T_ImportDeclarations = ( ImportDeclarations)
sem_ImportDeclarations_Cons :: T_ImportDeclaration ->
                               T_ImportDeclarations ->
                               T_ImportDeclarations
sem_ImportDeclarations_Cons hd_ tl_  =
    (let _lhsOself :: ImportDeclarations
         _hdIself :: ImportDeclaration
         _tlIself :: ImportDeclarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_ImportDeclarations_Nil :: T_ImportDeclarations
sem_ImportDeclarations_Nil  =
    (let _lhsOself :: ImportDeclarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification ->
                           T_ImportSpecification
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports )  =
    (sem_ImportSpecification_Import (sem_Range _range ) _hiding (sem_Imports _imports ) )
-- semantic domain
type T_ImportSpecification = ( ImportSpecification)
sem_ImportSpecification_Import :: T_Range ->
                                  Bool ->
                                  T_Imports ->
                                  T_ImportSpecification
sem_ImportSpecification_Import range_ hiding_ imports_  =
    (let _lhsOself :: ImportSpecification
         _rangeIself :: Range
         _importsIself :: Imports
         _self =
             ImportSpecification_Import _rangeIself hiding_ _importsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _importsIself) =
             (imports_ )
     in  ( _lhsOself))
-- Imports -----------------------------------------------------
-- cata
sem_Imports :: Imports ->
               T_Imports
sem_Imports list  =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list) )
-- semantic domain
type T_Imports = ( Imports)
sem_Imports_Cons :: T_Import ->
                    T_Imports ->
                    T_Imports
sem_Imports_Cons hd_ tl_  =
    (let _lhsOself :: Imports
         _hdIself :: Import
         _tlIself :: Imports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Imports_Nil :: T_Imports
sem_Imports_Nil  =
    (let _lhsOself :: Imports
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- LeftHandSide ------------------------------------------------
-- cata
sem_LeftHandSide :: LeftHandSide ->
                    T_LeftHandSide
sem_LeftHandSide (LeftHandSide_Function _range _name _patterns )  =
    (sem_LeftHandSide_Function (sem_Range _range ) (sem_Name _name ) (sem_Patterns _patterns ) )
sem_LeftHandSide (LeftHandSide_Infix _range _leftPattern _operator _rightPattern )  =
    (sem_LeftHandSide_Infix (sem_Range _range ) (sem_Pattern _leftPattern ) (sem_Name _operator ) (sem_Pattern _rightPattern ) )
sem_LeftHandSide (LeftHandSide_Parenthesized _range _lefthandside _patterns )  =
    (sem_LeftHandSide_Parenthesized (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_Patterns _patterns ) )
-- semantic domain
type T_LeftHandSide = OperatorTable ->
                      ( [ResolveError] ) ->
                      ( ( [ResolveError] ),LeftHandSide)
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: LeftHandSide
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _self =
                  LeftHandSide_Function _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternsIresolveErrors
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: LeftHandSide
              _lhsOresolveErrors :: ( [ResolveError] )
              _leftPatternOopTable :: OperatorTable
              _leftPatternOresolveErrors :: ( [ResolveError] )
              _rightPatternOopTable :: OperatorTable
              _rightPatternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _leftPatternIresolveErrors :: ( [ResolveError] )
              _leftPatternIself :: Pattern
              _operatorIself :: Name
              _rightPatternIresolveErrors :: ( [ResolveError] )
              _rightPatternIself :: Pattern
              _self =
                  LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _rightPatternIresolveErrors
              _leftPatternOopTable =
                  _lhsIopTable
              _leftPatternOresolveErrors =
                  _lhsIresolveErrors
              _rightPatternOopTable =
                  _lhsIopTable
              _rightPatternOresolveErrors =
                  _leftPatternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIresolveErrors,_leftPatternIself) =
                  (leftPattern_ _leftPatternOopTable _leftPatternOresolveErrors )
              ( _operatorIself) =
                  (operator_ )
              ( _rightPatternIresolveErrors,_rightPatternIself) =
                  (rightPattern_ _rightPatternOopTable _rightPatternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: LeftHandSide
              _lhsOresolveErrors :: ( [ResolveError] )
              _lefthandsideOopTable :: OperatorTable
              _lefthandsideOresolveErrors :: ( [ResolveError] )
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _lefthandsideIresolveErrors :: ( [ResolveError] )
              _lefthandsideIself :: LeftHandSide
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _self =
                  LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternsIresolveErrors
              _lefthandsideOopTable =
                  _lhsIopTable
              _lefthandsideOresolveErrors =
                  _lhsIresolveErrors
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lefthandsideIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIresolveErrors,_lefthandsideIself) =
                  (lefthandside_ _lefthandsideOopTable _lefthandsideOresolveErrors )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Literal -----------------------------------------------------
-- cata
sem_Literal :: Literal ->
               T_Literal
sem_Literal (Literal_Char _range _value )  =
    (sem_Literal_Char (sem_Range _range ) _value )
sem_Literal (Literal_Float _range _value )  =
    (sem_Literal_Float (sem_Range _range ) _value )
sem_Literal (Literal_Int _range _value )  =
    (sem_Literal_Int (sem_Range _range ) _value )
sem_Literal (Literal_String _range _value )  =
    (sem_Literal_String (sem_Range _range ) _value )
-- semantic domain
type T_Literal = ( Literal)
sem_Literal_Char :: T_Range ->
                    String ->
                    T_Literal
sem_Literal_Char range_ value_  =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Char _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Literal_Float :: T_Range ->
                     String ->
                     T_Literal
sem_Literal_Float range_ value_  =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Float _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Literal_Int :: T_Range ->
                   String ->
                   T_Literal
sem_Literal_Int range_ value_  =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Int _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Literal_String :: T_Range ->
                      String ->
                      T_Literal
sem_Literal_String range_ value_  =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_String _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations ->
                         T_MaybeDeclarations
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations )  =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations ) )
sem_MaybeDeclarations (MaybeDeclarations_Nothing )  =
    (sem_MaybeDeclarations_Nothing )
-- semantic domain
type T_MaybeDeclarations = OperatorTable ->
                           ( [ResolveError] ) ->
                           ( ( [ResolveError] ),MaybeDeclarations)
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: MaybeDeclarations
              _lhsOresolveErrors :: ( [ResolveError] )
              _declarationsOopTable :: OperatorTable
              _declarationsOresolveErrors :: ( [ResolveError] )
              _declarationsIresolveErrors :: ( [ResolveError] )
              _declarationsIself :: Declarations
              _self =
                  MaybeDeclarations_Just _declarationsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _declarationsIresolveErrors
              _declarationsOopTable =
                  _lhsIopTable
              _declarationsOresolveErrors =
                  _lhsIresolveErrors
              ( _declarationsIresolveErrors,_declarationsIself) =
                  (declarations_ _declarationsOopTable _declarationsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: MaybeDeclarations
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  MaybeDeclarations_Nothing
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports ->
                    T_MaybeExports
sem_MaybeExports (MaybeExports_Just _exports )  =
    (sem_MaybeExports_Just (sem_Exports _exports ) )
sem_MaybeExports (MaybeExports_Nothing )  =
    (sem_MaybeExports_Nothing )
-- semantic domain
type T_MaybeExports = ( MaybeExports)
sem_MaybeExports_Just :: T_Exports ->
                         T_MaybeExports
sem_MaybeExports_Just exports_  =
    (let _lhsOself :: MaybeExports
         _exportsIself :: Exports
         _self =
             MaybeExports_Just _exportsIself
         _lhsOself =
             _self
         ( _exportsIself) =
             (exports_ )
     in  ( _lhsOself))
sem_MaybeExports_Nothing :: T_MaybeExports
sem_MaybeExports_Nothing  =
    (let _lhsOself :: MaybeExports
         _self =
             MaybeExports_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression ->
                       T_MaybeExpression
sem_MaybeExpression (MaybeExpression_Just _expression )  =
    (sem_MaybeExpression_Just (sem_Expression _expression ) )
sem_MaybeExpression (MaybeExpression_Nothing )  =
    (sem_MaybeExpression_Nothing )
-- semantic domain
type T_MaybeExpression = OperatorTable ->
                         ( [ResolveError] ) ->
                         ( ( [ResolveError] ),MaybeExpression)
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: MaybeExpression
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  MaybeExpression_Just _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: MaybeExpression
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  MaybeExpression_Nothing
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification ->
                                T_MaybeImportSpecification
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification )  =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification ) )
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing )  =
    (sem_MaybeImportSpecification_Nothing )
-- semantic domain
type T_MaybeImportSpecification = ( MaybeImportSpecification)
sem_MaybeImportSpecification_Just :: T_ImportSpecification ->
                                     T_MaybeImportSpecification
sem_MaybeImportSpecification_Just importspecification_  =
    (let _lhsOself :: MaybeImportSpecification
         _importspecificationIself :: ImportSpecification
         _self =
             MaybeImportSpecification_Just _importspecificationIself
         _lhsOself =
             _self
         ( _importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOself))
sem_MaybeImportSpecification_Nothing :: T_MaybeImportSpecification
sem_MaybeImportSpecification_Nothing  =
    (let _lhsOself :: MaybeImportSpecification
         _self =
             MaybeImportSpecification_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeInt ----------------------------------------------------
-- cata
sem_MaybeInt :: MaybeInt ->
                T_MaybeInt
sem_MaybeInt (MaybeInt_Just _int )  =
    (sem_MaybeInt_Just _int )
sem_MaybeInt (MaybeInt_Nothing )  =
    (sem_MaybeInt_Nothing )
-- semantic domain
type T_MaybeInt = ( MaybeInt)
sem_MaybeInt_Just :: Int ->
                     T_MaybeInt
sem_MaybeInt_Just int_  =
    (let _lhsOself :: MaybeInt
         _self =
             MaybeInt_Just int_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_MaybeInt_Nothing :: T_MaybeInt
sem_MaybeInt_Nothing  =
    (let _lhsOself :: MaybeInt
         _self =
             MaybeInt_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeName ---------------------------------------------------
-- cata
sem_MaybeName :: MaybeName ->
                 T_MaybeName
sem_MaybeName (MaybeName_Just _name )  =
    (sem_MaybeName_Just (sem_Name _name ) )
sem_MaybeName (MaybeName_Nothing )  =
    (sem_MaybeName_Nothing )
-- semantic domain
type T_MaybeName = ( MaybeName)
sem_MaybeName_Just :: T_Name ->
                      T_MaybeName
sem_MaybeName_Just name_  =
    (let _lhsOself :: MaybeName
         _nameIself :: Name
         _self =
             MaybeName_Just _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_MaybeName_Nothing :: T_MaybeName
sem_MaybeName_Nothing  =
    (let _lhsOself :: MaybeName
         _self =
             MaybeName_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeNames --------------------------------------------------
-- cata
sem_MaybeNames :: MaybeNames ->
                  T_MaybeNames
sem_MaybeNames (MaybeNames_Just _names )  =
    (sem_MaybeNames_Just (sem_Names _names ) )
sem_MaybeNames (MaybeNames_Nothing )  =
    (sem_MaybeNames_Nothing )
-- semantic domain
type T_MaybeNames = ( MaybeNames)
sem_MaybeNames_Just :: T_Names ->
                       T_MaybeNames
sem_MaybeNames_Just names_  =
    (let _lhsOself :: MaybeNames
         _namesIself :: Names
         _self =
             MaybeNames_Just _namesIself
         _lhsOself =
             _self
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_MaybeNames_Nothing :: T_MaybeNames
sem_MaybeNames_Nothing  =
    (let _lhsOself :: MaybeNames
         _self =
             MaybeNames_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Module ------------------------------------------------------
-- cata
sem_Module :: Module ->
              T_Module
sem_Module (Module_Module _range _name _exports _body )  =
    (sem_Module_Module (sem_Range _range ) (sem_MaybeName _name ) (sem_MaybeExports _exports ) (sem_Body _body ) )
-- semantic domain
type T_Module = OperatorTable ->
                ( [ResolveError] ) ->
                ( ( [ResolveError] ),Module)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Module
              _lhsOresolveErrors :: ( [ResolveError] )
              _bodyOopTable :: OperatorTable
              _bodyOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: MaybeName
              _exportsIself :: MaybeExports
              _bodyIresolveErrors :: ( [ResolveError] )
              _bodyIself :: Body
              _self =
                  Module_Module _rangeIself _nameIself _exportsIself _bodyIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _bodyIresolveErrors
              _bodyOopTable =
                  _lhsIopTable
              _bodyOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _exportsIself) =
                  (exports_ )
              ( _bodyIresolveErrors,_bodyIself) =
                  (body_ _bodyOopTable _bodyOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name (Name_Identifier _range _module _name )  =
    (sem_Name_Identifier (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Operator _range _module _name )  =
    (sem_Name_Operator (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Special _range _module _name )  =
    (sem_Name_Special (sem_Range _range ) (sem_Strings _module ) _name )
-- semantic domain
type T_Name = ( Name)
sem_Name_Identifier :: T_Range ->
                       T_Strings ->
                       String ->
                       T_Name
sem_Name_Identifier range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Identifier _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
sem_Name_Operator :: T_Range ->
                     T_Strings ->
                     String ->
                     T_Name
sem_Name_Operator range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Operator _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
sem_Name_Special :: T_Range ->
                    T_Strings ->
                    String ->
                    T_Name
sem_Name_Special range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Special _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names ->
             T_Names
sem_Names list  =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list) )
-- semantic domain
type T_Names = ( Names)
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_  =
    (let _lhsOself :: Names
         _hdIself :: Name
         _tlIself :: Names
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Names_Nil :: T_Names
sem_Names_Nil  =
    (let _lhsOself :: Names
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Pattern -----------------------------------------------------
-- cata
sem_Pattern :: Pattern ->
               T_Pattern
sem_Pattern (Pattern_As _range _name _pattern )  =
    (sem_Pattern_As (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_Constructor _range _name _patterns )  =
    (sem_Pattern_Constructor (sem_Range _range ) (sem_Name _name ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_InfixConstructor _range _leftPattern _constructorOperator _rightPattern )  =
    (sem_Pattern_InfixConstructor (sem_Range _range ) (sem_Pattern _leftPattern ) (sem_Name _constructorOperator ) (sem_Pattern _rightPattern ) )
sem_Pattern (Pattern_Irrefutable _range _pattern )  =
    (sem_Pattern_Irrefutable (sem_Range _range ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_List _range _patterns )  =
    (sem_Pattern_List (sem_Range _range ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_Literal _range _literal )  =
    (sem_Pattern_Literal (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Negate _range _literal )  =
    (sem_Pattern_Negate (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_NegateFloat _range _literal )  =
    (sem_Pattern_NegateFloat (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Parenthesized _range _pattern )  =
    (sem_Pattern_Parenthesized (sem_Range _range ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_Record _range _name _recordPatternBindings )  =
    (sem_Pattern_Record (sem_Range _range ) (sem_Name _name ) (sem_RecordPatternBindings _recordPatternBindings ) )
sem_Pattern (Pattern_Successor _range _name _literal )  =
    (sem_Pattern_Successor (sem_Range _range ) (sem_Name _name ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Tuple _range _patterns )  =
    (sem_Pattern_Tuple (sem_Range _range ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_Variable _range _name )  =
    (sem_Pattern_Variable (sem_Range _range ) (sem_Name _name ) )
sem_Pattern (Pattern_Wildcard _range )  =
    (sem_Pattern_Wildcard (sem_Range _range ) )
-- semantic domain
type T_Pattern = OperatorTable ->
                 ( [ResolveError] ) ->
                 ( ( [ResolveError] ),Pattern)
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _self =
                  Pattern_As _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _self =
                  Pattern_Constructor _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternsIresolveErrors
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _leftPatternOopTable :: OperatorTable
              _leftPatternOresolveErrors :: ( [ResolveError] )
              _rightPatternOopTable :: OperatorTable
              _rightPatternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _leftPatternIresolveErrors :: ( [ResolveError] )
              _leftPatternIself :: Pattern
              _constructorOperatorIself :: Name
              _rightPatternIresolveErrors :: ( [ResolveError] )
              _rightPatternIself :: Pattern
              _self =
                  Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _rightPatternIresolveErrors
              _leftPatternOopTable =
                  _lhsIopTable
              _leftPatternOresolveErrors =
                  _lhsIresolveErrors
              _rightPatternOopTable =
                  _lhsIopTable
              _rightPatternOresolveErrors =
                  _leftPatternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIresolveErrors,_leftPatternIself) =
                  (leftPattern_ _leftPatternOopTable _leftPatternOresolveErrors )
              ( _constructorOperatorIself) =
                  (constructorOperator_ )
              ( _rightPatternIresolveErrors,_rightPatternIself) =
                  (rightPattern_ _rightPatternOopTable _rightPatternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _self =
                  Pattern_Irrefutable _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOresolveErrors :: ( [ResolveError] )
              _lhsOself :: Pattern
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _lhsOresolveErrors =
                  _errs ++ _patternsIresolveErrors
              __tup2 =
                  case _rangeIself of
                      Range_Range Position_Unknown Position_Unknown ->
                          resolvePattern _lhsIopTable _patternsIself
                      _ ->
                          (Pattern_List _rangeIself _patternsIself, [])
              (_self,_) =
                  __tup2
              (_,_errs) =
                  __tup2
              _lhsOself =
                  _self
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _literalIself :: Literal
              _self =
                  Pattern_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIself) =
                  (literal_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _literalIself :: Literal
              _self =
                  Pattern_Negate _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIself) =
                  (literal_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _literalIself :: Literal
              _self =
                  Pattern_NegateFloat _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIself) =
                  (literal_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _self =
                  Pattern_Parenthesized _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _recordPatternBindingsOopTable :: OperatorTable
              _recordPatternBindingsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _recordPatternBindingsIresolveErrors :: ( [ResolveError] )
              _recordPatternBindingsIself :: RecordPatternBindings
              _self =
                  Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _recordPatternBindingsIresolveErrors
              _recordPatternBindingsOopTable =
                  _lhsIopTable
              _recordPatternBindingsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordPatternBindingsIresolveErrors,_recordPatternBindingsIself) =
                  (recordPatternBindings_ _recordPatternBindingsOopTable _recordPatternBindingsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _literalIself :: Literal
              _self =
                  Pattern_Successor _rangeIself _nameIself _literalIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _literalIself) =
                  (literal_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternsOopTable :: OperatorTable
              _patternsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternsIresolveErrors :: ( [ResolveError] )
              _patternsIself :: Patterns
              _self =
                  Pattern_Tuple _rangeIself _patternsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternsIresolveErrors
              _patternsOopTable =
                  _lhsIopTable
              _patternsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternsIresolveErrors,_patternsIself) =
                  (patterns_ _patternsOopTable _patternsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _self =
                  Pattern_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Pattern
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _self =
                  Pattern_Wildcard _rangeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list  =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list) )
-- semantic domain
type T_Patterns = OperatorTable ->
                  ( [ResolveError] ) ->
                  ( ( [ResolveError] ),Patterns)
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Patterns
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Pattern
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Patterns
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Patterns
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Position ----------------------------------------------------
-- cata
sem_Position :: Position ->
                T_Position
sem_Position (Position_Position _filename _line _column )  =
    (sem_Position_Position _filename _line _column )
sem_Position (Position_Unknown )  =
    (sem_Position_Unknown )
-- semantic domain
type T_Position = ( Position)
sem_Position_Position :: String ->
                         Int ->
                         Int ->
                         T_Position
sem_Position_Position filename_ line_ column_  =
    (let _lhsOself :: Position
         _self =
             Position_Position filename_ line_ column_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Position_Unknown :: T_Position
sem_Position_Unknown  =
    (let _lhsOself :: Position
         _self =
             Position_Unknown
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Qualifier ---------------------------------------------------
-- cata
sem_Qualifier :: Qualifier ->
                 T_Qualifier
sem_Qualifier (Qualifier_Empty _range )  =
    (sem_Qualifier_Empty (sem_Range _range ) )
sem_Qualifier (Qualifier_Generator _range _pattern _expression )  =
    (sem_Qualifier_Generator (sem_Range _range ) (sem_Pattern _pattern ) (sem_Expression _expression ) )
sem_Qualifier (Qualifier_Guard _range _guard )  =
    (sem_Qualifier_Guard (sem_Range _range ) (sem_Expression _guard ) )
sem_Qualifier (Qualifier_Let _range _declarations )  =
    (sem_Qualifier_Let (sem_Range _range ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Qualifier = OperatorTable ->
                   ( [ResolveError] ) ->
                   ( ( [ResolveError] ),Qualifier)
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifier
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _self =
                  Qualifier_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifier
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Qualifier_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _patternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifier
              _lhsOresolveErrors :: ( [ResolveError] )
              _guardOopTable :: OperatorTable
              _guardOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _guardIresolveErrors :: ( [ResolveError] )
              _guardIself :: Expression
              _self =
                  Qualifier_Guard _rangeIself _guardIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _guardIresolveErrors
              _guardOopTable =
                  _lhsIopTable
              _guardOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _guardIresolveErrors,_guardIself) =
                  (guard_ _guardOopTable _guardOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifier
              _lhsOresolveErrors :: ( [ResolveError] )
              _declarationsOopTable :: OperatorTable
              _declarationsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _declarationsIresolveErrors :: ( [ResolveError] )
              _declarationsIself :: Declarations
              _self =
                  Qualifier_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _declarationsIresolveErrors
              _declarationsOopTable =
                  _lhsIopTable
              _declarationsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIresolveErrors,_declarationsIself) =
                  (declarations_ _declarationsOopTable _declarationsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list  =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list) )
-- semantic domain
type T_Qualifiers = OperatorTable ->
                    ( [ResolveError] ) ->
                    ( ( [ResolveError] ),Qualifiers)
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifiers
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Qualifier
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Qualifiers
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Qualifiers
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Range -------------------------------------------------------
-- cata
sem_Range :: Range ->
             T_Range
sem_Range (Range_Range _start _stop )  =
    (sem_Range_Range (sem_Position _start ) (sem_Position _stop ) )
-- semantic domain
type T_Range = ( Range)
sem_Range_Range :: T_Position ->
                   T_Position ->
                   T_Range
sem_Range_Range start_ stop_  =
    (let _lhsOself :: Range
         _startIself :: Position
         _stopIself :: Position
         _self =
             Range_Range _startIself _stopIself
         _lhsOself =
             _self
         ( _startIself) =
             (start_ )
         ( _stopIself) =
             (stop_ )
     in  ( _lhsOself))
-- RecordExpressionBinding -------------------------------------
-- cata
sem_RecordExpressionBinding :: RecordExpressionBinding ->
                               T_RecordExpressionBinding
sem_RecordExpressionBinding (RecordExpressionBinding_RecordExpressionBinding _range _name _expression )  =
    (sem_RecordExpressionBinding_RecordExpressionBinding (sem_Range _range ) (sem_Name _name ) (sem_Expression _expression ) )
-- semantic domain
type T_RecordExpressionBinding = OperatorTable ->
                                 ( [ResolveError] ) ->
                                 ( ( [ResolveError] ),RecordExpressionBinding)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordExpressionBinding
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list  =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list) )
-- semantic domain
type T_RecordExpressionBindings = OperatorTable ->
                                  ( [ResolveError] ) ->
                                  ( ( [ResolveError] ),RecordExpressionBindings)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordExpressionBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: RecordExpressionBinding
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: RecordExpressionBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordExpressionBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding ->
                            T_RecordPatternBinding
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern )  =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
-- semantic domain
type T_RecordPatternBinding = OperatorTable ->
                              ( [ResolveError] ) ->
                              ( ( [ResolveError] ),RecordPatternBinding)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range ->
                                                 T_Name ->
                                                 T_Pattern ->
                                                 T_RecordPatternBinding
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordPatternBinding
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _nameIself :: Name
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _self =
                  RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _patternIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings ->
                             T_RecordPatternBindings
sem_RecordPatternBindings list  =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list) )
-- semantic domain
type T_RecordPatternBindings = OperatorTable ->
                               ( [ResolveError] ) ->
                               ( ( [ResolveError] ),RecordPatternBindings)
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding ->
                                  T_RecordPatternBindings ->
                                  T_RecordPatternBindings
sem_RecordPatternBindings_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordPatternBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: RecordPatternBinding
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: RecordPatternBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings
sem_RecordPatternBindings_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RecordPatternBindings
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide ->
                     T_RightHandSide
sem_RightHandSide (RightHandSide_Expression _range _expression _where )  =
    (sem_RightHandSide_Expression (sem_Range _range ) (sem_Expression _expression ) (sem_MaybeDeclarations _where ) )
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where )  =
    (sem_RightHandSide_Guarded (sem_Range _range ) (sem_GuardedExpressions _guardedexpressions ) (sem_MaybeDeclarations _where ) )
-- semantic domain
type T_RightHandSide = OperatorTable ->
                       ( [ResolveError] ) ->
                       ( ( [ResolveError] ),RightHandSide)
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RightHandSide
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _whereOopTable :: OperatorTable
              _whereOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _whereIresolveErrors :: ( [ResolveError] )
              _whereIself :: MaybeDeclarations
              _self =
                  RightHandSide_Expression _rangeIself _expressionIself _whereIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _whereIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              _whereOopTable =
                  _lhsIopTable
              _whereOresolveErrors =
                  _expressionIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
              ( _whereIresolveErrors,_whereIself) =
                  (where_ _whereOopTable _whereOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: RightHandSide
              _lhsOresolveErrors :: ( [ResolveError] )
              _guardedexpressionsOopTable :: OperatorTable
              _guardedexpressionsOresolveErrors :: ( [ResolveError] )
              _whereOopTable :: OperatorTable
              _whereOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _guardedexpressionsIresolveErrors :: ( [ResolveError] )
              _guardedexpressionsIself :: GuardedExpressions
              _whereIresolveErrors :: ( [ResolveError] )
              _whereIself :: MaybeDeclarations
              _self =
                  RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _whereIresolveErrors
              _guardedexpressionsOopTable =
                  _lhsIopTable
              _guardedexpressionsOresolveErrors =
                  _lhsIresolveErrors
              _whereOopTable =
                  _lhsIopTable
              _whereOresolveErrors =
                  _guardedexpressionsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _guardedexpressionsIresolveErrors,_guardedexpressionsIself) =
                  (guardedexpressions_ _guardedexpressionsOopTable _guardedexpressionsOresolveErrors )
              ( _whereIresolveErrors,_whereIself) =
                  (where_ _whereOopTable _whereOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType ->
                  T_SimpleType
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables )  =
    (sem_SimpleType_SimpleType (sem_Range _range ) (sem_Name _name ) (sem_Names _typevariables ) )
-- semantic domain
type T_SimpleType = ( SimpleType)
sem_SimpleType_SimpleType :: T_Range ->
                             T_Name ->
                             T_Names ->
                             T_SimpleType
sem_SimpleType_SimpleType range_ name_ typevariables_  =
    (let _lhsOself :: SimpleType
         _rangeIself :: Range
         _nameIself :: Name
         _typevariablesIself :: Names
         _self =
             SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _typevariablesIself) =
             (typevariables_ )
     in  ( _lhsOself))
-- Statement ---------------------------------------------------
-- cata
sem_Statement :: Statement ->
                 T_Statement
sem_Statement (Statement_Empty _range )  =
    (sem_Statement_Empty (sem_Range _range ) )
sem_Statement (Statement_Expression _range _expression )  =
    (sem_Statement_Expression (sem_Range _range ) (sem_Expression _expression ) )
sem_Statement (Statement_Generator _range _pattern _expression )  =
    (sem_Statement_Generator (sem_Range _range ) (sem_Pattern _pattern ) (sem_Expression _expression ) )
sem_Statement (Statement_Let _range _declarations )  =
    (sem_Statement_Let (sem_Range _range ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Statement = OperatorTable ->
                   ( [ResolveError] ) ->
                   ( ( [ResolveError] ),Statement)
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statement
              _lhsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _self =
                  Statement_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statement
              _lhsOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Statement_Expression _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statement
              _lhsOresolveErrors :: ( [ResolveError] )
              _patternOopTable :: OperatorTable
              _patternOresolveErrors :: ( [ResolveError] )
              _expressionOopTable :: OperatorTable
              _expressionOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _patternIresolveErrors :: ( [ResolveError] )
              _patternIself :: Pattern
              _expressionIresolveErrors :: ( [ResolveError] )
              _expressionIself :: Expression
              _self =
                  Statement_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _expressionIresolveErrors
              _patternOopTable =
                  _lhsIopTable
              _patternOresolveErrors =
                  _lhsIresolveErrors
              _expressionOopTable =
                  _lhsIopTable
              _expressionOresolveErrors =
                  _patternIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _patternIresolveErrors,_patternIself) =
                  (pattern_ _patternOopTable _patternOresolveErrors )
              ( _expressionIresolveErrors,_expressionIself) =
                  (expression_ _expressionOopTable _expressionOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statement
              _lhsOresolveErrors :: ( [ResolveError] )
              _declarationsOopTable :: OperatorTable
              _declarationsOresolveErrors :: ( [ResolveError] )
              _rangeIself :: Range
              _declarationsIresolveErrors :: ( [ResolveError] )
              _declarationsIself :: Declarations
              _self =
                  Statement_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _declarationsIresolveErrors
              _declarationsOopTable =
                  _lhsIopTable
              _declarationsOresolveErrors =
                  _lhsIresolveErrors
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIresolveErrors,_declarationsIself) =
                  (declarations_ _declarationsOopTable _declarationsOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list  =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list) )
-- semantic domain
type T_Statements = OperatorTable ->
                    ( [ResolveError] ) ->
                    ( ( [ResolveError] ),Statements)
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statements
              _lhsOresolveErrors :: ( [ResolveError] )
              _hdOopTable :: OperatorTable
              _hdOresolveErrors :: ( [ResolveError] )
              _tlOopTable :: OperatorTable
              _tlOresolveErrors :: ( [ResolveError] )
              _hdIresolveErrors :: ( [ResolveError] )
              _hdIself :: Statement
              _tlIresolveErrors :: ( [ResolveError] )
              _tlIself :: Statements
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _tlIresolveErrors
              _hdOopTable =
                  _lhsIopTable
              _hdOresolveErrors =
                  _lhsIresolveErrors
              _tlOopTable =
                  _lhsIopTable
              _tlOresolveErrors =
                  _hdIresolveErrors
              ( _hdIresolveErrors,_hdIself) =
                  (hd_ _hdOopTable _hdOresolveErrors )
              ( _tlIresolveErrors,_tlIself) =
                  (tl_ _tlOopTable _tlOresolveErrors )
          in  ( _lhsOresolveErrors,_lhsOself)))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil  =
    (\ _lhsIopTable
       _lhsIresolveErrors ->
         (let _lhsOself :: Statements
              _lhsOresolveErrors :: ( [ResolveError] )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOresolveErrors =
                  _lhsIresolveErrors
          in  ( _lhsOresolveErrors,_lhsOself)))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings ->
               T_Strings
sem_Strings list  =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list )
-- semantic domain
type T_Strings = ( Strings)
sem_Strings_Cons :: String ->
                    T_Strings ->
                    T_Strings
sem_Strings_Cons hd_ tl_  =
    (let _lhsOself :: Strings
         _tlIself :: Strings
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Strings_Nil :: T_Strings
sem_Strings_Nil  =
    (let _lhsOself :: Strings
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Type --------------------------------------------------------
-- cata
sem_Type :: Type ->
            T_Type
sem_Type (Type_Application _range _prefix _function _arguments )  =
    (sem_Type_Application (sem_Range _range ) _prefix (sem_Type _function ) (sem_Types _arguments ) )
sem_Type (Type_Constructor _range _name )  =
    (sem_Type_Constructor (sem_Range _range ) (sem_Name _name ) )
sem_Type (Type_Exists _range _typevariables _type )  =
    (sem_Type_Exists (sem_Range _range ) (sem_Names _typevariables ) (sem_Type _type ) )
sem_Type (Type_Forall _range _typevariables _type )  =
    (sem_Type_Forall (sem_Range _range ) (sem_Names _typevariables ) (sem_Type _type ) )
sem_Type (Type_Parenthesized _range _type )  =
    (sem_Type_Parenthesized (sem_Range _range ) (sem_Type _type ) )
sem_Type (Type_Qualified _range _context _type )  =
    (sem_Type_Qualified (sem_Range _range ) (sem_ContextItems _context ) (sem_Type _type ) )
sem_Type (Type_Variable _range _name )  =
    (sem_Type_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Type = ( Type)
sem_Type_Application :: T_Range ->
                        Bool ->
                        T_Type ->
                        T_Types ->
                        T_Type
sem_Type_Application range_ prefix_ function_ arguments_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _functionIself :: Type
         _argumentsIself :: Types
         _self =
             Type_Application _rangeIself prefix_ _functionIself _argumentsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _functionIself) =
             (function_ )
         ( _argumentsIself) =
             (arguments_ )
     in  ( _lhsOself))
sem_Type_Constructor :: T_Range ->
                        T_Name ->
                        T_Type
sem_Type_Constructor range_ name_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Type_Constructor _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Type_Exists :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Exists range_ typevariables_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Exists _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesIself) =
             (typevariables_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Forall :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Forall range_ typevariables_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Forall _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesIself) =
             (typevariables_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Parenthesized :: T_Range ->
                          T_Type ->
                          T_Type
sem_Type_Parenthesized range_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typeIself :: Type
         _self =
             Type_Parenthesized _rangeIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Qualified :: T_Range ->
                      T_ContextItems ->
                      T_Type ->
                      T_Type
sem_Type_Qualified range_ context_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _contextIself :: ContextItems
         _typeIself :: Type
         _self =
             Type_Qualified _rangeIself _contextIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Variable :: T_Range ->
                     T_Name ->
                     T_Type
sem_Type_Variable range_ name_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Type_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- Types -------------------------------------------------------
-- cata
sem_Types :: Types ->
             T_Types
sem_Types list  =
    (Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list) )
-- semantic domain
type T_Types = ( Types)
sem_Types_Cons :: T_Type ->
                  T_Types ->
                  T_Types
sem_Types_Cons hd_ tl_  =
    (let _lhsOself :: Types
         _hdIself :: Type
         _tlIself :: Types
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Types_Nil :: T_Types
sem_Types_Nil  =
    (let _lhsOself :: Types
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))