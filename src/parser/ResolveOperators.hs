module ResolveOperators(operatorsFromModule, resolveOperators) where

import UHA_Syntax
import UHA_Utils
import OperatorTable
import Char
import ParseCommon(intUnaryMinusName, floatUnaryMinusName)
import Utils

-- operatoren resolven
-- staan alle imports bovenaan?

operatorsFromModule :: Module -> OperatorTable
operatorsFromModule m =
    concatMap declToOps (collectInfixdecls m)
  where
    declToOps (Declaration_Fixity _ f (MaybeInt_Just p) os) = 
        [ (getNameName o, (p, fixityToAssoc f)) | o <- os ]
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

resolveOperators :: OperatorTable -> Module -> Module
resolveOperators ops m@(Module_Module r mn mes b) = 
    Module_Module r mn mes (body ops b) 
    
-- <BORING>
body :: OperatorTable -> Body -> Body
body ops (Body_Body r is ds) =
    Body_Body r is (declarations ops ds)

declarations :: OperatorTable -> Declarations -> Declarations
declarations opTable ds = map (declaration opTable) ds

declaration :: OperatorTable -> Declaration -> Declaration
declaration opTable d = 
    case d of
        Declaration_FunctionBindings r fs -> 
            Declaration_FunctionBindings r (functionBindings opTable fs)
        Declaration_PatternBinding r p b ->
            Declaration_PatternBinding r (pattern opTable p) (rightHandSide opTable b)
        _ -> d

functionBindings :: OperatorTable -> FunctionBindings -> FunctionBindings       
functionBindings opTable fs = map (functionBinding opTable) fs

functionBinding :: OperatorTable -> FunctionBinding -> FunctionBinding       
functionBinding opTable (FunctionBinding_FunctionBinding r l b) =
    FunctionBinding_FunctionBinding r (leftHandSide opTable l) (rightHandSide opTable b)
    
rightHandSide :: OperatorTable -> RightHandSide -> RightHandSide
rightHandSide opTable b = 
    case b of
        RightHandSide_Expression r e mds ->
            RightHandSide_Expression r (expression opTable e) (maybeDeclarations opTable mds)
        RightHandSide_Guarded r gs mds ->
            RightHandSide_Guarded r (guardedExpressions opTable gs) (maybeDeclarations opTable mds)

maybeDeclarations :: OperatorTable -> MaybeDeclarations -> MaybeDeclarations
maybeDeclarations opTable mds =
    case mds of
        MaybeDeclarations_Just ds ->
            MaybeDeclarations_Just (declarations opTable ds)
        MaybeDeclarations_Nothing ->
            mds
            
guardedExpressions :: OperatorTable -> GuardedExpressions -> GuardedExpressions
guardedExpressions opTable gs = map (guardedExpression opTable) gs

guardedExpression :: OperatorTable -> GuardedExpression -> GuardedExpression
guardedExpression opTable (GuardedExpression_GuardedExpression r e1 e2) =
    GuardedExpression_GuardedExpression r (expression opTable e1) (expression opTable e2)

leftHandSide :: OperatorTable -> LeftHandSide -> LeftHandSide
leftHandSide opTable l = 
    case l of
        LeftHandSide_Function r n ps -> 
            LeftHandSide_Function r n (patterns opTable ps)
        LeftHandSide_Infix r p1 n p2 ->             
            LeftHandSide_Infix r (pattern opTable p1) n (pattern opTable p2)
        LeftHandSide_Parenthesized r l ps ->
            LeftHandSide_Parenthesized r (leftHandSide opTable l) (patterns opTable ps)

patterns :: OperatorTable -> Patterns -> Patterns
patterns opTable ps = map (pattern opTable) ps

alternatives :: OperatorTable -> Alternatives -> Alternatives
alternatives opTable as = map (alternative opTable) as

alternative :: OperatorTable -> Alternative -> Alternative
alternative opTable a =
    case a of
        Alternative_Alternative r p b -> 
            Alternative_Alternative r (pattern opTable p) (rightHandSide opTable b)
        Alternative_Empty _ -> a

qualifiers :: OperatorTable -> Qualifiers -> Qualifiers
qualifiers opTable qs = map (qualifier opTable) qs

qualifier :: OperatorTable -> Qualifier -> Qualifier
qualifier opTable q =
    case q of
        Qualifier_Empty _ -> q
        Qualifier_Generator r p e -> 
            Qualifier_Generator r (pattern opTable p) (expression opTable e)
        Qualifier_Guard r e ->
            Qualifier_Guard r (expression opTable e)
        Qualifier_Let r ds ->
            Qualifier_Let r (declarations opTable ds)

statements :: OperatorTable -> Statements -> Statements
statements opTable ss = map (statement opTable) ss

statement :: OperatorTable -> Statement -> Statement
statement opTable s =
    case s of
        Statement_Empty _ -> s
        Statement_Expression r e ->
            Statement_Expression r (expression opTable e)
        Statement_Generator r p e -> 
            Statement_Generator r (pattern opTable p) (expression opTable e)
        Statement_Let r ds ->
            Statement_Let r (declarations opTable ds)

maybeExpression :: OperatorTable -> MaybeExpression -> MaybeExpression          
maybeExpression opTable me =
    case me of
        MaybeExpression_Just e -> MaybeExpression_Just (expression opTable e)
        MaybeExpression_Nothing -> me

expressions :: OperatorTable -> Expressions -> Expressions
expressions opTable es = map (expression opTable) es
        
-- </BORING>

pattern :: OperatorTable -> Pattern -> Pattern
pattern opTable p = 
    case p of
        Pattern_List r ps -> 
            case r of
                Range_Range Position_Unknown Position_Unknown -> 
                    resolvePattern opTable (patterns opTable ps)
                _ -> Pattern_List r (patterns opTable ps)

        -- <BORING> 
        Pattern_As r n p -> Pattern_As r n (pattern opTable p)
        Pattern_Constructor r n ps -> Pattern_Constructor r n (patterns opTable ps)
        Pattern_Parenthesized r p -> Pattern_Parenthesized r (pattern opTable p)
        Pattern_Tuple r ps -> Pattern_Tuple r (patterns opTable ps)

        Pattern_Literal _ _ -> p
        Pattern_Variable _ _ -> p
        Pattern_Wildcard _ -> p
        -- </BORING>

        Pattern_Record _ _ _ -> internalError "ResolveOperators" "pattern" "Record"
        Pattern_Successor _ _ _ -> internalError "ResolveOperators" "pattern" "Successor"
        Pattern_InfixConstructor _ _ _ _ -> internalError "ResolveOperators" "pattern" "InfixConstructor"
        Pattern_Negate _ _ -> internalError "ResolveOperators" "pattern" "Negate"
        Pattern_Irrefutable _ _ -> internalError "ResolveOperators" "pattern" "Irrefutable"

expression :: OperatorTable -> Expression -> Expression
expression opTable e = 
    case e of
        Expression_List r es ->
            case r of
                Range_Range Position_Unknown Position_Unknown -> 
                    resolveExpression opTable (expressions opTable es)
                _ -> Expression_List r (expressions opTable es)
 
        -- <BORING> 
        Expression_Case r e as -> Expression_Case r (expression opTable e) (alternatives opTable as)
        Expression_Comprehension r e qs -> Expression_Comprehension r (expression opTable e) (qualifiers opTable qs)
        Expression_Do r ss -> Expression_Do r (statements opTable ss)
        Expression_Enum r e me1 me2 -> 
            Expression_Enum r (expression opTable e) (maybeExpression opTable me1) (maybeExpression opTable me2)
        Expression_If r e1 e2 e3 -> Expression_If r (expression opTable e1) (expression opTable e2) (expression opTable e3)   
        Expression_InfixApplication r me1 e me2 ->
            Expression_InfixApplication r (maybeExpression opTable me1) (expression opTable e) (maybeExpression opTable me2)
        Expression_Lambda r ps e -> Expression_Lambda r (patterns opTable ps) (expression opTable e)
        Expression_Let r ds e -> Expression_Let r (declarations opTable ds) (expression opTable e)
        Expression_Negate r e -> Expression_Negate r (expression opTable e)
        Expression_NormalApplication r e es -> 
            Expression_NormalApplication r (expression opTable e) (expressions opTable es)
        Expression_Parenthesized r e -> Expression_Parenthesized r (expression opTable e)
        Expression_Tuple r es -> Expression_Tuple r (expressions opTable es)
        Expression_Typed r e t -> Expression_Typed r (expression opTable e) t

        Expression_Constructor _ _ -> e
        Expression_Literal _ _ -> e
        Expression_Variable _ _ -> e
        -- </BORING>
        
        Expression_RecordConstruction _ _ _ -> internalError "ResolveOperators" "expression" "RecordConstruction"
        Expression_RecordUpdate _ _ _ -> internalError "ResolveOperators" "expression" "RecordUpdate"       
            
type State expr = 
    ( [Name] -- operator stack
    , [expr] -- expression/pattern stack
    )

resolveExpression :: OperatorTable -> [Expression] -> Expression
resolveExpression opTable es = resolve opTable es (getOp, applyMinus, applyBinary) ([], []) 
  where
    getOp (Expression_Variable (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp (Expression_Constructor (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp _ = Nothing
    
    applyMinus :: Name -> Expression -> Expression
    applyMinus n e
        | getNameName n == intUnaryMinusName =
            Expression_Negate      (mergeRanges (getNameRange n) (getExprRange e)) e
        | getNameName n == floatUnaryMinusName = 
            Expression_NegateFloat (mergeRanges (getNameRange n) (getExprRange e)) e
        | otherwise = internalError 
            "ResolveOperators.hs" "resolveExpression.applyMinus" "unknown unary operator"        
            
    applyBinary :: Name -> Expression -> Expression -> Expression
    applyBinary n e1 e2 =
        Expression_InfixApplication 
            (mergeRanges (getExprRange e1) (getExprRange e2)) 
            (MaybeExpression_Just e1) 
            ((if isConOp n then Expression_Constructor else Expression_Variable) (getNameRange n) n)
            (MaybeExpression_Just e2)

    isConOp n = isUpper firstLetter || firstLetter == ':'
      where
        firstLetter = head (getNameName n)
        
resolvePattern :: OperatorTable -> [Pattern] -> Pattern
resolvePattern opTable ps = resolve opTable ps (getOp, applyMinus, applyBinary) ([], []) 
  where
    getOp (Pattern_Variable (Range_Range Position_Unknown Position_Unknown) n) = Just n
    getOp _ = Nothing
    
    applyMinus :: Name -> Pattern -> Pattern
    applyMinus n p@(Pattern_Literal r l) 
        | getNameName n == intUnaryMinusName =
            Pattern_Negate (mergeRanges (getNameRange n) r) l
        | getNameName n == floatUnaryMinusName = 
            Pattern_NegateFloat (mergeRanges (getNameRange n) r) l            
        | otherwise = internalError 
                "ResolveOperators.hs" "resolvePattern.applyMinus" "unknown unary operator"        
    applyMinus n _ =
        internalError "ResolveOperators" "resolvePattern" "in patterns unary minus is only allowed in front of literals" 
        
        -- !!!
        
        
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
    -> State expr -> expr
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
    popOp (op:ops, exprs) 
        | getNameName op == intUnaryMinusName || getNameName op == floatUnaryMinusName =
            case exprs of
                (expr:rest) -> (ops, applyMinus op expr : rest)
                _ -> internalError "ResolveOperators" "popOp" "1"
        | otherwise =
            case exprs of
                (expr2:expr1:rest) -> (ops, applyBinary op expr1 expr2 : rest)
                _ -> internalError "ResolveOperators" "popOp" "2"
--    pushOp :: Name -> State expr -> State expr
    pushOp opTable op state@(top:ops, exprs) =
        if strongerOp opTable top op then
            pushOp opTable op (popOp state)
        else
            (op:top:ops, exprs)
    pushOp _ op ([], exprs) =
        ([op], exprs)
--    cleanup :: State expr -> expr
    cleanup state@(_:_, _)    = cleanup (popOp state)
    cleanup state@(_, [expr]) = expr
    cleanup _ = internalError "ResolveOperators" "cleanup" "invalid state"
    

pushExpr :: expr -> State expr -> State expr
pushExpr expr (ops, exprs) =
    (ops, expr:exprs)
                
strongerOp :: OperatorTable -> Name -> Name -> Bool
strongerOp opTable op1 op2
    | isBinary op1 && isBinary op2 =
        if prio1 == prio2 then
            if assoc1 == AssocLeft && assoc2 == AssocLeft then
                True
            else if assoc1 == AssocRight && assoc2 == AssocRight then
                False
            else
                let {
                    assocString AssocRight = "right-associative";
                    assocString AssocLeft  = "left-associative";
                    assocString AssocNone  = "non-associative";
                    
                    message =
                            "ambiguous use of "
                        ++  assocString (assoc1)
                        ++  " operator "
                        ++  getNameName op1
                        ++  " at " ++ showPosition (getRangeStart (getNameRange op1))
                        ++  " with "
                        ++  assocString (assoc2)
                        ++  " operator "
                        ++  getNameName op2
                        ++  " at " ++ showPosition (getRangeStart (getNameRange op2))
                        ;
                }
                in
                    error message -- !!!
        else
            prio1 > prio2
    | isUnary  op1 && isBinary op2 = prio1 >= prio2
    | isUnary  op2 = False
    | otherwise = internalError "ResolveOperators" "strongerOp" "unable to determine which operator binds stronger"
  where
    assoc1 = assoc opTable op1
    assoc2 = assoc opTable op2
    prio1 = prio opTable op1
    prio2 = prio opTable op2

showPosition :: Position -> String
showPosition p =
    case p of
        Position_Position _ row col -> "(" ++ show row ++ "," ++ show col ++ ")"
        Position_Unknown -> "(unknown position)"
        
isUnary :: Name -> Bool
isUnary name = getNameName name `elem` [ intUnaryMinusName, floatUnaryMinusName ]

isBinary :: Name -> Bool
isBinary = not . isUnary
