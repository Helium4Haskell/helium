

-- UUAGC 0.9.42.2 (Helium/Syntax/UHA_Syntax.ag)
module Helium.Syntax.UHA_Syntax where
-- Alternative -------------------------------------------------
data Alternative = Alternative_Hole (Range) (Integer)
                 | Alternative_Feedback (Range) (String) (Alternative)
                 | Alternative_Alternative (Range) (Pattern) (RightHandSide)
                 | Alternative_Empty (Range)
-- Alternatives ------------------------------------------------
type Alternatives = [Alternative]
-- AnnotatedType -----------------------------------------------
data AnnotatedType = AnnotatedType_AnnotatedType (Range) (Bool) (Type)
-- AnnotatedTypes ----------------------------------------------
type AnnotatedTypes = [AnnotatedType]
-- Body --------------------------------------------------------
data Body = Body_Hole (Range) (Integer)
          | Body_Body (Range) (ImportDeclarations) (Declarations)
-- Constructor -------------------------------------------------
data Constructor = Constructor_Constructor (Range) (Name) (AnnotatedTypes)
                 | Constructor_Infix (Range) (AnnotatedType) (Name) (AnnotatedType)
                 | Constructor_Record (Range) (Name) (FieldDeclarations)
-- Constructors ------------------------------------------------
type Constructors = [Constructor]
-- ContextItem -------------------------------------------------
data ContextItem = ContextItem_ContextItem (Range) (Name) (Types)
-- ContextItems ------------------------------------------------
type ContextItems = [ContextItem]
-- Declaration -------------------------------------------------
data Declaration = Declaration_Hole (Range) (Integer)
                 | Declaration_Type (Range) (SimpleType) (Type)
                 | Declaration_Data (Range) (ContextItems) (SimpleType) (Constructors) (Names)
                 | Declaration_Newtype (Range) (ContextItems) (SimpleType) (Constructor) (Names)
                 | Declaration_Class (Range) (ContextItems) (SimpleType) (MaybeDeclarations)
                 | Declaration_Instance (Range) (ContextItems) (Name) (Types) (MaybeDeclarations)
                 | Declaration_Default (Range) (Types)
                 | Declaration_FunctionBindings (Range) (FunctionBindings)
                 | Declaration_PatternBinding (Range) (Pattern) (RightHandSide)
                 | Declaration_TypeSignature (Range) (Names) (Type)
                 | Declaration_Fixity (Range) (Fixity) (MaybeInt) (Names)
                 | Declaration_Empty (Range)
-- Declarations ------------------------------------------------
type Declarations = [Declaration]
-- Export ------------------------------------------------------
data Export = Export_Variable (Range) (Name)
            | Export_TypeOrClass (Range) (Name) (MaybeNames)
            | Export_TypeOrClassComplete (Range) (Name)
            | Export_Module (Range) (Name)
-- Exports -----------------------------------------------------
type Exports = [Export]
-- Expression --------------------------------------------------
data Expression = Expression_Hole (Range) (Integer)
                | Expression_Feedback (Range) (String) (Expression)
                | Expression_MustUse (Range) (Expression)
                | Expression_Literal (Range) (Literal)
                | Expression_Variable (Range) (Name)
                | Expression_Constructor (Range) (Name)
                | Expression_Parenthesized (Range) (Expression)
                | Expression_NormalApplication (Range) (Expression) (Expressions)
                | Expression_InfixApplication (Range) (MaybeExpression) (Expression) (MaybeExpression)
                | Expression_If (Range) (Expression) (Expression) (Expression)
                | Expression_Lambda (Range) (Patterns) (Expression)
                | Expression_Case (Range) (Expression) (Alternatives)
                | Expression_Let (Range) (Declarations) (Expression)
                | Expression_Do (Range) (Statements)
                | Expression_List (Range) (Expressions)
                | Expression_Tuple (Range) (Expressions)
                | Expression_Comprehension (Range) (Expression) (Qualifiers)
                | Expression_Typed (Range) (Expression) (Type)
                | Expression_RecordConstruction (Range) (Name) (RecordExpressionBindings)
                | Expression_RecordUpdate (Range) (Expression) (RecordExpressionBindings)
                | Expression_Enum (Range) (Expression) (MaybeExpression) (MaybeExpression)
                | Expression_Negate (Range) (Expression)
                | Expression_NegateFloat (Range) (Expression)
-- Expressions -------------------------------------------------
type Expressions = [Expression]
-- FieldDeclaration --------------------------------------------
data FieldDeclaration = FieldDeclaration_FieldDeclaration (Range) (Names) (AnnotatedType)
-- FieldDeclarations -------------------------------------------
type FieldDeclarations = [FieldDeclaration]
-- Fixity ------------------------------------------------------
data Fixity = Fixity_Infixl (Range)
            | Fixity_Infixr (Range)
            | Fixity_Infix (Range)
-- FunctionBinding ---------------------------------------------
data FunctionBinding = FunctionBinding_Hole (Range) (Integer)
                     | FunctionBinding_Feedback (Range) (String) (FunctionBinding)
                     | FunctionBinding_FunctionBinding (Range) (LeftHandSide) (RightHandSide)
-- FunctionBindings --------------------------------------------
type FunctionBindings = [FunctionBinding]
-- GuardedExpression -------------------------------------------
data GuardedExpression = GuardedExpression_GuardedExpression (Range) (Expression) (Expression)
-- GuardedExpressions ------------------------------------------
type GuardedExpressions = [GuardedExpression]
-- Import ------------------------------------------------------
data Import = Import_Variable (Range) (Name)
            | Import_TypeOrClass (Range) (Name) (MaybeNames)
            | Import_TypeOrClassComplete (Range) (Name)
-- ImportDeclaration -------------------------------------------
data ImportDeclaration = ImportDeclaration_Import (Range) (Bool) (Name) (MaybeName) (MaybeImportSpecification)
                       | ImportDeclaration_Empty (Range)
-- ImportDeclarations ------------------------------------------
type ImportDeclarations = [ImportDeclaration]
-- ImportSpecification -----------------------------------------
data ImportSpecification = ImportSpecification_Import (Range) (Bool) (Imports)
-- Imports -----------------------------------------------------
type Imports = [Import]
-- LeftHandSide ------------------------------------------------
data LeftHandSide = LeftHandSide_Function (Range) (Name) (Patterns)
                  | LeftHandSide_Infix (Range) (Pattern) (Name) (Pattern)
                  | LeftHandSide_Parenthesized (Range) (LeftHandSide) (Patterns)
-- Literal -----------------------------------------------------
data Literal = Literal_Int (Range) (String)
             | Literal_Char (Range) (String)
             | Literal_Float (Range) (String)
             | Literal_String (Range) (String)
-- MaybeDeclarations -------------------------------------------
data MaybeDeclarations = MaybeDeclarations_Nothing
                       | MaybeDeclarations_Just (Declarations)
-- MaybeExports ------------------------------------------------
data MaybeExports = MaybeExports_Nothing
                  | MaybeExports_Just (Exports)
-- MaybeExpression ---------------------------------------------
data MaybeExpression = MaybeExpression_Nothing
                     | MaybeExpression_Just (Expression)
-- MaybeImportSpecification ------------------------------------
data MaybeImportSpecification = MaybeImportSpecification_Nothing
                              | MaybeImportSpecification_Just (ImportSpecification)
-- MaybeInt ----------------------------------------------------
data MaybeInt = MaybeInt_Nothing
              | MaybeInt_Just (Int)
-- MaybeName ---------------------------------------------------
data MaybeName = MaybeName_Nothing
               | MaybeName_Just (Name)
-- MaybeNames --------------------------------------------------
data MaybeNames = MaybeNames_Nothing
                | MaybeNames_Just (Names)
-- Module ------------------------------------------------------
data Module = Module_Module (Range) (MaybeName) (MaybeExports) (Body)
-- Name --------------------------------------------------------
data Name = Name_Identifier (Range) (Strings) (String)
          | Name_Operator (Range) (Strings) (String)
          | Name_Special (Range) (Strings) (String)
-- Names -------------------------------------------------------
type Names = [Name]
-- Pattern -----------------------------------------------------
data Pattern = Pattern_Hole (Range) (Integer)
             | Pattern_Literal (Range) (Literal)
             | Pattern_Variable (Range) (Name)
             | Pattern_Constructor (Range) (Name) (Patterns)
             | Pattern_Parenthesized (Range) (Pattern)
             | Pattern_InfixConstructor (Range) (Pattern) (Name) (Pattern)
             | Pattern_List (Range) (Patterns)
             | Pattern_Tuple (Range) (Patterns)
             | Pattern_Record (Range) (Name) (RecordPatternBindings)
             | Pattern_Negate (Range) (Literal)
             | Pattern_As (Range) (Name) (Pattern)
             | Pattern_Wildcard (Range)
             | Pattern_Irrefutable (Range) (Pattern)
             | Pattern_Successor (Range) (Name) (Literal)
             | Pattern_NegateFloat (Range) (Literal)
-- Patterns ----------------------------------------------------
type Patterns = [Pattern]
-- Position ----------------------------------------------------
data Position = Position_Position (String) (Int) (Int)
              | Position_Unknown
-- Qualifier ---------------------------------------------------
data Qualifier = Qualifier_Guard (Range) (Expression)
               | Qualifier_Let (Range) (Declarations)
               | Qualifier_Generator (Range) (Pattern) (Expression)
               | Qualifier_Empty (Range)
-- Qualifiers --------------------------------------------------
type Qualifiers = [Qualifier]
-- Range -------------------------------------------------------
data Range = Range_Range (Position) (Position)
-- RecordExpressionBinding -------------------------------------
data RecordExpressionBinding = RecordExpressionBinding_RecordExpressionBinding (Range) (Name) (Expression)
-- RecordExpressionBindings ------------------------------------
type RecordExpressionBindings = [RecordExpressionBinding]
-- RecordPatternBinding ----------------------------------------
data RecordPatternBinding = RecordPatternBinding_RecordPatternBinding (Range) (Name) (Pattern)
-- RecordPatternBindings ---------------------------------------
type RecordPatternBindings = [RecordPatternBinding]
-- RightHandSide -----------------------------------------------
data RightHandSide = RightHandSide_Expression (Range) (Expression) (MaybeDeclarations)
                   | RightHandSide_Guarded (Range) (GuardedExpressions) (MaybeDeclarations)
-- SimpleType --------------------------------------------------
data SimpleType = SimpleType_SimpleType (Range) (Name) (Names)
-- Statement ---------------------------------------------------
data Statement = Statement_Expression (Range) (Expression)
               | Statement_Let (Range) (Declarations)
               | Statement_Generator (Range) (Pattern) (Expression)
               | Statement_Empty (Range)
-- Statements --------------------------------------------------
type Statements = [Statement]
-- Strings -----------------------------------------------------
type Strings = [(String)]
-- Type --------------------------------------------------------
data Type = Type_Application (Range) (Bool) (Type) (Types)
          | Type_Variable (Range) (Name)
          | Type_Constructor (Range) (Name)
          | Type_Qualified (Range) (ContextItems) (Type)
          | Type_Forall (Range) (Names) (Type)
          | Type_Exists (Range) (Names) (Type)
          | Type_Parenthesized (Range) (Type)
-- Types -------------------------------------------------------
type Types = [Type]