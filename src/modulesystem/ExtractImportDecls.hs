
-- UUAGC 0.9.5 (ExtractImportDecls.ag)
module ExtractImportDecls where

import UHA_Syntax
import UHA_Utils
import Lvm.Common.Id
import qualified Lvm.Core.Data as Core
import Utils (internalError)
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside )  =
    (sem_Alternative_Alternative (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Alternative (Alternative_Empty _range )  =
    (sem_Alternative_Empty (sem_Range _range ) )
-- semantic domain
type T_Alternative = ( Alternative)
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_  =
    (let _lhsOself :: Alternative
         _rangeIself :: Range
         _patternIself :: Pattern
         _righthandsideIself :: RightHandSide
         _self =
             Alternative_Alternative _rangeIself _patternIself _righthandsideIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
         ( _righthandsideIself) =
             (righthandside_ )
     in  ( _lhsOself))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_  =
    (let _lhsOself :: Alternative
         _rangeIself :: Range
         _self =
             Alternative_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list  =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list) )
-- semantic domain
type T_Alternatives = ( Alternatives)
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_  =
    (let _lhsOself :: Alternatives
         _hdIself :: Alternative
         _tlIself :: Alternatives
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil  =
    (let _lhsOself :: Alternatives
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
type T_Body = ( ( [(Core.CoreDecl,[Id])] ),Body)
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_  =
    (let _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _lhsOself :: Body
         _rangeIself :: Range
         _importdeclarationsIcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _importdeclarationsIself :: ImportDeclarations
         _declarationsIself :: Declarations
         _lhsOcoreImportDecls =
             _importdeclarationsIcoreImportDecls
         _self =
             Body_Body _rangeIself _importdeclarationsIself _declarationsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _importdeclarationsIcoreImportDecls,_importdeclarationsIself) =
             (importdeclarations_ )
         ( _declarationsIself) =
             (declarations_ )
     in  ( _lhsOcoreImportDecls,_lhsOself))
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
type T_Declaration = ( Declaration)
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _contextIself :: ContextItems
         _simpletypeIself :: SimpleType
         _whereIself :: MaybeDeclarations
         _self =
             Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _simpletypeIself) =
             (simpletype_ )
         ( _whereIself) =
             (where_ )
     in  ( _lhsOself))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _contextIself :: ContextItems
         _simpletypeIself :: SimpleType
         _constructorsIself :: Constructors
         _derivingsInames :: ([Name])
         _derivingsIself :: Names
         _self =
             Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _simpletypeIself) =
             (simpletype_ )
         ( _constructorsIself) =
             (constructors_ )
         ( _derivingsInames,_derivingsIself) =
             (derivings_ )
     in  ( _lhsOself))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _typesIself :: Types
         _self =
             Declaration_Default _rangeIself _typesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typesIself) =
             (types_ )
     in  ( _lhsOself))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _self =
             Declaration_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _fixityIself :: Fixity
         _priorityIself :: MaybeInt
         _operatorsInames :: ([Name])
         _operatorsIself :: Names
         _self =
             Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _fixityIself) =
             (fixity_ )
         ( _priorityIself) =
             (priority_ )
         ( _operatorsInames,_operatorsIself) =
             (operators_ )
     in  ( _lhsOself))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _bindingsIname :: Name
         _bindingsIself :: FunctionBindings
         _self =
             Declaration_FunctionBindings _rangeIself _bindingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _bindingsIname,_bindingsIself) =
             (bindings_ )
     in  ( _lhsOself))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _contextIself :: ContextItems
         _nameIself :: Name
         _typesIself :: Types
         _whereIself :: MaybeDeclarations
         _self =
             Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _nameIself) =
             (name_ )
         ( _typesIself) =
             (types_ )
         ( _whereIself) =
             (where_ )
     in  ( _lhsOself))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _contextIself :: ContextItems
         _simpletypeIself :: SimpleType
         _constructorIself :: Constructor
         _derivingsInames :: ([Name])
         _derivingsIself :: Names
         _self =
             Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _simpletypeIself) =
             (simpletype_ )
         ( _constructorIself) =
             (constructor_ )
         ( _derivingsInames,_derivingsIself) =
             (derivings_ )
     in  ( _lhsOself))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _patternIself :: Pattern
         _righthandsideIself :: RightHandSide
         _self =
             Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
         ( _righthandsideIself) =
             (righthandside_ )
     in  ( _lhsOself))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _simpletypeIself :: SimpleType
         _typeIself :: Type
         _self =
             Declaration_Type _rangeIself _simpletypeIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _simpletypeIself) =
             (simpletype_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_  =
    (let _lhsOself :: Declaration
         _rangeIself :: Range
         _namesInames :: ([Name])
         _namesIself :: Names
         _typeIself :: Type
         _self =
             Declaration_TypeSignature _rangeIself _namesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _namesInames,_namesIself) =
             (names_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list  =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list) )
-- semantic domain
type T_Declarations = ( Declarations)
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_  =
    (let _lhsOself :: Declarations
         _hdIself :: Declaration
         _tlIself :: Declarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil  =
    (let _lhsOself :: Declarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
         _namesInames :: ( Maybe [Name] )
         _namesIself :: MaybeNames
         _self =
             Export_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesInames,_namesIself) =
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
type T_Expression = ( Expression)
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _alternativesIself :: Alternatives
         _self =
             Expression_Case _rangeIself _expressionIself _alternativesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
         ( _alternativesIself) =
             (alternatives_ )
     in  ( _lhsOself))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _qualifiersIself :: Qualifiers
         _self =
             Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
         ( _qualifiersIself) =
             (qualifiers_ )
     in  ( _lhsOself))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Expression_Constructor _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _statementsIself :: Statements
         _self =
             Expression_Do _rangeIself _statementsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _statementsIself) =
             (statements_ )
     in  ( _lhsOself))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _fromIself :: Expression
         _thenIself :: MaybeExpression
         _toIself :: MaybeExpression
         _self =
             Expression_Enum _rangeIself _fromIself _thenIself _toIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _fromIself) =
             (from_ )
         ( _thenIself) =
             (then_ )
         ( _toIself) =
             (to_ )
     in  ( _lhsOself))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _guardExpressionIself :: Expression
         _thenExpressionIself :: Expression
         _elseExpressionIself :: Expression
         _self =
             Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _guardExpressionIself) =
             (guardExpression_ )
         ( _thenExpressionIself) =
             (thenExpression_ )
         ( _elseExpressionIself) =
             (elseExpression_ )
     in  ( _lhsOself))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _leftExpressionIself :: MaybeExpression
         _operatorIself :: Expression
         _rightExpressionIself :: MaybeExpression
         _self =
             Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftExpressionIself) =
             (leftExpression_ )
         ( _operatorIself) =
             (operator_ )
         ( _rightExpressionIself) =
             (rightExpression_ )
     in  ( _lhsOself))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _patternsIself :: Patterns
         _expressionIself :: Expression
         _self =
             Expression_Lambda _rangeIself _patternsIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternsIself) =
             (patterns_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _declarationsIself :: Declarations
         _expressionIself :: Expression
         _self =
             Expression_Let _rangeIself _declarationsIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _declarationsIself) =
             (declarations_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionsIself :: Expressions
         _self =
             Expression_List _rangeIself _expressionsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionsIself) =
             (expressions_ )
     in  ( _lhsOself))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Expression_Literal _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIself) =
             (literal_ )
     in  ( _lhsOself))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _self =
             Expression_Negate _rangeIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _self =
             Expression_NegateFloat _rangeIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _functionIself :: Expression
         _argumentsIself :: Expressions
         _self =
             Expression_NormalApplication _rangeIself _functionIself _argumentsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _functionIself) =
             (function_ )
         ( _argumentsIself) =
             (arguments_ )
     in  ( _lhsOself))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _self =
             Expression_Parenthesized _rangeIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _nameIself :: Name
         _recordExpressionBindingsIself :: RecordExpressionBindings
         _self =
             Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _recordExpressionBindingsIself) =
             (recordExpressionBindings_ )
     in  ( _lhsOself))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _recordExpressionBindingsIself :: RecordExpressionBindings
         _self =
             Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
         ( _recordExpressionBindingsIself) =
             (recordExpressionBindings_ )
     in  ( _lhsOself))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionsIself :: Expressions
         _self =
             Expression_Tuple _rangeIself _expressionsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionsIself) =
             (expressions_ )
     in  ( _lhsOself))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _expressionIself :: Expression
         _typeIself :: Type
         _self =
             Expression_Typed _rangeIself _expressionIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_  =
    (let _lhsOself :: Expression
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Expression_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list  =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list) )
-- semantic domain
type T_Expressions = ( Expressions)
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_  =
    (let _lhsOself :: Expressions
         _hdIself :: Expression
         _tlIself :: Expressions
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil  =
    (let _lhsOself :: Expressions
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
         _namesInames :: ([Name])
         _namesIself :: Names
         _typeIself :: AnnotatedType
         _self =
             FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _namesInames,_namesIself) =
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
type T_FunctionBinding = ( Name,FunctionBinding)
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_  =
    (let _lhsOself :: FunctionBinding
         _lhsOname :: Name
         _rangeIself :: Range
         _lefthandsideIname :: Name
         _lefthandsideIself :: LeftHandSide
         _righthandsideIself :: RightHandSide
         _self =
             FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
         _lhsOself =
             _self
         _lhsOname =
             _lefthandsideIname
         ( _rangeIself) =
             (range_ )
         ( _lefthandsideIname,_lefthandsideIself) =
             (lefthandside_ )
         ( _righthandsideIself) =
             (righthandside_ )
     in  ( _lhsOname,_lhsOself))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list  =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list) )
-- semantic domain
type T_FunctionBindings = ( Name,FunctionBindings)
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_  =
    (let _lhsOname :: Name
         _lhsOself :: FunctionBindings
         _hdIname :: Name
         _hdIself :: FunctionBinding
         _tlIname :: Name
         _tlIself :: FunctionBindings
         _lhsOname =
             _hdIname
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIname,_hdIself) =
             (hd_ )
         ( _tlIname,_tlIself) =
             (tl_ )
     in  ( _lhsOname,_lhsOself))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil  =
    (let _lhsOname :: Name
         _lhsOself :: FunctionBindings
         _lhsOname =
             internalError "ToCoreName.ag" "n/a" "empty FunctionBindings"
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOname,_lhsOself))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression )  =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range ) (sem_Expression _guard ) (sem_Expression _expression ) )
-- semantic domain
type T_GuardedExpression = ( GuardedExpression)
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_  =
    (let _lhsOself :: GuardedExpression
         _rangeIself :: Range
         _guardIself :: Expression
         _expressionIself :: Expression
         _self =
             GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _guardIself) =
             (guard_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list  =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list) )
-- semantic domain
type T_GuardedExpressions = ( GuardedExpressions)
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_  =
    (let _lhsOself :: GuardedExpressions
         _hdIself :: GuardedExpression
         _tlIself :: GuardedExpressions
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil  =
    (let _lhsOself :: GuardedExpressions
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
type T_Import = ( ([Id]),Import)
sem_Import_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Import
sem_Import_TypeOrClass range_ name_ names_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _namesInames :: ( Maybe [Name] )
         _namesIself :: MaybeNames
         _lhsOimps =
             internalError "ExtractImportDecls.ag" "ImportSpecification.Import" "only variables can be hidden"
         _self =
             Import_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesInames,_namesIself) =
             (names_ )
     in  ( _lhsOimps,_lhsOself))
sem_Import_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Import
sem_Import_TypeOrClassComplete range_ name_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOimps =
             internalError "ExtractImportDecls.ag" "ImportSpecification.Import" "only variables can be hidden"
         _self =
             Import_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOimps,_lhsOself))
sem_Import_Variable :: T_Range ->
                       T_Name ->
                       T_Import
sem_Import_Variable range_ name_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOimps =
             [idFromName _nameIself]
         _self =
             Import_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOimps,_lhsOself))
-- ImportDeclaration -------------------------------------------
-- cata
sem_ImportDeclaration :: ImportDeclaration ->
                         T_ImportDeclaration
sem_ImportDeclaration (ImportDeclaration_Empty _range )  =
    (sem_ImportDeclaration_Empty (sem_Range _range ) )
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification )  =
    (sem_ImportDeclaration_Import (sem_Range _range ) _qualified (sem_Name _name ) (sem_MaybeName _asname ) (sem_MaybeImportSpecification _importspecification ) )
-- semantic domain
type T_ImportDeclaration = ( ( [(Core.CoreDecl,[Id])] ),ImportDeclaration)
sem_ImportDeclaration_Empty :: T_Range ->
                               T_ImportDeclaration
sem_ImportDeclaration_Empty range_  =
    (let _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _lhsOcoreImportDecls =
             []
         _self =
             ImportDeclaration_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOcoreImportDecls,_lhsOself))
sem_ImportDeclaration_Import :: T_Range ->
                                Bool ->
                                T_Name ->
                                T_MaybeName ->
                                T_MaybeImportSpecification ->
                                T_ImportDeclaration
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_  =
    (let _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _nameIself :: Name
         _asnameIisNothing :: Bool
         _asnameIname :: ( Maybe Name )
         _asnameIself :: MaybeName
         _importspecificationIimps :: ([Id])
         _importspecificationIself :: MaybeImportSpecification
         _lhsOcoreImportDecls =
             [(_importDecls    ,_hidings    )]
         _importDecls =
             if qualified_ || not _asnameIisNothing then
                 internalError "ExtractImportDecls.ag" "ImportDeclaration.Import" "qualified and as-imports not supported yet"
             else
                 Core.DeclImport
                     { Core.declName = idFromName _nameIself
                     , Core.declAccess =
                         Core.Imported
                             { Core.accessPublic   = False
                             , Core.importModule   = idFromName _nameIself
                             , Core.importName     = dummyId
                             , Core.importKind     = Core.DeclKindModule
                             , Core.importMajorVer = 0
                             , Core.importMinorVer = 0
                             }
                     , Core.declCustoms = []
                     }
         _hidings =
             _importspecificationIimps
         _self =
             ImportDeclaration_Import _rangeIself qualified_ _nameIself _asnameIself _importspecificationIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _asnameIisNothing,_asnameIname,_asnameIself) =
             (asname_ )
         ( _importspecificationIimps,_importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOcoreImportDecls,_lhsOself))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations ->
                          T_ImportDeclarations
sem_ImportDeclarations list  =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list) )
-- semantic domain
type T_ImportDeclarations = ( ( [(Core.CoreDecl,[Id])] ),ImportDeclarations)
sem_ImportDeclarations_Cons :: T_ImportDeclaration ->
                               T_ImportDeclarations ->
                               T_ImportDeclarations
sem_ImportDeclarations_Cons hd_ tl_  =
    (let _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _lhsOself :: ImportDeclarations
         _hdIcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _hdIself :: ImportDeclaration
         _tlIcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _tlIself :: ImportDeclarations
         _lhsOcoreImportDecls =
             _hdIcoreImportDecls  ++  _tlIcoreImportDecls
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIcoreImportDecls,_hdIself) =
             (hd_ )
         ( _tlIcoreImportDecls,_tlIself) =
             (tl_ )
     in  ( _lhsOcoreImportDecls,_lhsOself))
sem_ImportDeclarations_Nil :: T_ImportDeclarations
sem_ImportDeclarations_Nil  =
    (let _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _lhsOself :: ImportDeclarations
         _lhsOcoreImportDecls =
             []
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOcoreImportDecls,_lhsOself))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification ->
                           T_ImportSpecification
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports )  =
    (sem_ImportSpecification_Import (sem_Range _range ) _hiding (sem_Imports _imports ) )
-- semantic domain
type T_ImportSpecification = ( ([Id]),ImportSpecification)
sem_ImportSpecification_Import :: T_Range ->
                                  Bool ->
                                  T_Imports ->
                                  T_ImportSpecification
sem_ImportSpecification_Import range_ hiding_ imports_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: ImportSpecification
         _rangeIself :: Range
         _importsIimps :: ([Id])
         _importsIself :: Imports
         _lhsOimps =
             if not hiding_ then
                 internalError "ExtractImportDecls.ag" "ImportSpecification.Import" "import lists are not supported"
             else
                 _importsIimps
         _self =
             ImportSpecification_Import _rangeIself hiding_ _importsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _importsIimps,_importsIself) =
             (imports_ )
     in  ( _lhsOimps,_lhsOself))
-- Imports -----------------------------------------------------
-- cata
sem_Imports :: Imports ->
               T_Imports
sem_Imports list  =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list) )
-- semantic domain
type T_Imports = ( ([Id]),Imports)
sem_Imports_Cons :: T_Import ->
                    T_Imports ->
                    T_Imports
sem_Imports_Cons hd_ tl_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: Imports
         _hdIimps :: ([Id])
         _hdIself :: Import
         _tlIimps :: ([Id])
         _tlIself :: Imports
         _lhsOimps =
             _hdIimps  ++  _tlIimps
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIimps,_hdIself) =
             (hd_ )
         ( _tlIimps,_tlIself) =
             (tl_ )
     in  ( _lhsOimps,_lhsOself))
sem_Imports_Nil :: T_Imports
sem_Imports_Nil  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: Imports
         _lhsOimps =
             []
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOimps,_lhsOself))
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
type T_LeftHandSide = ( Name,LeftHandSide)
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_  =
    (let _lhsOname :: Name
         _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIself :: Patterns
         _lhsOname =
             _nameIself
         _self =
             LeftHandSide_Function _rangeIself _nameIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternsIself) =
             (patterns_ )
     in  ( _lhsOname,_lhsOself))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_  =
    (let _lhsOname :: Name
         _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _operatorIself :: Name
         _rightPatternIself :: Pattern
         _lhsOname =
             _operatorIself
         _self =
             LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftPatternIself) =
             (leftPattern_ )
         ( _operatorIself) =
             (operator_ )
         ( _rightPatternIself) =
             (rightPattern_ )
     in  ( _lhsOname,_lhsOself))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_  =
    (let _lhsOself :: LeftHandSide
         _lhsOname :: Name
         _rangeIself :: Range
         _lefthandsideIname :: Name
         _lefthandsideIself :: LeftHandSide
         _patternsIself :: Patterns
         _self =
             LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
         _lhsOself =
             _self
         _lhsOname =
             _lefthandsideIname
         ( _rangeIself) =
             (range_ )
         ( _lefthandsideIname,_lefthandsideIself) =
             (lefthandside_ )
         ( _patternsIself) =
             (patterns_ )
     in  ( _lhsOname,_lhsOself))
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
type T_MaybeDeclarations = ( MaybeDeclarations)
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_  =
    (let _lhsOself :: MaybeDeclarations
         _declarationsIself :: Declarations
         _self =
             MaybeDeclarations_Just _declarationsIself
         _lhsOself =
             _self
         ( _declarationsIself) =
             (declarations_ )
     in  ( _lhsOself))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing  =
    (let _lhsOself :: MaybeDeclarations
         _self =
             MaybeDeclarations_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
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
type T_MaybeExpression = ( MaybeExpression)
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_  =
    (let _lhsOself :: MaybeExpression
         _expressionIself :: Expression
         _self =
             MaybeExpression_Just _expressionIself
         _lhsOself =
             _self
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing  =
    (let _lhsOself :: MaybeExpression
         _self =
             MaybeExpression_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification ->
                                T_MaybeImportSpecification
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification )  =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification ) )
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing )  =
    (sem_MaybeImportSpecification_Nothing )
-- semantic domain
type T_MaybeImportSpecification = ( ([Id]),MaybeImportSpecification)
sem_MaybeImportSpecification_Just :: T_ImportSpecification ->
                                     T_MaybeImportSpecification
sem_MaybeImportSpecification_Just importspecification_  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: MaybeImportSpecification
         _importspecificationIimps :: ([Id])
         _importspecificationIself :: ImportSpecification
         _lhsOimps =
             _importspecificationIimps
         _self =
             MaybeImportSpecification_Just _importspecificationIself
         _lhsOself =
             _self
         ( _importspecificationIimps,_importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOimps,_lhsOself))
sem_MaybeImportSpecification_Nothing :: T_MaybeImportSpecification
sem_MaybeImportSpecification_Nothing  =
    (let _lhsOimps :: ([Id])
         _lhsOself :: MaybeImportSpecification
         _lhsOimps =
             []
         _self =
             MaybeImportSpecification_Nothing
         _lhsOself =
             _self
     in  ( _lhsOimps,_lhsOself))
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
type T_MaybeName = ( Bool,( Maybe Name ),MaybeName)
sem_MaybeName_Just :: T_Name ->
                      T_MaybeName
sem_MaybeName_Just name_  =
    (let _lhsOisNothing :: Bool
         _lhsOname :: ( Maybe Name )
         _lhsOself :: MaybeName
         _nameIself :: Name
         _lhsOisNothing =
             False
         _lhsOname =
             Just _nameIself
         _self =
             MaybeName_Just _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             (name_ )
     in  ( _lhsOisNothing,_lhsOname,_lhsOself))
sem_MaybeName_Nothing :: T_MaybeName
sem_MaybeName_Nothing  =
    (let _lhsOisNothing :: Bool
         _lhsOname :: ( Maybe Name )
         _lhsOself :: MaybeName
         _lhsOisNothing =
             True
         _lhsOname =
             Nothing
         _self =
             MaybeName_Nothing
         _lhsOself =
             _self
     in  ( _lhsOisNothing,_lhsOname,_lhsOself))
-- MaybeNames --------------------------------------------------
-- cata
sem_MaybeNames :: MaybeNames ->
                  T_MaybeNames
sem_MaybeNames (MaybeNames_Just _names )  =
    (sem_MaybeNames_Just (sem_Names _names ) )
sem_MaybeNames (MaybeNames_Nothing )  =
    (sem_MaybeNames_Nothing )
-- semantic domain
type T_MaybeNames = ( ( Maybe [Name] ),MaybeNames)
sem_MaybeNames_Just :: T_Names ->
                       T_MaybeNames
sem_MaybeNames_Just names_  =
    (let _lhsOnames :: ( Maybe [Name] )
         _lhsOself :: MaybeNames
         _namesInames :: ([Name])
         _namesIself :: Names
         _lhsOnames =
             Just _namesInames
         _self =
             MaybeNames_Just _namesIself
         _lhsOself =
             _self
         ( _namesInames,_namesIself) =
             (names_ )
     in  ( _lhsOnames,_lhsOself))
sem_MaybeNames_Nothing :: T_MaybeNames
sem_MaybeNames_Nothing  =
    (let _lhsOnames :: ( Maybe [Name] )
         _lhsOself :: MaybeNames
         _lhsOnames =
             Nothing
         _self =
             MaybeNames_Nothing
         _lhsOself =
             _self
     in  ( _lhsOnames,_lhsOself))
-- Module ------------------------------------------------------
-- cata
sem_Module :: Module ->
              T_Module
sem_Module (Module_Module _range _name _exports _body )  =
    (sem_Module_Module (sem_Range _range ) (sem_MaybeName _name ) (sem_MaybeExports _exports ) (sem_Body _body ) )
-- semantic domain
type T_Module = ( ( [(Core.CoreDecl,[Id])] ),Module)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_  =
    (let _lhsOself :: Module
         _lhsOcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _rangeIself :: Range
         _nameIisNothing :: Bool
         _nameIname :: ( Maybe Name )
         _nameIself :: MaybeName
         _exportsIself :: MaybeExports
         _bodyIcoreImportDecls :: ( [(Core.CoreDecl,[Id])] )
         _bodyIself :: Body
         _self =
             Module_Module _rangeIself _nameIself _exportsIself _bodyIself
         _lhsOself =
             _self
         _lhsOcoreImportDecls =
             _bodyIcoreImportDecls
         ( _rangeIself) =
             (range_ )
         ( _nameIisNothing,_nameIname,_nameIself) =
             (name_ )
         ( _exportsIself) =
             (exports_ )
         ( _bodyIcoreImportDecls,_bodyIself) =
             (body_ )
     in  ( _lhsOcoreImportDecls,_lhsOself))
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
type T_Names = ( ([Name]),Names)
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_  =
    (let _lhsOnames :: ([Name])
         _lhsOself :: Names
         _hdIself :: Name
         _tlInames :: ([Name])
         _tlIself :: Names
         _lhsOnames =
             _hdIself : _tlInames
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlInames,_tlIself) =
             (tl_ )
     in  ( _lhsOnames,_lhsOself))
sem_Names_Nil :: T_Names
sem_Names_Nil  =
    (let _lhsOnames :: ([Name])
         _lhsOself :: Names
         _lhsOnames =
             []
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOnames,_lhsOself))
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
type T_Pattern = ( Pattern)
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternIself :: Pattern
         _self =
             Pattern_As _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternIself) =
             (pattern_ )
     in  ( _lhsOself))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIself :: Patterns
         _self =
             Pattern_Constructor _rangeIself _nameIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternsIself) =
             (patterns_ )
     in  ( _lhsOself))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _constructorOperatorIself :: Name
         _rightPatternIself :: Pattern
         _self =
             Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftPatternIself) =
             (leftPattern_ )
         ( _constructorOperatorIself) =
             (constructorOperator_ )
         ( _rightPatternIself) =
             (rightPattern_ )
     in  ( _lhsOself))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _self =
             Pattern_Irrefutable _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
     in  ( _lhsOself))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIself :: Patterns
         _self =
             Pattern_List _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternsIself) =
             (patterns_ )
     in  ( _lhsOself))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_Literal _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIself) =
             (literal_ )
     in  ( _lhsOself))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_Negate _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIself) =
             (literal_ )
     in  ( _lhsOself))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_NegateFloat _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIself) =
             (literal_ )
     in  ( _lhsOself))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _self =
             Pattern_Parenthesized _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
     in  ( _lhsOself))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _recordPatternBindingsIself :: RecordPatternBindings
         _self =
             Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _recordPatternBindingsIself) =
             (recordPatternBindings_ )
     in  ( _lhsOself))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _literalIself :: Literal
         _self =
             Pattern_Successor _rangeIself _nameIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _literalIself) =
             (literal_ )
     in  ( _lhsOself))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIself :: Patterns
         _self =
             Pattern_Tuple _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternsIself) =
             (patterns_ )
     in  ( _lhsOself))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Pattern_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_  =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _self =
             Pattern_Wildcard _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list  =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list) )
-- semantic domain
type T_Patterns = ( Patterns)
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_  =
    (let _lhsOself :: Patterns
         _hdIself :: Pattern
         _tlIself :: Patterns
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil  =
    (let _lhsOself :: Patterns
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
type T_Qualifier = ( Qualifier)
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_  =
    (let _lhsOself :: Qualifier
         _rangeIself :: Range
         _self =
             Qualifier_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_  =
    (let _lhsOself :: Qualifier
         _rangeIself :: Range
         _patternIself :: Pattern
         _expressionIself :: Expression
         _self =
             Qualifier_Generator _rangeIself _patternIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_  =
    (let _lhsOself :: Qualifier
         _rangeIself :: Range
         _guardIself :: Expression
         _self =
             Qualifier_Guard _rangeIself _guardIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _guardIself) =
             (guard_ )
     in  ( _lhsOself))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_  =
    (let _lhsOself :: Qualifier
         _rangeIself :: Range
         _declarationsIself :: Declarations
         _self =
             Qualifier_Let _rangeIself _declarationsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _declarationsIself) =
             (declarations_ )
     in  ( _lhsOself))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list  =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list) )
-- semantic domain
type T_Qualifiers = ( Qualifiers)
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_  =
    (let _lhsOself :: Qualifiers
         _hdIself :: Qualifier
         _tlIself :: Qualifiers
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil  =
    (let _lhsOself :: Qualifiers
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
type T_RecordExpressionBinding = ( RecordExpressionBinding)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_  =
    (let _lhsOself :: RecordExpressionBinding
         _rangeIself :: Range
         _nameIself :: Name
         _expressionIself :: Expression
         _self =
             RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list  =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list) )
-- semantic domain
type T_RecordExpressionBindings = ( RecordExpressionBindings)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_  =
    (let _lhsOself :: RecordExpressionBindings
         _hdIself :: RecordExpressionBinding
         _tlIself :: RecordExpressionBindings
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil  =
    (let _lhsOself :: RecordExpressionBindings
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding ->
                            T_RecordPatternBinding
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern )  =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
-- semantic domain
type T_RecordPatternBinding = ( RecordPatternBinding)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range ->
                                                 T_Name ->
                                                 T_Pattern ->
                                                 T_RecordPatternBinding
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_  =
    (let _lhsOself :: RecordPatternBinding
         _rangeIself :: Range
         _nameIself :: Name
         _patternIself :: Pattern
         _self =
             RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternIself) =
             (pattern_ )
     in  ( _lhsOself))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings ->
                             T_RecordPatternBindings
sem_RecordPatternBindings list  =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list) )
-- semantic domain
type T_RecordPatternBindings = ( RecordPatternBindings)
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding ->
                                  T_RecordPatternBindings ->
                                  T_RecordPatternBindings
sem_RecordPatternBindings_Cons hd_ tl_  =
    (let _lhsOself :: RecordPatternBindings
         _hdIself :: RecordPatternBinding
         _tlIself :: RecordPatternBindings
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings
sem_RecordPatternBindings_Nil  =
    (let _lhsOself :: RecordPatternBindings
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide ->
                     T_RightHandSide
sem_RightHandSide (RightHandSide_Expression _range _expression _where )  =
    (sem_RightHandSide_Expression (sem_Range _range ) (sem_Expression _expression ) (sem_MaybeDeclarations _where ) )
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where )  =
    (sem_RightHandSide_Guarded (sem_Range _range ) (sem_GuardedExpressions _guardedexpressions ) (sem_MaybeDeclarations _where ) )
-- semantic domain
type T_RightHandSide = ( RightHandSide)
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_  =
    (let _lhsOself :: RightHandSide
         _rangeIself :: Range
         _expressionIself :: Expression
         _whereIself :: MaybeDeclarations
         _self =
             RightHandSide_Expression _rangeIself _expressionIself _whereIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
         ( _whereIself) =
             (where_ )
     in  ( _lhsOself))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_  =
    (let _lhsOself :: RightHandSide
         _rangeIself :: Range
         _guardedexpressionsIself :: GuardedExpressions
         _whereIself :: MaybeDeclarations
         _self =
             RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _guardedexpressionsIself) =
             (guardedexpressions_ )
         ( _whereIself) =
             (where_ )
     in  ( _lhsOself))
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
         _typevariablesInames :: ([Name])
         _typevariablesIself :: Names
         _self =
             SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _typevariablesInames,_typevariablesIself) =
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
type T_Statement = ( Statement)
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_  =
    (let _lhsOself :: Statement
         _rangeIself :: Range
         _self =
             Statement_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_  =
    (let _lhsOself :: Statement
         _rangeIself :: Range
         _expressionIself :: Expression
         _self =
             Statement_Expression _rangeIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_  =
    (let _lhsOself :: Statement
         _rangeIself :: Range
         _patternIself :: Pattern
         _expressionIself :: Expression
         _self =
             Statement_Generator _rangeIself _patternIself _expressionIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself) =
             (pattern_ )
         ( _expressionIself) =
             (expression_ )
     in  ( _lhsOself))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_  =
    (let _lhsOself :: Statement
         _rangeIself :: Range
         _declarationsIself :: Declarations
         _self =
             Statement_Let _rangeIself _declarationsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _declarationsIself) =
             (declarations_ )
     in  ( _lhsOself))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list  =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list) )
-- semantic domain
type T_Statements = ( Statements)
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_  =
    (let _lhsOself :: Statements
         _hdIself :: Statement
         _tlIself :: Statements
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil  =
    (let _lhsOself :: Statements
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
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
         _typevariablesInames :: ([Name])
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Exists _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesInames,_typevariablesIself) =
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
         _typevariablesInames :: ([Name])
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Forall _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesInames,_typevariablesIself) =
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