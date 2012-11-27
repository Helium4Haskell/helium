

-- UUAGC 0.9.40.3 (Syntax/UHA_Pretty.ag)
module Syntax.UHA_Pretty where
{-# LINE 3 "Syntax/UHA_Pretty.ag" #-}

-- Below two imports are to avoid clashes of "list" as used by the AG system.
-- Effectively, only list from the imported library needs to be qualified.
import Text.PrettyPrint.Leijen hiding (list)
import qualified Text.PrettyPrint.Leijen as PPrint
import Data.Char
import Top.Types (isTupleConstructor)

import Syntax.UHA_Syntax
import Utils.Utils (internalError, hole)

{-# LINE 18 "Syntax/UHA_Pretty.hs" #-}
{-# LINE 16 "Syntax/UHA_Pretty.ag" #-}

intErr :: String -> String -> a
intErr = internalError "UHA_Pretty"

opt :: Maybe Doc -> Doc
opt = maybe empty id

parensIf, backQuotesIf :: Bool -> Doc -> Doc
parensIf     p  n  = if p then parens n else n
backQuotesIf p  n  = if p then text "`" <> n <> text "`" else n

parensIfList :: [Bool] -> [Doc] -> [Doc]
parensIfList ps ns = map (uncurry parensIf) (zip ps ns)

tupled1 :: [Doc] -> Doc
tupled1 []  = empty
tupled1 xs  = tupled xs

tupled2 :: [Doc] -> Doc
tupled2 []  = empty
tupled2 xs  = tupledUnit xs

tupledUnit :: [Doc] -> Doc
tupledUnit [x] = x
tupledUnit xs  = tupled xs

commas :: [Doc] -> Doc
commas docs =
    hcat (punctuate (comma <+> empty) docs)

utrechtList :: Doc -> Doc -> [Doc] -> Doc
utrechtList _     _   []     = empty
utrechtList start end (d:ds) =
    let utrechtList' []     = end
        utrechtList' (doc:docs) = comma <+> doc <$> utrechtList' docs
    in
        start <+> d <$> utrechtList' ds

{-# LINE 58 "Syntax/UHA_Pretty.hs" #-}
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside) =
    (sem_Alternative_Alternative (sem_Range _range) (sem_Pattern _pattern) (sem_RightHandSide _righthandside))
sem_Alternative (Alternative_Empty _range) =
    (sem_Alternative_Empty (sem_Range _range))
sem_Alternative (Alternative_Feedback _range _feedback _alternative) =
    (sem_Alternative_Feedback (sem_Range _range) _feedback (sem_Alternative _alternative))
sem_Alternative (Alternative_Hole _range _id) =
    (sem_Alternative_Hole (sem_Range _range) _id)
-- semantic domain
type T_Alternative = ( Doc)
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _righthandsideItext :: ( Doc        -> Doc  )
         _text =
             ({-# LINE 584 "Syntax/UHA_Pretty.ag" #-}
              _patternItext <$> indent 2 (_righthandsideItext (text "->"))
              {-# LINE 85 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 90 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
         ( _righthandsideItext) =
             righthandside_
     in  ( _lhsOtext))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 588 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 107 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 112 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Alternative_Feedback :: T_Range ->
                            String ->
                            T_Alternative ->
                            T_Alternative
sem_Alternative_Feedback range_ feedback_ alternative_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _alternativeItext :: Doc
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _alternativeItext
              {-# LINE 128 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _alternativeItext) =
             alternative_
     in  ( _lhsOtext))
sem_Alternative_Hole :: T_Range ->
                        Integer ->
                        T_Alternative
sem_Alternative_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 583 "Syntax/UHA_Pretty.ag" #-}
              text hole
              {-# LINE 144 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 149 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list))
-- semantic domain
type T_Alternatives = ( ( [       Doc ] ))
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 172 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 185 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- AnnotatedType -----------------------------------------------
-- cata
sem_AnnotatedType :: AnnotatedType ->
                     T_AnnotatedType
sem_AnnotatedType (AnnotatedType_AnnotatedType _range _strict _type) =
    (sem_AnnotatedType_AnnotatedType (sem_Range _range) _strict (sem_Type _type))
-- semantic domain
type T_AnnotatedType = ( Doc)
sem_AnnotatedType_AnnotatedType :: T_Range ->
                                   Bool ->
                                   T_Type ->
                                   T_AnnotatedType
sem_AnnotatedType_AnnotatedType range_ strict_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _typeItext :: Doc
         _text =
             ({-# LINE 431 "Syntax/UHA_Pretty.ag" #-}
              (if strict_ then (text "!" <+>) else id) _typeItext
              {-# LINE 207 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 212 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
-- AnnotatedTypes ----------------------------------------------
-- cata
sem_AnnotatedTypes :: AnnotatedTypes ->
                      T_AnnotatedTypes
sem_AnnotatedTypes list =
    (Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list))
-- semantic domain
type T_AnnotatedTypes = ( ( [       Doc ] ))
sem_AnnotatedTypes_Cons :: T_AnnotatedType ->
                           T_AnnotatedTypes ->
                           T_AnnotatedTypes
sem_AnnotatedTypes_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 237 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes
sem_AnnotatedTypes_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 250 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body ->
            T_Body
sem_Body (Body_Body _range _importdeclarations _declarations) =
    (sem_Body_Body (sem_Range _range) (sem_ImportDeclarations _importdeclarations) (sem_Declarations _declarations))
sem_Body (Body_Hole _range _id) =
    (sem_Body_Hole (sem_Range _range) _id)
-- semantic domain
type T_Body = ( Doc)
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _importdeclarationsItext :: ( [       Doc ] )
         _declarationsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 176 "Syntax/UHA_Pretty.ag" #-}
              vcat
                       (   _importdeclarationsItext
                       ++                        _declarationsItext
                       )
              {-# LINE 278 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 283 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _importdeclarationsItext) =
             importdeclarations_
         ( _declarationsItext) =
             declarations_
     in  ( _lhsOtext))
sem_Body_Hole :: T_Range ->
                 Integer ->
                 T_Body
sem_Body_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 175 "Syntax/UHA_Pretty.ag" #-}
              text hole
              {-# LINE 301 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 306 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- Constructor -------------------------------------------------
-- cata
sem_Constructor :: Constructor ->
                   T_Constructor
sem_Constructor (Constructor_Constructor _range _constructor _types) =
    (sem_Constructor_Constructor (sem_Range _range) (sem_Name _constructor) (sem_AnnotatedTypes _types))
sem_Constructor (Constructor_Infix _range _leftType _constructorOperator _rightType) =
    (sem_Constructor_Infix (sem_Range _range) (sem_AnnotatedType _leftType) (sem_Name _constructorOperator) (sem_AnnotatedType _rightType))
sem_Constructor (Constructor_Record _range _constructor _fieldDeclarations) =
    (sem_Constructor_Record (sem_Range _range) (sem_Name _constructor) (sem_FieldDeclarations _fieldDeclarations))
-- semantic domain
type T_Constructor = ( Doc)
sem_Constructor_Constructor :: T_Range ->
                               T_Name ->
                               T_AnnotatedTypes ->
                               T_Constructor
sem_Constructor_Constructor range_ constructor_ types_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _constructorIisIdentifier :: Bool
         _constructorIisOperator :: Bool
         _constructorIisSpecial :: Bool
         _constructorItext :: Doc
         _typesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 410 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (parensIf _constructorIisOperator _constructorItext) _typesItext
              {-# LINE 338 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 343 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _constructorIisIdentifier,_constructorIisOperator,_constructorIisSpecial,_constructorItext) =
             constructor_
         ( _typesItext) =
             types_
     in  ( _lhsOtext))
sem_Constructor_Infix :: T_Range ->
                         T_AnnotatedType ->
                         T_Name ->
                         T_AnnotatedType ->
                         T_Constructor
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _leftTypeItext :: Doc
         _constructorOperatorIisIdentifier :: Bool
         _constructorOperatorIisOperator :: Bool
         _constructorOperatorIisSpecial :: Bool
         _constructorOperatorItext :: Doc
         _rightTypeItext :: Doc
         _text =
             ({-# LINE 414 "Syntax/UHA_Pretty.ag" #-}
              _leftTypeItext <+> _constructorOperatorItext <+> _rightTypeItext
              {-# LINE 369 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 374 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _leftTypeItext) =
             leftType_
         ( _constructorOperatorIisIdentifier,_constructorOperatorIisOperator,_constructorOperatorIisSpecial,_constructorOperatorItext) =
             constructorOperator_
         ( _rightTypeItext) =
             rightType_
     in  ( _lhsOtext))
sem_Constructor_Record :: T_Range ->
                          T_Name ->
                          T_FieldDeclarations ->
                          T_Constructor
sem_Constructor_Record range_ constructor_ fieldDeclarations_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _constructorIisIdentifier :: Bool
         _constructorIisOperator :: Bool
         _constructorIisSpecial :: Bool
         _constructorItext :: Doc
         _fieldDeclarationsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 419 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! record constructor -}"
              {-# LINE 400 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 405 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _constructorIisIdentifier,_constructorIisOperator,_constructorIisSpecial,_constructorItext) =
             constructor_
         ( _fieldDeclarationsItext) =
             fieldDeclarations_
     in  ( _lhsOtext))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors ->
                    T_Constructors
sem_Constructors list =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list))
-- semantic domain
type T_Constructors = ( ( [       Doc ] ))
sem_Constructors_Cons :: T_Constructor ->
                         T_Constructors ->
                         T_Constructors
sem_Constructors_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 432 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Constructors_Nil :: T_Constructors
sem_Constructors_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 445 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- ContextItem -------------------------------------------------
-- cata
sem_ContextItem :: ContextItem ->
                   T_ContextItem
sem_ContextItem (ContextItem_ContextItem _range _name _types) =
    (sem_ContextItem_ContextItem (sem_Range _range) (sem_Name _name) (sem_Types _types))
-- semantic domain
type T_ContextItem = ( Doc)
sem_ContextItem_ContextItem :: T_Range ->
                               T_Name ->
                               T_Types ->
                               T_ContextItem
sem_ContextItem_ContextItem range_ name_ types_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _typesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 404 "Syntax/UHA_Pretty.ag" #-}
              _nameItext <+> head _typesItext
              {-# LINE 471 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 476 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _typesItext) =
             types_
     in  ( _lhsOtext))
-- ContextItems ------------------------------------------------
-- cata
sem_ContextItems :: ContextItems ->
                    T_ContextItems
sem_ContextItems list =
    (Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list))
-- semantic domain
type T_ContextItems = ( ( [       Doc ] ))
sem_ContextItems_Cons :: T_ContextItem ->
                         T_ContextItems ->
                         T_ContextItems
sem_ContextItems_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 503 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_ContextItems_Nil :: T_ContextItems
sem_ContextItems_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 516 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Declaration -------------------------------------------------
-- cata
sem_Declaration :: Declaration ->
                   T_Declaration
sem_Declaration (Declaration_Class _range _context _simpletype _where) =
    (sem_Declaration_Class (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_MaybeDeclarations _where))
sem_Declaration (Declaration_Data _range _context _simpletype _constructors _derivings) =
    (sem_Declaration_Data (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_Constructors _constructors) (sem_Names _derivings))
sem_Declaration (Declaration_Default _range _types) =
    (sem_Declaration_Default (sem_Range _range) (sem_Types _types))
sem_Declaration (Declaration_Empty _range) =
    (sem_Declaration_Empty (sem_Range _range))
sem_Declaration (Declaration_Fixity _range _fixity _priority _operators) =
    (sem_Declaration_Fixity (sem_Range _range) (sem_Fixity _fixity) (sem_MaybeInt _priority) (sem_Names _operators))
sem_Declaration (Declaration_FunctionBindings _range _bindings) =
    (sem_Declaration_FunctionBindings (sem_Range _range) (sem_FunctionBindings _bindings))
sem_Declaration (Declaration_Hole _range _id) =
    (sem_Declaration_Hole (sem_Range _range) _id)
sem_Declaration (Declaration_Instance _range _context _name _types _where) =
    (sem_Declaration_Instance (sem_Range _range) (sem_ContextItems _context) (sem_Name _name) (sem_Types _types) (sem_MaybeDeclarations _where))
sem_Declaration (Declaration_Newtype _range _context _simpletype _constructor _derivings) =
    (sem_Declaration_Newtype (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_Constructor _constructor) (sem_Names _derivings))
sem_Declaration (Declaration_PatternBinding _range _pattern _righthandside) =
    (sem_Declaration_PatternBinding (sem_Range _range) (sem_Pattern _pattern) (sem_RightHandSide _righthandside))
sem_Declaration (Declaration_Type _range _simpletype _type) =
    (sem_Declaration_Type (sem_Range _range) (sem_SimpleType _simpletype) (sem_Type _type))
sem_Declaration (Declaration_TypeSignature _range _names _type) =
    (sem_Declaration_TypeSignature (sem_Range _range) (sem_Names _names) (sem_Type _type))
-- semantic domain
type T_Declaration = ( Doc)
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _contextItext :: ( [       Doc ] )
         _simpletypeItext :: Doc
         _whereItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 298 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! class decl -}"
              {-# LINE 563 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 568 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _contextItext) =
             context_
         ( _simpletypeItext) =
             simpletype_
         ( _whereItext) =
             where_
     in  ( _lhsOtext))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _contextItext :: ( [       Doc ] )
         _simpletypeItext :: Doc
         _constructorsItext :: ( [       Doc ] )
         _derivingsIisIdentifier :: ( [Bool] )
         _derivingsIisOperator :: ( [Bool] )
         _derivingsIisSpecial :: ( [Bool] )
         _derivingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 238 "Syntax/UHA_Pretty.ag" #-}
              text "data" <+>
              _contextDoc
              <>
              _simpletypeItext
              <$>
              (indent 4 $
                  vcat
                      (   text "="
                          <+>
                          head _constructorsItext
                      :   map
                              (text "|" <+>)
                              (tail _constructorsItext)
                      ++  [_derivingDoc]
                      )
              )
              {-# LINE 613 "Syntax/UHA_Pretty.hs" #-}
              )
         _contextDoc =
             ({-# LINE 255 "Syntax/UHA_Pretty.ag" #-}
              case _contextItext of
               []  -> empty
               [x] -> x <+> text "=>" <+> empty
               xs  -> tupled xs <+> text "=>" <+> empty
              {-# LINE 621 "Syntax/UHA_Pretty.hs" #-}
              )
         _derivingDoc =
             ({-# LINE 259 "Syntax/UHA_Pretty.ag" #-}
              if null _derivingsItext then
                  empty
              else
                  (    empty
                  <+>  text "deriving"
                  <+>  tupledUnit _derivingsItext
                  )
              {-# LINE 632 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 637 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _contextItext) =
             context_
         ( _simpletypeItext) =
             simpletype_
         ( _constructorsItext) =
             constructors_
         ( _derivingsIisIdentifier,_derivingsIisOperator,_derivingsIisSpecial,_derivingsItext) =
             derivings_
     in  ( _lhsOtext))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _typesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 310 "Syntax/UHA_Pretty.ag" #-}
              text "default" <+> tupled _typesItext
              {-# LINE 660 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 665 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _typesItext) =
             types_
     in  ( _lhsOtext))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 344 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 680 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 685 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _fixityItext :: Doc
         _priorityItext :: (        Maybe Doc  )
         _operatorsIisIdentifier :: ( [Bool] )
         _operatorsIisOperator :: ( [Bool] )
         _operatorsIisSpecial :: ( [Bool] )
         _operatorsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 329 "Syntax/UHA_Pretty.ag" #-}
              _fixityItext <+> _ops
              {-# LINE 707 "Syntax/UHA_Pretty.hs" #-}
              )
         _ops =
             ({-# LINE 330 "Syntax/UHA_Pretty.ag" #-}
              opt _priorityItext <+>
                  commas
                      (map
                          (\(n, p) -> if p then
                              text "`" <> n <> text "`"
                           else
                              n
                          )
                          (zip _operatorsItext _operatorsIisIdentifier)
                      )
              {-# LINE 721 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 726 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _fixityItext) =
             fixity_
         ( _priorityItext) =
             priority_
         ( _operatorsIisIdentifier,_operatorsIisOperator,_operatorsIisSpecial,_operatorsItext) =
             operators_
     in  ( _lhsOtext))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _bindingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 314 "Syntax/UHA_Pretty.ag" #-}
              case filter ((/= "") . show) _bindingsItext of
                 [] -> empty
                 xs -> foldl1  (<$>) xs
              {-# LINE 749 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 754 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _bindingsItext) =
             bindings_
     in  ( _lhsOtext))
sem_Declaration_Hole :: T_Range ->
                        Integer ->
                        T_Declaration
sem_Declaration_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 233 "Syntax/UHA_Pretty.ag" #-}
              text hole
              {-# LINE 770 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 775 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _contextItext :: ( [       Doc ] )
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _typesItext :: ( [       Doc ] )
         _whereItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 303 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! instance decl -}"
              {-# LINE 799 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 804 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _contextItext) =
             context_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _typesItext) =
             types_
         ( _whereItext) =
             where_
     in  ( _lhsOtext))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _contextItext :: ( [       Doc ] )
         _simpletypeItext :: Doc
         _constructorItext :: Doc
         _derivingsIisIdentifier :: ( [Bool] )
         _derivingsIisOperator :: ( [Bool] )
         _derivingsIisSpecial :: ( [Bool] )
         _derivingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 272 "Syntax/UHA_Pretty.ag" #-}
              text "newtype"
              <+>
              _contextDoc
              <>
              _simpletypeItext
              <+>
              _constructorItext
              <>
              _derivingDoc
              {-# LINE 844 "Syntax/UHA_Pretty.hs" #-}
              )
         _contextDoc =
             ({-# LINE 281 "Syntax/UHA_Pretty.ag" #-}
              case _contextItext of
               []  -> empty
               [x] -> x <+> text "=>" <+> empty
               xs  -> tupled xs <+> text "=>" <+> empty
              {-# LINE 852 "Syntax/UHA_Pretty.hs" #-}
              )
         _derivingDoc =
             ({-# LINE 285 "Syntax/UHA_Pretty.ag" #-}
              if null _derivingsItext then
                  empty
              else
                  (    empty
                  <+>  text "deriving"
                  <+>  tupledUnit _derivingsItext
                  )
              {-# LINE 863 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 868 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _contextItext) =
             context_
         ( _simpletypeItext) =
             simpletype_
         ( _constructorItext) =
             constructor_
         ( _derivingsIisIdentifier,_derivingsIisOperator,_derivingsIisSpecial,_derivingsItext) =
             derivings_
     in  ( _lhsOtext))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _righthandsideItext :: ( Doc        -> Doc  )
         _text =
             ({-# LINE 320 "Syntax/UHA_Pretty.ag" #-}
              _patternItext <+> _righthandsideItext (text "=")
              {-# LINE 893 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 898 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
         ( _righthandsideItext) =
             righthandside_
     in  ( _lhsOtext))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _simpletypeItext :: Doc
         _typeItext :: Doc
         _text =
             ({-# LINE 234 "Syntax/UHA_Pretty.ag" #-}
              text "type" <+> _simpletypeItext <+> text "=" <+> _typeItext
              {-# LINE 919 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 924 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _simpletypeItext) =
             simpletype_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _namesIisIdentifier :: ( [Bool] )
         _namesIisOperator :: ( [Bool] )
         _namesIisSpecial :: ( [Bool] )
         _namesItext :: ( [       Doc ] )
         _typeItext :: Doc
         _text =
             ({-# LINE 324 "Syntax/UHA_Pretty.ag" #-}
              commas _namesDocs <+> text "::" <+> _typeItext
              {-# LINE 948 "Syntax/UHA_Pretty.hs" #-}
              )
         _namesDocs =
             ({-# LINE 325 "Syntax/UHA_Pretty.ag" #-}
              parensIfList _namesIisOperator _namesItext
              {-# LINE 953 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 958 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _namesIisIdentifier,_namesIisOperator,_namesIisSpecial,_namesItext) =
             names_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list))
-- semantic domain
type T_Declarations = ( ( [       Doc ] ))
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 985 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 998 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Export ------------------------------------------------------
-- cata
sem_Export :: Export ->
              T_Export
sem_Export (Export_Module _range _name) =
    (sem_Export_Module (sem_Range _range) (sem_Name _name))
sem_Export (Export_TypeOrClass _range _name _names) =
    (sem_Export_TypeOrClass (sem_Range _range) (sem_Name _name) (sem_MaybeNames _names))
sem_Export (Export_TypeOrClassComplete _range _name) =
    (sem_Export_TypeOrClassComplete (sem_Range _range) (sem_Name _name))
sem_Export (Export_Variable _range _name) =
    (sem_Export_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Export = ( Doc)
sem_Export_Module :: T_Range ->
                     T_Name ->
                     T_Export
sem_Export_Module range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 162 "Syntax/UHA_Pretty.ag" #-}
              text "module" <+> _nameItext
              {-# LINE 1028 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1033 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Export_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Export
sem_Export_TypeOrClass range_ name_ names_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _namesItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 155 "Syntax/UHA_Pretty.ag" #-}
              _nameItext <> maybe empty tupled (_namesItext)
              {-# LINE 1055 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1060 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _namesItext) =
             names_
     in  ( _lhsOtext))
sem_Export_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Export
sem_Export_TypeOrClassComplete range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 159 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 1082 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1087 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Export_Variable :: T_Range ->
                       T_Name ->
                       T_Export
sem_Export_Variable range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 152 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 1107 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1112 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports ->
               T_Exports
sem_Exports list =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list))
-- semantic domain
type T_Exports = ( ( [       Doc ] ))
sem_Exports_Cons :: T_Export ->
                    T_Exports ->
                    T_Exports
sem_Exports_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 1137 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Exports_Nil :: T_Exports
sem_Exports_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 1150 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Expression --------------------------------------------------
-- cata
sem_Expression :: Expression ->
                  T_Expression
sem_Expression (Expression_Case _range _expression _alternatives) =
    (sem_Expression_Case (sem_Range _range) (sem_Expression _expression) (sem_Alternatives _alternatives))
sem_Expression (Expression_Comprehension _range _expression _qualifiers) =
    (sem_Expression_Comprehension (sem_Range _range) (sem_Expression _expression) (sem_Qualifiers _qualifiers))
sem_Expression (Expression_Constructor _range _name) =
    (sem_Expression_Constructor (sem_Range _range) (sem_Name _name))
sem_Expression (Expression_Do _range _statements) =
    (sem_Expression_Do (sem_Range _range) (sem_Statements _statements))
sem_Expression (Expression_Enum _range _from _then _to) =
    (sem_Expression_Enum (sem_Range _range) (sem_Expression _from) (sem_MaybeExpression _then) (sem_MaybeExpression _to))
sem_Expression (Expression_Feedback _range _feedback _expression) =
    (sem_Expression_Feedback (sem_Range _range) _feedback (sem_Expression _expression))
sem_Expression (Expression_Hole _range _id) =
    (sem_Expression_Hole (sem_Range _range) _id)
sem_Expression (Expression_If _range _guardExpression _thenExpression _elseExpression) =
    (sem_Expression_If (sem_Range _range) (sem_Expression _guardExpression) (sem_Expression _thenExpression) (sem_Expression _elseExpression))
sem_Expression (Expression_InfixApplication _range _leftExpression _operator _rightExpression) =
    (sem_Expression_InfixApplication (sem_Range _range) (sem_MaybeExpression _leftExpression) (sem_Expression _operator) (sem_MaybeExpression _rightExpression))
sem_Expression (Expression_Lambda _range _patterns _expression) =
    (sem_Expression_Lambda (sem_Range _range) (sem_Patterns _patterns) (sem_Expression _expression))
sem_Expression (Expression_Let _range _declarations _expression) =
    (sem_Expression_Let (sem_Range _range) (sem_Declarations _declarations) (sem_Expression _expression))
sem_Expression (Expression_List _range _expressions) =
    (sem_Expression_List (sem_Range _range) (sem_Expressions _expressions))
sem_Expression (Expression_Literal _range _literal) =
    (sem_Expression_Literal (sem_Range _range) (sem_Literal _literal))
sem_Expression (Expression_MustUse _range _expression) =
    (sem_Expression_MustUse (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_Negate _range _expression) =
    (sem_Expression_Negate (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_NegateFloat _range _expression) =
    (sem_Expression_NegateFloat (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_NormalApplication _range _function _arguments) =
    (sem_Expression_NormalApplication (sem_Range _range) (sem_Expression _function) (sem_Expressions _arguments))
sem_Expression (Expression_Parenthesized _range _expression) =
    (sem_Expression_Parenthesized (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_RecordConstruction _range _name _recordExpressionBindings) =
    (sem_Expression_RecordConstruction (sem_Range _range) (sem_Name _name) (sem_RecordExpressionBindings _recordExpressionBindings))
sem_Expression (Expression_RecordUpdate _range _expression _recordExpressionBindings) =
    (sem_Expression_RecordUpdate (sem_Range _range) (sem_Expression _expression) (sem_RecordExpressionBindings _recordExpressionBindings))
sem_Expression (Expression_Tuple _range _expressions) =
    (sem_Expression_Tuple (sem_Range _range) (sem_Expressions _expressions))
sem_Expression (Expression_Typed _range _expression _type) =
    (sem_Expression_Typed (sem_Range _range) (sem_Expression _expression) (sem_Type _type))
sem_Expression (Expression_Variable _range _name) =
    (sem_Expression_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Expression = ( Doc)
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _alternativesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 496 "Syntax/UHA_Pretty.ag" #-}
              (text "case" <+> _expressionItext <+> text "of" <$>
                             (indent 4 $ vcat _alternativesItext) <$> empty
                         )
              {-# LINE 1219 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1224 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
         ( _alternativesItext) =
             alternatives_
     in  ( _lhsOtext))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _qualifiersItext :: ( [       Doc ] )
         _text =
             ({-# LINE 521 "Syntax/UHA_Pretty.ag" #-}
              text "[" <+> _expressionItext <+>
              text "|" <+> commas _qualifiersItext <+> text "]"
              {-# LINE 1246 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1251 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
         ( _qualifiersItext) =
             qualifiers_
     in  ( _lhsOtext))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 455 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 1273 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1278 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _statementsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 512 "Syntax/UHA_Pretty.ag" #-}
              text "do" <$> (indent 4 $ vcat _statementsItext) <$> empty
              {-# LINE 1295 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1300 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _statementsItext) =
             statements_
     in  ( _lhsOtext))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _fromItext :: Doc
         _thenItext :: (        Maybe Doc  )
         _toItext :: (        Maybe Doc  )
         _text =
             ({-# LINE 538 "Syntax/UHA_Pretty.ag" #-}
              text "[" <>
              _fromItext <>
              maybe empty (text "," <+>)  _thenItext <+>
              text ".." <+>
              opt _toItext <>
              text "]"
              {-# LINE 1326 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1331 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _fromItext) =
             from_
         ( _thenItext) =
             then_
         ( _toItext) =
             to_
     in  ( _lhsOtext))
sem_Expression_Feedback :: T_Range ->
                           String ->
                           T_Expression ->
                           T_Expression
sem_Expression_Feedback range_ feedback_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _expressionItext
              {-# LINE 1353 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_Hole :: T_Range ->
                       Integer ->
                       T_Expression
sem_Expression_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 446 "Syntax/UHA_Pretty.ag" #-}
              text hole
              {-# LINE 1369 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1374 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _guardExpressionItext :: Doc
         _thenExpressionItext :: Doc
         _elseExpressionItext :: Doc
         _text =
             ({-# LINE 485 "Syntax/UHA_Pretty.ag" #-}
              text "if" <+> _guardExpressionItext <$>
                 indent 4 (text "then" <+> _thenExpressionItext <$>
                           text "else" <+> _elseExpressionItext)
              {-# LINE 1395 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1400 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _guardExpressionItext) =
             guardExpression_
         ( _thenExpressionItext) =
             thenExpression_
         ( _elseExpressionItext) =
             elseExpression_
     in  ( _lhsOtext))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _leftExpressionItext :: (        Maybe Doc  )
         _operatorItext :: Doc
         _rightExpressionItext :: (        Maybe Doc  )
         _text =
             ({-# LINE 465 "Syntax/UHA_Pretty.ag" #-}
              let f []     m = m
                  f (c:cs) m = if isAlpha c && all (\ch -> ch == '_' || ch == '\'' || isAlphaNum ch) cs then char '`' <> m <> char '`' else m
              in
                 case (_leftExpressionItext, _rightExpressionItext) of
                     (Nothing, Nothing) ->
                         parens _operatorItext
                     (Just l , Nothing) ->
                         parens (l <+> _operatorItext)
                     (Nothing, Just r ) ->
                         parens (_operatorItext <+> r)
                     (Just l , Just r ) ->
                         l
                         <+>
                         f (show _operatorItext) _operatorItext
                         <+>
                         r
              {-# LINE 1440 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1445 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _leftExpressionItext) =
             leftExpression_
         ( _operatorItext) =
             operator_
         ( _rightExpressionItext) =
             rightExpression_
     in  ( _lhsOtext))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _expressionItext :: Doc
         _text =
             ({-# LINE 492 "Syntax/UHA_Pretty.ag" #-}
              text "\\" <+> foldl1 (<+>) _patternsItext <+> text "->" <+> _expressionItext
              {-# LINE 1468 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1473 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternsItext) =
             patterns_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _declarationsItext :: ( [       Doc ] )
         _expressionItext :: Doc
         _text =
             ({-# LINE 504 "Syntax/UHA_Pretty.ag" #-}
              (text "let"<$>
                             (indent 4 $ vcat _declarationsItext) <+>
                          text "in" <$>
                             (indent 4 $ _expressionItext)
                         ) <$> empty
              {-# LINE 1498 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1503 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _declarationsItext) =
             declarations_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 515 "Syntax/UHA_Pretty.ag" #-}
              PPrint.list _expressionsItext
              {-# LINE 1522 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1527 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionsItext) =
             expressions_
     in  ( _lhsOtext))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _literalItext :: Doc
         _text =
             ({-# LINE 449 "Syntax/UHA_Pretty.ag" #-}
              _literalItext
              {-# LINE 1544 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1549 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _literalItext) =
             literal_
     in  ( _lhsOtext))
sem_Expression_MustUse :: T_Range ->
                          T_Expression ->
                          T_Expression
sem_Expression_MustUse range_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _expressionItext
              {-# LINE 1566 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 549 "Syntax/UHA_Pretty.ag" #-}
              text "-"  <> _expressionItext
              {-# LINE 1583 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1588 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 550 "Syntax/UHA_Pretty.ag" #-}
              text "-." <> _expressionItext
              {-# LINE 1605 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1610 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _functionItext :: Doc
         _argumentsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 461 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) _functionItext _argumentsItext
              {-# LINE 1629 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1634 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _functionItext) =
             function_
         ( _argumentsItext) =
             arguments_
     in  ( _lhsOtext))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 458 "Syntax/UHA_Pretty.ag" #-}
              parens _expressionItext
              {-# LINE 1653 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1658 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _recordExpressionBindingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 530 "Syntax/UHA_Pretty.ag" #-}
              intErr "Expression" "record construction"
              {-# LINE 1680 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1685 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _recordExpressionBindingsItext) =
             recordExpressionBindings_
     in  ( _lhsOtext))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _recordExpressionBindingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 534 "Syntax/UHA_Pretty.ag" #-}
              intErr "Expression" "record update"
              {-# LINE 1706 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1711 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
         ( _recordExpressionBindingsItext) =
             recordExpressionBindings_
     in  ( _lhsOtext))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 518 "Syntax/UHA_Pretty.ag" #-}
              tupled _expressionsItext
              {-# LINE 1730 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1735 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionsItext) =
             expressions_
     in  ( _lhsOtext))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _typeItext :: Doc
         _text =
             ({-# LINE 526 "Syntax/UHA_Pretty.ag" #-}
              _expressionItext <+> text "::" <+> _typeItext
              {-# LINE 1754 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1759 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 452 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 1781 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1786 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list))
-- semantic domain
type T_Expressions = ( ( [       Doc ] ))
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 1811 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 1824 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- FieldDeclaration --------------------------------------------
-- cata
sem_FieldDeclaration :: FieldDeclaration ->
                        T_FieldDeclaration
sem_FieldDeclaration (FieldDeclaration_FieldDeclaration _range _names _type) =
    (sem_FieldDeclaration_FieldDeclaration (sem_Range _range) (sem_Names _names) (sem_AnnotatedType _type))
-- semantic domain
type T_FieldDeclaration = ( Doc)
sem_FieldDeclaration_FieldDeclaration :: T_Range ->
                                         T_Names ->
                                         T_AnnotatedType ->
                                         T_FieldDeclaration
sem_FieldDeclaration_FieldDeclaration range_ names_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _namesIisIdentifier :: ( [Bool] )
         _namesIisOperator :: ( [Bool] )
         _namesIisSpecial :: ( [Bool] )
         _namesItext :: ( [       Doc ] )
         _typeItext :: Doc
         _text =
             ({-# LINE 425 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! field declaration -}"
              {-# LINE 1850 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1855 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _namesIisIdentifier,_namesIisOperator,_namesIisSpecial,_namesItext) =
             names_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
-- FieldDeclarations -------------------------------------------
-- cata
sem_FieldDeclarations :: FieldDeclarations ->
                         T_FieldDeclarations
sem_FieldDeclarations list =
    (Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list))
-- semantic domain
type T_FieldDeclarations = ( ( [       Doc ] ))
sem_FieldDeclarations_Cons :: T_FieldDeclaration ->
                              T_FieldDeclarations ->
                              T_FieldDeclarations
sem_FieldDeclarations_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 1882 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_FieldDeclarations_Nil :: T_FieldDeclarations
sem_FieldDeclarations_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 1895 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Fixity ------------------------------------------------------
-- cata
sem_Fixity :: Fixity ->
              T_Fixity
sem_Fixity (Fixity_Infix _range) =
    (sem_Fixity_Infix (sem_Range _range))
sem_Fixity (Fixity_Infixl _range) =
    (sem_Fixity_Infixl (sem_Range _range))
sem_Fixity (Fixity_Infixr _range) =
    (sem_Fixity_Infixr (sem_Range _range))
-- semantic domain
type T_Fixity = ( Doc)
sem_Fixity_Infix :: T_Range ->
                    T_Fixity
sem_Fixity_Infix range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 352 "Syntax/UHA_Pretty.ag" #-}
              text "infix "
              {-# LINE 1918 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1923 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Fixity_Infixl :: T_Range ->
                     T_Fixity
sem_Fixity_Infixl range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 348 "Syntax/UHA_Pretty.ag" #-}
              text "infixl"
              {-# LINE 1936 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1941 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Fixity_Infixr :: T_Range ->
                     T_Fixity
sem_Fixity_Infixr range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 350 "Syntax/UHA_Pretty.ag" #-}
              text "infixr"
              {-# LINE 1954 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 1959 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- FunctionBinding ---------------------------------------------
-- cata
sem_FunctionBinding :: FunctionBinding ->
                       T_FunctionBinding
sem_FunctionBinding (FunctionBinding_Feedback _range _feedback _functionBinding) =
    (sem_FunctionBinding_Feedback (sem_Range _range) _feedback (sem_FunctionBinding _functionBinding))
sem_FunctionBinding (FunctionBinding_FunctionBinding _range _lefthandside _righthandside) =
    (sem_FunctionBinding_FunctionBinding (sem_Range _range) (sem_LeftHandSide _lefthandside) (sem_RightHandSide _righthandside))
sem_FunctionBinding (FunctionBinding_Hole _range _id) =
    (sem_FunctionBinding_Hole (sem_Range _range) _id)
-- semantic domain
type T_FunctionBinding = ( Doc)
sem_FunctionBinding_Feedback :: T_Range ->
                                String ->
                                T_FunctionBinding ->
                                T_FunctionBinding
sem_FunctionBinding_Feedback range_ feedback_ functionBinding_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _functionBindingItext :: Doc
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _functionBindingItext
              {-# LINE 1987 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _functionBindingItext) =
             functionBinding_
     in  ( _lhsOtext))
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _lefthandsideItext :: Doc
         _righthandsideItext :: ( Doc        -> Doc  )
         _text =
             ({-# LINE 611 "Syntax/UHA_Pretty.ag" #-}
              _lefthandsideItext <+> _righthandsideItext (text "=")
              {-# LINE 2006 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2011 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _lefthandsideItext) =
             lefthandside_
         ( _righthandsideItext) =
             righthandside_
     in  ( _lhsOtext))
sem_FunctionBinding_Hole :: T_Range ->
                            Integer ->
                            T_FunctionBinding
sem_FunctionBinding_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 610 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 2029 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2034 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list))
-- semantic domain
type T_FunctionBindings = ( ( [       Doc ] ))
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 2057 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 2070 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression) =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range) (sem_Expression _guard) (sem_Expression _expression))
-- semantic domain
type T_GuardedExpression = ( ( Doc        -> Doc  ))
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_ =
    (let _lhsOtext :: ( Doc        -> Doc  )
         _rangeItext :: Doc
         _guardItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 592 "Syntax/UHA_Pretty.ag" #-}
              \assign -> text "|" <+> _guardItext <+> assign <+> _expressionItext
              {-# LINE 2093 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 81 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2098 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _guardItext) =
             guard_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list))
-- semantic domain
type T_GuardedExpressions = ( ( [        Doc -> Doc  ] ))
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_ =
    (let _lhsOtext :: ( [        Doc -> Doc  ] )
         _hdItext :: ( Doc        -> Doc  )
         _tlItext :: ( [        Doc -> Doc  ] )
         _lhsOtext =
             ({-# LINE 87 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 2125 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil =
    (let _lhsOtext :: ( [        Doc -> Doc  ] )
         _lhsOtext =
             ({-# LINE 87 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 2138 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Import ------------------------------------------------------
-- cata
sem_Import :: Import ->
              T_Import
sem_Import (Import_TypeOrClass _range _name _names) =
    (sem_Import_TypeOrClass (sem_Range _range) (sem_Name _name) (sem_MaybeNames _names))
sem_Import (Import_TypeOrClassComplete _range _name) =
    (sem_Import_TypeOrClassComplete (sem_Range _range) (sem_Name _name))
sem_Import (Import_Variable _range _name) =
    (sem_Import_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Import = ( Doc)
sem_Import_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Import
sem_Import_TypeOrClass range_ name_ names_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _namesItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 209 "Syntax/UHA_Pretty.ag" #-}
              _nameItext <> maybe empty tupled1 _namesItext
              {-# LINE 2168 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2173 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _namesItext) =
             names_
     in  ( _lhsOtext))
sem_Import_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Import
sem_Import_TypeOrClassComplete range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 213 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 2195 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2200 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Import_Variable :: T_Range ->
                       T_Name ->
                       T_Import
sem_Import_Variable range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 206 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 2220 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2225 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
-- ImportDeclaration -------------------------------------------
-- cata
sem_ImportDeclaration :: ImportDeclaration ->
                         T_ImportDeclaration
sem_ImportDeclaration (ImportDeclaration_Empty _range) =
    (sem_ImportDeclaration_Empty (sem_Range _range))
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification) =
    (sem_ImportDeclaration_Import (sem_Range _range) _qualified (sem_Name _name) (sem_MaybeName _asname) (sem_MaybeImportSpecification _importspecification))
-- semantic domain
type T_ImportDeclaration = ( Doc)
sem_ImportDeclaration_Empty :: T_Range ->
                               T_ImportDeclaration
sem_ImportDeclaration_Empty range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 191 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 2250 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2255 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_ImportDeclaration_Import :: T_Range ->
                                Bool ->
                                T_Name ->
                                T_MaybeName ->
                                T_MaybeImportSpecification ->
                                T_ImportDeclaration
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _asnameItext :: (        Maybe Doc  )
         _importspecificationItext :: (        Maybe Doc  )
         _text =
             ({-# LINE 185 "Syntax/UHA_Pretty.ag" #-}
              text "import" <+> (if qualified_ then (text "qualified" <+>) else id) _nameItext <+> maybe empty id _importspecificationItext
              {-# LINE 2278 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2283 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _asnameItext) =
             asname_
         ( _importspecificationItext) =
             importspecification_
     in  ( _lhsOtext))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations ->
                          T_ImportDeclarations
sem_ImportDeclarations list =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list))
-- semantic domain
type T_ImportDeclarations = ( ( [       Doc ] ))
sem_ImportDeclarations_Cons :: T_ImportDeclaration ->
                               T_ImportDeclarations ->
                               T_ImportDeclarations
sem_ImportDeclarations_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 2312 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_ImportDeclarations_Nil :: T_ImportDeclarations
sem_ImportDeclarations_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 2325 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification ->
                           T_ImportSpecification
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports) =
    (sem_ImportSpecification_Import (sem_Range _range) _hiding (sem_Imports _imports))
-- semantic domain
type T_ImportSpecification = ( Doc)
sem_ImportSpecification_Import :: T_Range ->
                                  Bool ->
                                  T_Imports ->
                                  T_ImportSpecification
sem_ImportSpecification_Import range_ hiding_ imports_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _importsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 199 "Syntax/UHA_Pretty.ag" #-}
              (if hiding_ then (text "hiding" <+>) else id)
                                       (tupled _importsItext)
              {-# LINE 2348 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2353 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _importsItext) =
             imports_
     in  ( _lhsOtext))
-- Imports -----------------------------------------------------
-- cata
sem_Imports :: Imports ->
               T_Imports
sem_Imports list =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list))
-- semantic domain
type T_Imports = ( ( [       Doc ] ))
sem_Imports_Cons :: T_Import ->
                    T_Imports ->
                    T_Imports
sem_Imports_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 2378 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Imports_Nil :: T_Imports
sem_Imports_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 2391 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- LeftHandSide ------------------------------------------------
-- cata
sem_LeftHandSide :: LeftHandSide ->
                    T_LeftHandSide
sem_LeftHandSide (LeftHandSide_Function _range _name _patterns) =
    (sem_LeftHandSide_Function (sem_Range _range) (sem_Name _name) (sem_Patterns _patterns))
sem_LeftHandSide (LeftHandSide_Infix _range _leftPattern _operator _rightPattern) =
    (sem_LeftHandSide_Infix (sem_Range _range) (sem_Pattern _leftPattern) (sem_Name _operator) (sem_Pattern _rightPattern))
sem_LeftHandSide (LeftHandSide_Parenthesized _range _lefthandside _patterns) =
    (sem_LeftHandSide_Parenthesized (sem_Range _range) (sem_LeftHandSide _lefthandside) (sem_Patterns _patterns))
-- semantic domain
type T_LeftHandSide = ( Doc)
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 617 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (parensIf _nameIisOperator _nameItext) _patternsItext
              {-# LINE 2421 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2426 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _patternsItext) =
             patterns_
     in  ( _lhsOtext))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _leftPatternItext :: Doc
         _operatorIisIdentifier :: Bool
         _operatorIisOperator :: Bool
         _operatorIisSpecial :: Bool
         _operatorItext :: Doc
         _rightPatternItext :: Doc
         _text =
             ({-# LINE 621 "Syntax/UHA_Pretty.ag" #-}
              _leftPatternItext <+> backQuotesIf (not _operatorIisOperator) _operatorItext <+> _rightPatternItext
              {-# LINE 2452 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2457 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _leftPatternItext) =
             leftPattern_
         ( _operatorIisIdentifier,_operatorIisOperator,_operatorIisSpecial,_operatorItext) =
             operator_
         ( _rightPatternItext) =
             rightPattern_
     in  ( _lhsOtext))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _lefthandsideItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 626 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (parens _lefthandsideItext) _patternsItext
              {-# LINE 2480 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2485 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _lefthandsideItext) =
             lefthandside_
         ( _patternsItext) =
             patterns_
     in  ( _lhsOtext))
-- Literal -----------------------------------------------------
-- cata
sem_Literal :: Literal ->
               T_Literal
sem_Literal (Literal_Char _range _value) =
    (sem_Literal_Char (sem_Range _range) _value)
sem_Literal (Literal_Float _range _value) =
    (sem_Literal_Float (sem_Range _range) _value)
sem_Literal (Literal_Int _range _value) =
    (sem_Literal_Int (sem_Range _range) _value)
sem_Literal (Literal_String _range _value) =
    (sem_Literal_String (sem_Range _range) _value)
-- semantic domain
type T_Literal = ( Doc)
sem_Literal_Char :: T_Range ->
                    String ->
                    T_Literal
sem_Literal_Char range_ value_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 730 "Syntax/UHA_Pretty.ag" #-}
              text ("'" ++ value_ ++ "'")
              {-# LINE 2517 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2522 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Literal_Float :: T_Range ->
                     String ->
                     T_Literal
sem_Literal_Float range_ value_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 733 "Syntax/UHA_Pretty.ag" #-}
              text value_
              {-# LINE 2536 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2541 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Literal_Int :: T_Range ->
                   String ->
                   T_Literal
sem_Literal_Int range_ value_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 727 "Syntax/UHA_Pretty.ag" #-}
              text value_
              {-# LINE 2555 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2560 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Literal_String :: T_Range ->
                      String ->
                      T_Literal
sem_Literal_String range_ value_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 736 "Syntax/UHA_Pretty.ag" #-}
              text ("\"" ++ value_ ++ "\"")
              {-# LINE 2574 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2579 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations ->
                         T_MaybeDeclarations
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations) =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations))
sem_MaybeDeclarations (MaybeDeclarations_Nothing) =
    (sem_MaybeDeclarations_Nothing)
-- semantic domain
type T_MaybeDeclarations = ( ( Maybe [       Doc ] ))
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_ =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _declarationsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 226 "Syntax/UHA_Pretty.ag" #-}
              case filter ((/= "") . show) _declarationsItext of
                [] -> Nothing
                xs -> Just xs
              {-# LINE 2604 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2609 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _declarationsItext) =
             declarations_
     in  ( _lhsOtext))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 224 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2620 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2625 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports ->
                    T_MaybeExports
sem_MaybeExports (MaybeExports_Just _exports) =
    (sem_MaybeExports_Just (sem_Exports _exports))
sem_MaybeExports (MaybeExports_Nothing) =
    (sem_MaybeExports_Nothing)
-- semantic domain
type T_MaybeExports = ( ( Maybe [       Doc ] ))
sem_MaybeExports_Just :: T_Exports ->
                         T_MaybeExports
sem_MaybeExports_Just exports_ =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _exportsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 148 "Syntax/UHA_Pretty.ag" #-}
              Just _exportsItext
              {-# LINE 2646 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2651 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _exportsItext) =
             exports_
     in  ( _lhsOtext))
sem_MaybeExports_Nothing :: T_MaybeExports
sem_MaybeExports_Nothing =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 147 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2662 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2667 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression ->
                       T_MaybeExpression
sem_MaybeExpression (MaybeExpression_Just _expression) =
    (sem_MaybeExpression_Just (sem_Expression _expression))
sem_MaybeExpression (MaybeExpression_Nothing) =
    (sem_MaybeExpression_Nothing)
-- semantic domain
type T_MaybeExpression = ( (        Maybe Doc  ))
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_ =
    (let _lhsOtext :: (        Maybe Doc  )
         _expressionItext :: Doc
         _text =
             ({-# LINE 442 "Syntax/UHA_Pretty.ag" #-}
              Just _expressionItext
              {-# LINE 2688 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2693 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing =
    (let _lhsOtext :: (        Maybe Doc  )
         _text =
             ({-# LINE 441 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2704 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2709 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification ->
                                T_MaybeImportSpecification
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification) =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification))
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing) =
    (sem_MaybeImportSpecification_Nothing)
-- semantic domain
type T_MaybeImportSpecification = ( (        Maybe Doc  ))
sem_MaybeImportSpecification_Just :: T_ImportSpecification ->
                                     T_MaybeImportSpecification
sem_MaybeImportSpecification_Just importspecification_ =
    (let _lhsOtext :: (        Maybe Doc  )
         _importspecificationItext :: Doc
         _text =
             ({-# LINE 195 "Syntax/UHA_Pretty.ag" #-}
              Just _importspecificationItext
              {-# LINE 2730 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2735 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _importspecificationItext) =
             importspecification_
     in  ( _lhsOtext))
sem_MaybeImportSpecification_Nothing :: T_MaybeImportSpecification
sem_MaybeImportSpecification_Nothing =
    (let _lhsOtext :: (        Maybe Doc  )
         _text =
             ({-# LINE 194 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2746 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2751 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeInt ----------------------------------------------------
-- cata
sem_MaybeInt :: MaybeInt ->
                T_MaybeInt
sem_MaybeInt (MaybeInt_Just _int) =
    (sem_MaybeInt_Just _int)
sem_MaybeInt (MaybeInt_Nothing) =
    (sem_MaybeInt_Nothing)
-- semantic domain
type T_MaybeInt = ( (        Maybe Doc  ))
sem_MaybeInt_Just :: Int ->
                     T_MaybeInt
sem_MaybeInt_Just int_ =
    (let _lhsOtext :: (        Maybe Doc  )
         _text =
             ({-# LINE 764 "Syntax/UHA_Pretty.ag" #-}
              Just (int int_)
              {-# LINE 2771 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2776 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
sem_MaybeInt_Nothing :: T_MaybeInt
sem_MaybeInt_Nothing =
    (let _lhsOtext :: (        Maybe Doc  )
         _text =
             ({-# LINE 763 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2785 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2790 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeName ---------------------------------------------------
-- cata
sem_MaybeName :: MaybeName ->
                 T_MaybeName
sem_MaybeName (MaybeName_Just _name) =
    (sem_MaybeName_Just (sem_Name _name))
sem_MaybeName (MaybeName_Nothing) =
    (sem_MaybeName_Nothing)
-- semantic domain
type T_MaybeName = ( (        Maybe Doc  ))
sem_MaybeName_Just :: T_Name ->
                      T_MaybeName
sem_MaybeName_Just name_ =
    (let _lhsOtext :: (        Maybe Doc  )
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 742 "Syntax/UHA_Pretty.ag" #-}
              Just _nameItext
              {-# LINE 2814 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2819 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_MaybeName_Nothing :: T_MaybeName
sem_MaybeName_Nothing =
    (let _lhsOtext :: (        Maybe Doc  )
         _text =
             ({-# LINE 741 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2830 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 111 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2835 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- MaybeNames --------------------------------------------------
-- cata
sem_MaybeNames :: MaybeNames ->
                  T_MaybeNames
sem_MaybeNames (MaybeNames_Just _names) =
    (sem_MaybeNames_Just (sem_Names _names))
sem_MaybeNames (MaybeNames_Nothing) =
    (sem_MaybeNames_Nothing)
-- semantic domain
type T_MaybeNames = ( ( Maybe [       Doc ] ))
sem_MaybeNames_Just :: T_Names ->
                       T_MaybeNames
sem_MaybeNames_Just names_ =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _namesIisIdentifier :: ( [Bool] )
         _namesIisOperator :: ( [Bool] )
         _namesIisSpecial :: ( [Bool] )
         _namesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 168 "Syntax/UHA_Pretty.ag" #-}
              Just _namesItext
              {-# LINE 2859 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2864 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _namesIisIdentifier,_namesIisOperator,_namesIisSpecial,_namesItext) =
             names_
     in  ( _lhsOtext))
sem_MaybeNames_Nothing :: T_MaybeNames
sem_MaybeNames_Nothing =
    (let _lhsOtext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 167 "Syntax/UHA_Pretty.ag" #-}
              Nothing
              {-# LINE 2875 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 104 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2880 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Module ------------------------------------------------------
-- cata
sem_Module :: Module ->
              T_Module
sem_Module (Module_Module _range _name _exports _body) =
    (sem_Module_Module (sem_Range _range) (sem_MaybeName _name) (sem_MaybeExports _exports) (sem_Body _body))
-- semantic domain
type T_Module = ( Doc)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameItext :: (        Maybe Doc  )
         _exportsItext :: ( Maybe [       Doc ] )
         _bodyItext :: Doc
         _text =
             ({-# LINE 126 "Syntax/UHA_Pretty.ag" #-}
              maybe
                  id
                  ( \name body ->
                      text "module" <+> name <+>
                          (maybe
                              (text "where")
                              (\x -> indent 4 (utrechtList (text "(") (text ")") x <+> text "where"))
                              _exportsItext
                          )
                      <$> empty <$>
                      body
                  )
                  _nameItext
                  _bodyItext
              {-# LINE 2918 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2923 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameItext) =
             name_
         ( _exportsItext) =
             exports_
         ( _bodyItext) =
             body_
     in  ( _lhsOtext))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name (Name_Identifier _range _module _name) =
    (sem_Name_Identifier (sem_Range _range) (sem_Strings _module) _name)
sem_Name (Name_Operator _range _module _name) =
    (sem_Name_Operator (sem_Range _range) (sem_Strings _module) _name)
sem_Name (Name_Special _range _module _name) =
    (sem_Name_Special (sem_Range _range) (sem_Strings _module) _name)
-- semantic domain
type T_Name = ( Bool,Bool,Bool,Doc)
sem_Name_Identifier :: T_Range ->
                       T_Strings ->
                       String ->
                       T_Name
sem_Name_Identifier range_ module_ name_ =
    (let _lhsOisIdentifier :: Bool
         _lhsOisOperator :: Bool
         _lhsOisSpecial :: Bool
         _lhsOtext :: Doc
         _rangeItext :: Doc
         _moduleItext :: ( [       Doc ] )
         _text =
             ({-# LINE 746 "Syntax/UHA_Pretty.ag" #-}
              text name_
              {-# LINE 2960 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisIdentifier =
             ({-# LINE 747 "Syntax/UHA_Pretty.ag" #-}
              True
              {-# LINE 2965 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisOperator =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 2970 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisSpecial =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 2975 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 2980 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _moduleItext) =
             module_
     in  ( _lhsOisIdentifier,_lhsOisOperator,_lhsOisSpecial,_lhsOtext))
sem_Name_Operator :: T_Range ->
                     T_Strings ->
                     String ->
                     T_Name
sem_Name_Operator range_ module_ name_ =
    (let _lhsOisOperator :: Bool
         _lhsOisIdentifier :: Bool
         _lhsOisSpecial :: Bool
         _lhsOtext :: Doc
         _rangeItext :: Doc
         _moduleItext :: ( [       Doc ] )
         _text =
             ({-# LINE 751 "Syntax/UHA_Pretty.ag" #-}
              text name_
              {-# LINE 3001 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisOperator =
             ({-# LINE 752 "Syntax/UHA_Pretty.ag" #-}
              True
              {-# LINE 3006 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisIdentifier =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 3011 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisSpecial =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 3016 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3021 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _moduleItext) =
             module_
     in  ( _lhsOisIdentifier,_lhsOisOperator,_lhsOisSpecial,_lhsOtext))
sem_Name_Special :: T_Range ->
                    T_Strings ->
                    String ->
                    T_Name
sem_Name_Special range_ module_ name_ =
    (let _lhsOisSpecial :: Bool
         _lhsOisIdentifier :: Bool
         _lhsOisOperator :: Bool
         _lhsOtext :: Doc
         _rangeItext :: Doc
         _moduleItext :: ( [       Doc ] )
         _text =
             ({-# LINE 756 "Syntax/UHA_Pretty.ag" #-}
              text name_
              {-# LINE 3042 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisSpecial =
             ({-# LINE 757 "Syntax/UHA_Pretty.ag" #-}
              True
              {-# LINE 3047 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisIdentifier =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 3052 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisOperator =
             ({-# LINE 116 "Syntax/UHA_Pretty.ag" #-}
              False
              {-# LINE 3057 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3062 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _moduleItext) =
             module_
     in  ( _lhsOisIdentifier,_lhsOisOperator,_lhsOisSpecial,_lhsOtext))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names ->
             T_Names
sem_Names list =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list))
-- semantic domain
type T_Names = ( ( [Bool] ),( [Bool] ),( [Bool] ),( [       Doc ] ))
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_ =
    (let _lhsOisIdentifier :: ( [Bool] )
         _lhsOisOperator :: ( [Bool] )
         _lhsOisSpecial :: ( [Bool] )
         _lhsOtext :: ( [       Doc ] )
         _hdIisIdentifier :: Bool
         _hdIisOperator :: Bool
         _hdIisSpecial :: Bool
         _hdItext :: Doc
         _tlIisIdentifier :: ( [Bool] )
         _tlIisOperator :: ( [Bool] )
         _tlIisSpecial :: ( [Bool] )
         _tlItext :: ( [       Doc ] )
         _lhsOisIdentifier =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              _hdIisIdentifier  :  _tlIisIdentifier
              {-# LINE 3096 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisOperator =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              _hdIisOperator  :  _tlIisOperator
              {-# LINE 3101 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisSpecial =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              _hdIisSpecial  :  _tlIisSpecial
              {-# LINE 3106 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 3111 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdIisIdentifier,_hdIisOperator,_hdIisSpecial,_hdItext) =
             hd_
         ( _tlIisIdentifier,_tlIisOperator,_tlIisSpecial,_tlItext) =
             tl_
     in  ( _lhsOisIdentifier,_lhsOisOperator,_lhsOisSpecial,_lhsOtext))
sem_Names_Nil :: T_Names
sem_Names_Nil =
    (let _lhsOisIdentifier :: ( [Bool] )
         _lhsOisOperator :: ( [Bool] )
         _lhsOisSpecial :: ( [Bool] )
         _lhsOtext :: ( [       Doc ] )
         _lhsOisIdentifier =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3127 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisOperator =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3132 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOisSpecial =
             ({-# LINE 120 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3137 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3142 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOisIdentifier,_lhsOisOperator,_lhsOisSpecial,_lhsOtext))
-- Pattern -----------------------------------------------------
-- cata
sem_Pattern :: Pattern ->
               T_Pattern
sem_Pattern (Pattern_As _range _name _pattern) =
    (sem_Pattern_As (sem_Range _range) (sem_Name _name) (sem_Pattern _pattern))
sem_Pattern (Pattern_Constructor _range _name _patterns) =
    (sem_Pattern_Constructor (sem_Range _range) (sem_Name _name) (sem_Patterns _patterns))
sem_Pattern (Pattern_Hole _range _id) =
    (sem_Pattern_Hole (sem_Range _range) _id)
sem_Pattern (Pattern_InfixConstructor _range _leftPattern _constructorOperator _rightPattern) =
    (sem_Pattern_InfixConstructor (sem_Range _range) (sem_Pattern _leftPattern) (sem_Name _constructorOperator) (sem_Pattern _rightPattern))
sem_Pattern (Pattern_Irrefutable _range _pattern) =
    (sem_Pattern_Irrefutable (sem_Range _range) (sem_Pattern _pattern))
sem_Pattern (Pattern_List _range _patterns) =
    (sem_Pattern_List (sem_Range _range) (sem_Patterns _patterns))
sem_Pattern (Pattern_Literal _range _literal) =
    (sem_Pattern_Literal (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_Negate _range _literal) =
    (sem_Pattern_Negate (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_NegateFloat _range _literal) =
    (sem_Pattern_NegateFloat (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_Parenthesized _range _pattern) =
    (sem_Pattern_Parenthesized (sem_Range _range) (sem_Pattern _pattern))
sem_Pattern (Pattern_Record _range _name _recordPatternBindings) =
    (sem_Pattern_Record (sem_Range _range) (sem_Name _name) (sem_RecordPatternBindings _recordPatternBindings))
sem_Pattern (Pattern_Successor _range _name _literal) =
    (sem_Pattern_Successor (sem_Range _range) (sem_Name _name) (sem_Literal _literal))
sem_Pattern (Pattern_Tuple _range _patterns) =
    (sem_Pattern_Tuple (sem_Range _range) (sem_Patterns _patterns))
sem_Pattern (Pattern_Variable _range _name) =
    (sem_Pattern_Variable (sem_Range _range) (sem_Name _name))
sem_Pattern (Pattern_Wildcard _range) =
    (sem_Pattern_Wildcard (sem_Range _range))
-- semantic domain
type T_Pattern = ( Doc)
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _patternItext :: Doc
         _text =
             ({-# LINE 708 "Syntax/UHA_Pretty.ag" #-}
              _nameItext <> text "@" <> _patternItext
              {-# LINE 3196 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3201 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _patternItext) =
             pattern_
     in  ( _lhsOtext))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 680 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (parensIf _nameIisOperator _nameItext) _patternsItext
              {-# LINE 3225 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3230 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _patternsItext) =
             patterns_
     in  ( _lhsOtext))
sem_Pattern_Hole :: T_Range ->
                    Integer ->
                    T_Pattern
sem_Pattern_Hole range_ id_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 673 "Syntax/UHA_Pretty.ag" #-}
              text hole
              {-# LINE 3248 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3253 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _leftPatternItext :: Doc
         _constructorOperatorIisIdentifier :: Bool
         _constructorOperatorIisOperator :: Bool
         _constructorOperatorIisSpecial :: Bool
         _constructorOperatorItext :: Doc
         _rightPatternItext :: Doc
         _text =
             ({-# LINE 687 "Syntax/UHA_Pretty.ag" #-}
              _leftPatternItext <+> _constructorOperatorItext <+> _rightPatternItext
              {-# LINE 3275 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3280 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _leftPatternItext) =
             leftPattern_
         ( _constructorOperatorIisIdentifier,_constructorOperatorIisOperator,_constructorOperatorIisSpecial,_constructorOperatorItext) =
             constructorOperator_
         ( _rightPatternItext) =
             rightPattern_
     in  ( _lhsOtext))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _text =
             ({-# LINE 714 "Syntax/UHA_Pretty.ag" #-}
              text "~" <> _patternItext
              {-# LINE 3301 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3306 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
     in  ( _lhsOtext))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 692 "Syntax/UHA_Pretty.ag" #-}
              PPrint.list _patternsItext
              {-# LINE 3323 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3328 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternsItext) =
             patterns_
     in  ( _lhsOtext))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _literalItext :: Doc
         _text =
             ({-# LINE 674 "Syntax/UHA_Pretty.ag" #-}
              _literalItext
              {-# LINE 3345 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3350 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _literalItext) =
             literal_
     in  ( _lhsOtext))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _literalItext :: Doc
         _text =
             ({-# LINE 702 "Syntax/UHA_Pretty.ag" #-}
              text "-" <> _literalItext
              {-# LINE 3367 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3372 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _literalItext) =
             literal_
     in  ( _lhsOtext))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _literalItext :: Doc
         _text =
             ({-# LINE 705 "Syntax/UHA_Pretty.ag" #-}
              text "-." <> _literalItext
              {-# LINE 3389 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3394 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _literalItext) =
             literal_
     in  ( _lhsOtext))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _text =
             ({-# LINE 684 "Syntax/UHA_Pretty.ag" #-}
              parens _patternItext
              {-# LINE 3411 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3416 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
     in  ( _lhsOtext))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _recordPatternBindingsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 698 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! record pattern -}"
              {-# LINE 3438 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3443 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _recordPatternBindingsItext) =
             recordPatternBindings_
     in  ( _lhsOtext))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _literalItext :: Doc
         _text =
             ({-# LINE 717 "Syntax/UHA_Pretty.ag" #-}
              _nameItext <+> text "+" <+> _literalItext
              {-# LINE 3467 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3472 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _literalItext) =
             literal_
     in  ( _lhsOtext))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 695 "Syntax/UHA_Pretty.ag" #-}
              tupled _patternsItext
              {-# LINE 3491 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3496 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternsItext) =
             patterns_
     in  ( _lhsOtext))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 677 "Syntax/UHA_Pretty.ag" #-}
              parensIf _nameIisOperator _nameItext
              {-# LINE 3516 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3521 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 712 "Syntax/UHA_Pretty.ag" #-}
              text "_"
              {-# LINE 3536 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3541 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list))
-- semantic domain
type T_Patterns = ( ( [       Doc ] ))
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 3564 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3577 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Position ----------------------------------------------------
-- cata
sem_Position :: Position ->
                T_Position
sem_Position (Position_Position _filename _line _column) =
    (sem_Position_Position _filename _line _column)
sem_Position (Position_Unknown) =
    (sem_Position_Unknown)
-- semantic domain
type T_Position = ( Doc)
sem_Position_Position :: String ->
                         Int ->
                         Int ->
                         T_Position
sem_Position_Position filename_ line_ column_ =
    (let _lhsOtext :: Doc
         _text =
             ({-# LINE 773 "Syntax/UHA_Pretty.ag" #-}
              text filename_ <> tupled [int line_, int column_]
              {-# LINE 3599 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3604 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
sem_Position_Unknown :: T_Position
sem_Position_Unknown =
    (let _lhsOtext :: Doc
         _text =
             ({-# LINE 777 "Syntax/UHA_Pretty.ag" #-}
              text "Unknown"
              {-# LINE 3613 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3618 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Qualifier ---------------------------------------------------
-- cata
sem_Qualifier :: Qualifier ->
                 T_Qualifier
sem_Qualifier (Qualifier_Empty _range) =
    (sem_Qualifier_Empty (sem_Range _range))
sem_Qualifier (Qualifier_Generator _range _pattern _expression) =
    (sem_Qualifier_Generator (sem_Range _range) (sem_Pattern _pattern) (sem_Expression _expression))
sem_Qualifier (Qualifier_Guard _range _guard) =
    (sem_Qualifier_Guard (sem_Range _range) (sem_Expression _guard))
sem_Qualifier (Qualifier_Let _range _declarations) =
    (sem_Qualifier_Let (sem_Range _range) (sem_Declarations _declarations))
-- semantic domain
type T_Qualifier = ( Doc)
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 579 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 3643 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3648 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 575 "Syntax/UHA_Pretty.ag" #-}
              _patternItext <+> text "<-" <+> _expressionItext
              {-# LINE 3665 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3670 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _guardItext :: Doc
         _text =
             ({-# LINE 569 "Syntax/UHA_Pretty.ag" #-}
              _guardItext
              {-# LINE 3689 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3694 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _guardItext) =
             guard_
     in  ( _lhsOtext))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _declarationsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 572 "Syntax/UHA_Pretty.ag" #-}
              text "let" <$> (indent 4 $ vcat _declarationsItext)
              {-# LINE 3711 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3716 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _declarationsItext) =
             declarations_
     in  ( _lhsOtext))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list))
-- semantic domain
type T_Qualifiers = ( ( [       Doc ] ))
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 3741 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3754 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Range -------------------------------------------------------
-- cata
sem_Range :: Range ->
             T_Range
sem_Range (Range_Range _start _stop) =
    (sem_Range_Range (sem_Position _start) (sem_Position _stop))
-- semantic domain
type T_Range = ( Doc)
sem_Range_Range :: T_Position ->
                   T_Position ->
                   T_Range
sem_Range_Range start_ stop_ =
    (let _lhsOtext :: Doc
         _startItext :: Doc
         _stopItext :: Doc
         _text =
             ({-# LINE 768 "Syntax/UHA_Pretty.ag" #-}
              text "{-" <+> _startItext <+> text ", " <+> _stopItext <+> text "-}"
              {-# LINE 3775 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3780 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _startItext) =
             start_
         ( _stopItext) =
             stop_
     in  ( _lhsOtext))
-- RecordExpressionBinding -------------------------------------
-- cata
sem_RecordExpressionBinding :: RecordExpressionBinding ->
                               T_RecordExpressionBinding
sem_RecordExpressionBinding (RecordExpressionBinding_RecordExpressionBinding _range _name _expression) =
    (sem_RecordExpressionBinding_RecordExpressionBinding (sem_Range _range) (sem_Name _name) (sem_Expression _expression))
-- semantic domain
type T_RecordExpressionBinding = ( Doc)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 598 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! record expression binding -}"
              {-# LINE 3810 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3815 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list))
-- semantic domain
type T_RecordExpressionBindings = ( ( [       Doc ] ))
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 3842 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3855 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding ->
                            T_RecordPatternBinding
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern) =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range) (sem_Name _name) (sem_Pattern _pattern))
-- semantic domain
type T_RecordPatternBinding = ( Doc)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range ->
                                                 T_Name ->
                                                 T_Pattern ->
                                                 T_RecordPatternBinding
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _patternItext :: Doc
         _text =
             ({-# LINE 604 "Syntax/UHA_Pretty.ag" #-}
              text "{- !!! record pattern binding -}"
              {-# LINE 3881 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3886 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _patternItext) =
             pattern_
     in  ( _lhsOtext))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings ->
                             T_RecordPatternBindings
sem_RecordPatternBindings list =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list))
-- semantic domain
type T_RecordPatternBindings = ( ( [       Doc ] ))
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding ->
                                  T_RecordPatternBindings ->
                                  T_RecordPatternBindings
sem_RecordPatternBindings_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 3913 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings
sem_RecordPatternBindings_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 3926 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide ->
                     T_RightHandSide
sem_RightHandSide (RightHandSide_Expression _range _expression _where) =
    (sem_RightHandSide_Expression (sem_Range _range) (sem_Expression _expression) (sem_MaybeDeclarations _where))
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where) =
    (sem_RightHandSide_Guarded (sem_Range _range) (sem_GuardedExpressions _guardedexpressions) (sem_MaybeDeclarations _where))
-- semantic domain
type T_RightHandSide = ( ( Doc        -> Doc  ))
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_ =
    (let _lhsOtext :: ( Doc        -> Doc  )
         _rangeItext :: Doc
         _expressionItext :: Doc
         _whereItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 633 "Syntax/UHA_Pretty.ag" #-}
              \assign       -> assign <$> _justText
              {-# LINE 3951 "Syntax/UHA_Pretty.hs" #-}
              )
         _justText =
             ({-# LINE 634 "Syntax/UHA_Pretty.ag" #-}
              indent 4
                  (  _expressionItext
                  <> maybe
                         empty
                         (\ds -> PPrint.empty <$> text "where" <$> indent 4 (vcat ds))
                         _whereItext
                  )
              {-# LINE 3962 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 81 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 3967 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
         ( _whereItext) =
             where_
     in  ( _lhsOtext))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_ =
    (let _lhsOtext :: ( Doc        -> Doc  )
         _rangeItext :: Doc
         _guardedexpressionsItext :: ( [        Doc -> Doc  ] )
         _whereItext :: ( Maybe [       Doc ] )
         _text =
             ({-# LINE 654 "Syntax/UHA_Pretty.ag" #-}
              \assign ->
                  (   PPrint.empty
                  <$> vsep
                         (zipWith (\f x -> indent 4 (f x)) _guardedexpressionsItext (repeat assign))
                  <>  maybe
                         empty
                         (\ds -> PPrint.empty <$> indent 4 (text "where" <$> indent 4 (vcat ds)))
                         _whereItext
                  )
              {-# LINE 3996 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 81 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4001 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _guardedexpressionsItext) =
             guardedexpressions_
         ( _whereItext) =
             where_
     in  ( _lhsOtext))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType ->
                  T_SimpleType
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables) =
    (sem_SimpleType_SimpleType (sem_Range _range) (sem_Name _name) (sem_Names _typevariables))
-- semantic domain
type T_SimpleType = ( Doc)
sem_SimpleType_SimpleType :: T_Range ->
                             T_Name ->
                             T_Names ->
                             T_SimpleType
sem_SimpleType_SimpleType range_ name_ typevariables_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _typevariablesIisIdentifier :: ( [Bool] )
         _typevariablesIisOperator :: ( [Bool] )
         _typevariablesIisSpecial :: ( [Bool] )
         _typevariablesItext :: ( [       Doc ] )
         _text =
             ({-# LINE 399 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) _nameItext _typevariablesItext
              {-# LINE 4036 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4041 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
         ( _typevariablesIisIdentifier,_typevariablesIisOperator,_typevariablesIisSpecial,_typevariablesItext) =
             typevariables_
     in  ( _lhsOtext))
-- Statement ---------------------------------------------------
-- cata
sem_Statement :: Statement ->
                 T_Statement
sem_Statement (Statement_Empty _range) =
    (sem_Statement_Empty (sem_Range _range))
sem_Statement (Statement_Expression _range _expression) =
    (sem_Statement_Expression (sem_Range _range) (sem_Expression _expression))
sem_Statement (Statement_Generator _range _pattern _expression) =
    (sem_Statement_Generator (sem_Range _range) (sem_Pattern _pattern) (sem_Expression _expression))
sem_Statement (Statement_Let _range _declarations) =
    (sem_Statement_Let (sem_Range _range) (sem_Declarations _declarations))
-- semantic domain
type T_Statement = ( Doc)
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _text =
             ({-# LINE 565 "Syntax/UHA_Pretty.ag" #-}
              empty
              {-# LINE 4072 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4077 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
     in  ( _lhsOtext))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 555 "Syntax/UHA_Pretty.ag" #-}
              _expressionItext
              {-# LINE 4092 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4097 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _patternItext :: Doc
         _expressionItext :: Doc
         _text =
             ({-# LINE 561 "Syntax/UHA_Pretty.ag" #-}
              _patternItext <+> text "<-" <+> _expressionItext
              {-# LINE 4116 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4121 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _patternItext) =
             pattern_
         ( _expressionItext) =
             expression_
     in  ( _lhsOtext))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _declarationsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 558 "Syntax/UHA_Pretty.ag" #-}
              text "let" <$> (indent 4 $ vcat _declarationsItext)
              {-# LINE 4140 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4145 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _declarationsItext) =
             declarations_
     in  ( _lhsOtext))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list))
-- semantic domain
type T_Statements = ( ( [       Doc ] ))
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 4170 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 4183 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings ->
               T_Strings
sem_Strings list =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list)
-- semantic domain
type T_Strings = ( ( [       Doc ] ))
sem_Strings_Cons :: String ->
                    T_Strings ->
                    T_Strings
sem_Strings_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _tlItext
              {-# LINE 4203 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Strings_Nil :: T_Strings
sem_Strings_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 4214 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))
-- Type --------------------------------------------------------
-- cata
sem_Type :: Type ->
            T_Type
sem_Type (Type_Application _range _prefix _function _arguments) =
    (sem_Type_Application (sem_Range _range) _prefix (sem_Type _function) (sem_Types _arguments))
sem_Type (Type_Constructor _range _name) =
    (sem_Type_Constructor (sem_Range _range) (sem_Name _name))
sem_Type (Type_Exists _range _typevariables _type) =
    (sem_Type_Exists (sem_Range _range) (sem_Names _typevariables) (sem_Type _type))
sem_Type (Type_Forall _range _typevariables _type) =
    (sem_Type_Forall (sem_Range _range) (sem_Names _typevariables) (sem_Type _type))
sem_Type (Type_Parenthesized _range _type) =
    (sem_Type_Parenthesized (sem_Range _range) (sem_Type _type))
sem_Type (Type_Qualified _range _context _type) =
    (sem_Type_Qualified (sem_Range _range) (sem_ContextItems _context) (sem_Type _type))
sem_Type (Type_Variable _range _name) =
    (sem_Type_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Type = ( Doc)
sem_Type_Application :: T_Range ->
                        Bool ->
                        T_Type ->
                        T_Types ->
                        T_Type
sem_Type_Application range_ prefix_ function_ arguments_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _functionItext :: Doc
         _argumentsItext :: ( [       Doc ] )
         _text =
             ({-# LINE 360 "Syntax/UHA_Pretty.ag" #-}
              if prefix_ then
                  foldl (<+>) _functionItext _argumentsItext
              else if show _functionItext == "[]" then
                  PPrint.list _argumentsItext
              else if isTupleConstructor (show _functionItext) then
                  tupled _argumentsItext
              else
                  case _argumentsItext of
                      [a, b] -> a <+> _functionItext <+> b
                      _      -> text "{- error: Unknown special application notation -}"
              {-# LINE 4259 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4264 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _functionItext) =
             function_
         ( _argumentsItext) =
             arguments_
     in  ( _lhsOtext))
sem_Type_Constructor :: T_Range ->
                        T_Name ->
                        T_Type
sem_Type_Constructor range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 377 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 4286 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4291 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
sem_Type_Exists :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Exists range_ typevariables_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _typevariablesIisIdentifier :: ( [Bool] )
         _typevariablesIisOperator :: ( [Bool] )
         _typevariablesIisSpecial :: ( [Bool] )
         _typevariablesItext :: ( [       Doc ] )
         _typeItext :: Doc
         _text =
             ({-# LINE 390 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (text "exists") _typevariablesItext <> text "." <> _typeItext
              {-# LINE 4313 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4318 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _typevariablesIisIdentifier,_typevariablesIisOperator,_typevariablesIisSpecial,_typevariablesItext) =
             typevariables_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Type_Forall :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Forall range_ typevariables_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _typevariablesIisIdentifier :: ( [Bool] )
         _typevariablesIisOperator :: ( [Bool] )
         _typevariablesIisSpecial :: ( [Bool] )
         _typevariablesItext :: ( [       Doc ] )
         _typeItext :: Doc
         _text =
             ({-# LINE 386 "Syntax/UHA_Pretty.ag" #-}
              foldl (<+>) (text "forall") _typevariablesItext <> text "." <> _typeItext
              {-# LINE 4342 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4347 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _typevariablesIisIdentifier,_typevariablesIisOperator,_typevariablesIisSpecial,_typevariablesItext) =
             typevariables_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Type_Parenthesized :: T_Range ->
                          T_Type ->
                          T_Type
sem_Type_Parenthesized range_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _typeItext :: Doc
         _text =
             ({-# LINE 394 "Syntax/UHA_Pretty.ag" #-}
              parens _typeItext
              {-# LINE 4366 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4371 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Type_Qualified :: T_Range ->
                      T_ContextItems ->
                      T_Type ->
                      T_Type
sem_Type_Qualified range_ context_ type_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _contextItext :: ( [       Doc ] )
         _typeItext :: Doc
         _text =
             ({-# LINE 380 "Syntax/UHA_Pretty.ag" #-}
              case _contextItext of
                [ct] -> ct <+> text "=>" <+> _typeItext
                cts -> parens (commas cts) <+> text "=>" <+> _typeItext
              {-# LINE 4392 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4397 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _contextItext) =
             context_
         ( _typeItext) =
             type_
     in  ( _lhsOtext))
sem_Type_Variable :: T_Range ->
                     T_Name ->
                     T_Type
sem_Type_Variable range_ name_ =
    (let _lhsOtext :: Doc
         _rangeItext :: Doc
         _nameIisIdentifier :: Bool
         _nameIisOperator :: Bool
         _nameIisSpecial :: Bool
         _nameItext :: Doc
         _text =
             ({-# LINE 374 "Syntax/UHA_Pretty.ag" #-}
              _nameItext
              {-# LINE 4419 "Syntax/UHA_Pretty.hs" #-}
              )
         _lhsOtext =
             ({-# LINE 75 "Syntax/UHA_Pretty.ag" #-}
              _text
              {-# LINE 4424 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _rangeItext) =
             range_
         ( _nameIisIdentifier,_nameIisOperator,_nameIisSpecial,_nameItext) =
             name_
     in  ( _lhsOtext))
-- Types -------------------------------------------------------
-- cata
sem_Types :: Types ->
             T_Types
sem_Types list =
    (Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list))
-- semantic domain
type T_Types = ( ( [       Doc ] ))
sem_Types_Cons :: T_Type ->
                  T_Types ->
                  T_Types
sem_Types_Cons hd_ tl_ =
    (let _lhsOtext :: ( [       Doc ] )
         _hdItext :: Doc
         _tlItext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              _hdItext  :  _tlItext
              {-# LINE 4449 "Syntax/UHA_Pretty.hs" #-}
              )
         ( _hdItext) =
             hd_
         ( _tlItext) =
             tl_
     in  ( _lhsOtext))
sem_Types_Nil :: T_Types
sem_Types_Nil =
    (let _lhsOtext :: ( [       Doc ] )
         _lhsOtext =
             ({-# LINE 97 "Syntax/UHA_Pretty.ag" #-}
              []
              {-# LINE 4462 "Syntax/UHA_Pretty.hs" #-}
              )
     in  ( _lhsOtext))