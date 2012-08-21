
-- UUAGC 0.9.5 (CodeGeneration.ag)
module CodeGeneration where

import UHA_Syntax
import UHA_Utils
import UHA_Range 
import ImportEnvironment
import DictionaryEnvironment
import qualified Data.Map as M
import TypeConversion
import Data.Char (ord)

import Lvm.Common.Id
import Lvm.Common.IdSet 
import Utils(internalError)

import Top.Types

import PatternMatch
import DerivingShow
import DerivingEq

-- Semi-Daan
import CoreUtils

-- Daan
import qualified Lvm.Core.Core as Core
import qualified Lvm.Module as Module
import qualified Lvm.Common.Byte as Byte


import Lvm.Common.Byte(bytesFromString)


type CoreDecl = Core.Decl Core.Expr


makeCoreModule name decls =
    Module.Module
        { Module.moduleName   =
            case name of
                Nothing -> idFromString "Main"
                Just n -> n
        , Module.moduleMajorVer = 0
        , Module.moduleMinorVer = 0
        , Module.moduleDecls    = decls
        }

interpreterMain = "interpreter_main"

-- Unfortunately we need a hack for the interpreter
-- The interpreter_main has te be wrapped inside unsafePerformIO etcetera, too
-- We can't just call it main because we'll get import clashes.  Sigh!

insertedMain :: TypeEnvironment -> CoreDecl
insertedMain toplevelTypes =
    let maybeWrapMainAndType = 
            case M.lookup (Name_Identifier noRange [] "main") toplevelTypes of -- !!!Name
                Just t -> Just ("main", t)
                Nothing ->
                    case M.lookup (Name_Identifier noRange [] interpreterMain) toplevelTypes of -- !!!Name
                        Just t -> Just (interpreterMain, t)
                        Nothing -> Nothing
    in
    decl False "main$" $
        app_ unsafePIO $
            case maybeWrapMainAndType of 
                Nothing -> 
                    var "$primPutStrLn" `app_` 
                        (var "$primPackedToString" `app_`
                            packedString "No 'main' function defined in this module")
                Just (name, tpScheme)
                    | not (null qs) ->
                        var "$primPutStrLn" `app_` 
                            (var "$primPackedToString" `app_`
                                packedString "<<overloaded function>>")
                    | isIOType tp -> 
                        var name
                    | otherwise ->
                        var "$primPutStrLn" `app_` 
                            (showFunctionOfType True (makeTypeFromTp tp) `app_` 
                                var name)
                    where                        
                        (qs, tp) = split (snd (instantiate 123456789 tpScheme))
    where
        unsafePIO = var "$primUnsafePerformIO"    
                


-- set the public bit of all declarations except those that are imported from
-- Prelude or HeliumLang. I.e. export everything everywhere
everythingPublicButPrelude :: Core.CoreModule -> Core.CoreModule
everythingPublicButPrelude mod = mod { Core.moduleDecls = map setPublic (Core.moduleDecls mod) }
  where
    setPublic decl = 
        let -- accessRecord = Core.declAccess decl
            public = case Core.declAccess decl of 
                    Core.Defined _ -> True
                    Core.Imported { Core.importModule = m } -> 
                        stringFromId m `notElem` ["Prelude", "HeliumLang"] 
        in 
        decl{ Core.declAccess = 
                  (Core.declAccess decl){ Core.accessPublic = public } }


predicateToId :: Predicate -> Id
predicateToId (Predicate class_ tp) =
    idFromString $ "$dict" ++ class_ ++ show tp
    
dictionaryTreeToCore :: DictionaryTree -> Core.Expr
dictionaryTreeToCore tree = 
   case tree of
      ByPredicate predicate -> 
         Core.Var (predicateToId predicate)
      ByInstance className instanceName trees ->
         foldl Core.Ap
               (Core.Var (idFromString ("$dict"++className++instanceName)))
               (map dictionaryTreeToCore trees)
      BySuperClass subClass superClass tree -> 
         Core.Ap (Core.Var (idFromString ("$get" ++ superClass ++ "From" ++ subClass)))          
                 (dictionaryTreeToCore tree)

insertDictionaries :: Name -> DictionaryEnvironment -> Core.Expr
insertDictionaries name dictionaryEnv = 
   foldl Core.Ap
         (Core.Var (idFromName name))
         (map dictionaryTreeToCore (getDictionaryTrees name dictionaryEnv))


toplevelType :: Name -> ImportEnvironment -> Bool -> [Core.Custom]
toplevelType name ie isTopLevel
    | isTopLevel = [custom "type" typeString]
    | otherwise  = []
    where
        typeString = maybe
            (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
            show
            (M.lookup name (typeEnvironment ie))

constructorCustoms :: Name -> Name -> ValueConstructorEnvironment -> [Core.Custom]
constructorCustoms dataTypeName name env =
    maybe 
        (internalError "ToCoreDecl" "Constructor" ("no type found for " ++ show name))
        (\tpScheme -> 
            [ custom "type" (show tpScheme)
            , Core.CustomLink 
                    (idFromName dataTypeName) 
                    (Core.DeclKindCustom (idFromString "data"))
            ]
        )
        (M.lookup name env)



-- Function "bind" is used in the translation of do-expressions
bind :: Core.Expr -> Core.Expr -> Core.Expr
bind ma f = Core.Var primBindIOId `app_` ma `app_` f

( primBindIOId :  caseExprId :  okId :  parameterId : []) = map idFromString $
 "$primBindIO"  : "caseExpr$" : "ok$" : "parameter$" : []

-- Function "chainCode" is used in the translation of do-expressions
chainCode :: [Maybe Core.Expr -> Core.Expr] -> Core.Expr
chainCode cores =
    case cores of
        [core] -> core Nothing
        (core:cores) -> core (Just (chainCode cores))



patternAlwaysSucceeds :: Pattern -> Bool
patternAlwaysSucceeds p = 
    case p of
        Pattern_Variable _ _ -> True
        Pattern_Wildcard _ -> True
        Pattern_As _ _ p -> patternAlwaysSucceeds p
        Pattern_Parenthesized _ p -> patternAlwaysSucceeds p
        _ -> False

patternMatchFail :: String -> Range -> Core.Expr
patternMatchFail nodeDescription range =
    var "$primPatternFailPacked"
        `app_` packedString (
                    nodeDescription ++ " ranging from " ++ 
                    showPosition start ++ " to " ++ 
                    showPosition (getRangeEnd range) ++ " in module " ++
                    moduleFromPosition start
               )
    where
        start = getRangeStart range
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside )  =
    (sem_Alternative_Alternative (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Alternative (Alternative_Empty _range )  =
    (sem_Alternative_Empty (sem_Range _range ) )
-- semantic domain
type T_Alternative = DictionaryEnvironment ->
                     ( ( Core.Expr -> Core.Expr ),Alternative)
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Alternative
              _righthandsideOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _patternIself :: Pattern
              _patternIvars :: ( [Name] )
              _righthandsideIcore :: ( Core.Expr )
              _righthandsideIisGuarded :: Bool
              _righthandsideIself :: RightHandSide
              _lhsOcore =
                  \nextCase  ->
                     let thisCase =
                             patternToCore
                                 (caseExprId, _patternIself)
                                 _righthandsideIcore
                     in
                         let_ nextClauseId nextCase thisCase
              _self =
                  Alternative_Alternative _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _righthandsideOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _patternIself,_patternIvars) =
                  (pattern_ )
              ( _righthandsideIcore,_righthandsideIisGuarded,_righthandsideIself) =
                  (righthandside_ _righthandsideOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Alternative
              _rangeIself :: Range
              _lhsOcore =
                  id
              _self =
                  Alternative_Empty _rangeIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcore,_lhsOself)))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list  =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list) )
-- semantic domain
type T_Alternatives = Range ->
                      DictionaryEnvironment ->
                      ( ( Core.Expr ),Alternatives)
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_  =
    (\ _lhsIcaseRange
       _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Alternatives
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOcaseRange :: Range
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIcore :: ( Core.Expr -> Core.Expr )
              _hdIself :: Alternative
              _tlIcore :: ( Core.Expr )
              _tlIself :: Alternatives
              _lhsOcore =
                  _hdIcore _tlIcore
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOcaseRange =
                  _lhsIcaseRange
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIcore,_hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIcore,_tlIself) =
                  (tl_ _tlOcaseRange _tlOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil  =
    (\ _lhsIcaseRange
       _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Alternatives
              _lhsOcore =
                  patternMatchFail "case expression" _lhsIcaseRange
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
type T_AnnotatedTypes = ( Int,AnnotatedTypes)
sem_AnnotatedTypes_Cons :: T_AnnotatedType ->
                           T_AnnotatedTypes ->
                           T_AnnotatedTypes
sem_AnnotatedTypes_Cons hd_ tl_  =
    (let _lhsOlength :: Int
         _lhsOself :: AnnotatedTypes
         _hdIself :: AnnotatedType
         _tlIlength :: Int
         _tlIself :: AnnotatedTypes
         _lhsOlength =
             1 + _tlIlength
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIlength,_tlIself) =
             (tl_ )
     in  ( _lhsOlength,_lhsOself))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes
sem_AnnotatedTypes_Nil  =
    (let _lhsOlength :: Int
         _lhsOself :: AnnotatedTypes
         _lhsOlength =
             0
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOlength,_lhsOself))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body ->
            T_Body
sem_Body (Body_Body _range _importdeclarations _declarations )  =
    (sem_Body_Body (sem_Range _range ) (sem_ImportDeclarations _importdeclarations ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Body = DictionaryEnvironment ->
              ImportEnvironment ->
              ( ( [CoreDecl] ),Body)
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _declarationsOpatBindNr :: Int
              _declarationsOisTopLevel :: Bool
              _lhsOself :: Body
              _declarationsOdictionaryEnv :: DictionaryEnvironment
              _declarationsOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _importdeclarationsIself :: ImportDeclarations
              _declarationsIdecls :: ( [CoreDecl] )
              _declarationsIpatBindNr :: Int
              _declarationsIself :: Declarations
              _lhsOdecls =
                  _declarationsIdecls
              _declarationsOpatBindNr =
                  0
              _declarationsOisTopLevel =
                  True
              _self =
                  Body_Body _rangeIself _importdeclarationsIself _declarationsIself
              _lhsOself =
                  _self
              _declarationsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _declarationsOimportEnv =
                  _lhsIimportEnv
              ( _rangeIself) =
                  (range_ )
              ( _importdeclarationsIself) =
                  (importdeclarations_ )
              ( _declarationsIdecls,_declarationsIpatBindNr,_declarationsIself) =
                  (declarations_ _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr )
          in  ( _lhsOdecls,_lhsOself)))
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
type T_Constructor = Name ->
                     DictionaryEnvironment ->
                     ImportEnvironment ->
                     Int ->
                     ( ( [(Id, CoreDecl)] ),Constructor)
sem_Constructor_Constructor :: T_Range ->
                               T_Name ->
                               T_AnnotatedTypes ->
                               T_Constructor
sem_Constructor_Constructor range_ constructor_ types_  =
    (\ _lhsIdataTypeName
       _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsItag ->
         (let _lhsOcons :: ( [(Id, CoreDecl)] )
              _lhsOself :: Constructor
              _rangeIself :: Range
              _constructorIself :: Name
              _typesIlength :: Int
              _typesIself :: AnnotatedTypes
              _lhsOcons =
                  [ (idFromName _constructorIself, Core.DeclCon
                      { Core.declName    = idFromName _constructorIself
                      , Core.declAccess  = Core.private
                      , Core.declArity   = _typesIlength
                      , Core.conTag      = _lhsItag
                      , Core.declCustoms = constructorCustoms
                                              _lhsIdataTypeName
                                              _constructorIself
                                              (valueConstructors _lhsIimportEnv)
                      }
                    )
                  ]
              _self =
                  Constructor_Constructor _rangeIself _constructorIself _typesIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _typesIlength,_typesIself) =
                  (types_ )
          in  ( _lhsOcons,_lhsOself)))
sem_Constructor_Infix :: T_Range ->
                         T_AnnotatedType ->
                         T_Name ->
                         T_AnnotatedType ->
                         T_Constructor
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_  =
    (\ _lhsIdataTypeName
       _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsItag ->
         (let _lhsOcons :: ( [(Id, CoreDecl)] )
              _lhsOself :: Constructor
              _rangeIself :: Range
              _leftTypeIself :: AnnotatedType
              _constructorOperatorIself :: Name
              _rightTypeIself :: AnnotatedType
              _lhsOcons =
                  [ (idFromName _constructorOperatorIself, Core.DeclCon
                      { Core.declName    = idFromName _constructorOperatorIself
                      , Core.declAccess  = Core.private
                      , Core.declArity   = 2
                      , Core.conTag      = _lhsItag
                      , Core.declCustoms = constructorCustoms
                                              _lhsIdataTypeName
                                              _constructorOperatorIself
                                              (valueConstructors _lhsIimportEnv)
                      }
                    )
                  ]
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
          in  ( _lhsOcons,_lhsOself)))
sem_Constructor_Record :: T_Range ->
                          T_Name ->
                          T_FieldDeclarations ->
                          T_Constructor
sem_Constructor_Record range_ constructor_ fieldDeclarations_  =
    (\ _lhsIdataTypeName
       _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsItag ->
         (let _lhsOcons :: ( [(Id, CoreDecl)] )
              _lhsOself :: Constructor
              _rangeIself :: Range
              _constructorIself :: Name
              _fieldDeclarationsIself :: FieldDeclarations
              _lhsOcons =
                  internalError "ToCoreDecl" "Constructor" "records not supported"
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
          in  ( _lhsOcons,_lhsOself)))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors ->
                    T_Constructors
sem_Constructors list  =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list) )
-- semantic domain
type T_Constructors = Name ->
                      DictionaryEnvironment ->
                      ImportEnvironment ->
                      Int ->
                      ( ( [(Id, CoreDecl)] ),Constructors)
sem_Constructors_Cons :: T_Constructor ->
                         T_Constructors ->
                         T_Constructors
sem_Constructors_Cons hd_ tl_  =
    (\ _lhsIdataTypeName
       _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsItag ->
         (let _hdOtag :: Int
              _tlOtag :: Int
              _lhsOcons :: ( [(Id, CoreDecl)] )
              _lhsOself :: Constructors
              _hdOdataTypeName :: Name
              _hdOdictionaryEnv :: DictionaryEnvironment
              _hdOimportEnv :: ImportEnvironment
              _tlOdataTypeName :: Name
              _tlOdictionaryEnv :: DictionaryEnvironment
              _tlOimportEnv :: ImportEnvironment
              _hdIcons :: ( [(Id, CoreDecl)] )
              _hdIself :: Constructor
              _tlIcons :: ( [(Id, CoreDecl)] )
              _tlIself :: Constructors
              _hdOtag =
                  _lhsItag
              _tlOtag =
                  _lhsItag + 1
              _lhsOcons =
                  _hdIcons  ++  _tlIcons
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdataTypeName =
                  _lhsIdataTypeName
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _hdOimportEnv =
                  _lhsIimportEnv
              _tlOdataTypeName =
                  _lhsIdataTypeName
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOimportEnv =
                  _lhsIimportEnv
              ( _hdIcons,_hdIself) =
                  (hd_ _hdOdataTypeName _hdOdictionaryEnv _hdOimportEnv _hdOtag )
              ( _tlIcons,_tlIself) =
                  (tl_ _tlOdataTypeName _tlOdictionaryEnv _tlOimportEnv _tlOtag )
          in  ( _lhsOcons,_lhsOself)))
sem_Constructors_Nil :: T_Constructors
sem_Constructors_Nil  =
    (\ _lhsIdataTypeName
       _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsItag ->
         (let _lhsOcons :: ( [(Id, CoreDecl)] )
              _lhsOself :: Constructors
              _lhsOcons =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcons,_lhsOself)))
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
type T_Declaration = DictionaryEnvironment ->
                     ImportEnvironment ->
                     Bool ->
                     Int ->
                     ( ( [CoreDecl] ),Int,Declaration)
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _whereOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _whereIcore :: ( Core.Expr -> Core.Expr )
              _whereIself :: MaybeDeclarations
              _lhsOdecls =
                  internalError "ToCoreDecl" "Declaration" "'class' not supported"
              _self =
                  Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              _whereOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _whereIcore,_whereIself) =
                  (where_ _whereOdictionaryEnv )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _constructorsOtag :: Int
              _constructorsOdataTypeName :: Name
              _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _constructorsOdictionaryEnv :: DictionaryEnvironment
              _constructorsOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorsIcons :: ( [(Id, CoreDecl)] )
              _constructorsIself :: Constructors
              _derivingsInames :: ([Name])
              _derivingsIself :: Names
              _constructorsOtag =
                  0
              _constructorsOdataTypeName =
                  _simpletypeIname
              _lhsOdecls =
                  map snd _constructorsIcons
                  ++
                  [ Core.DeclCustom
                      { Core.declName    = idFromString (getNameName _simpletypeIname)
                      , Core.declAccess  = Core.private
                      , Core.declKind    = Core.DeclKindCustom (idFromString "data")
                      , Core.declCustoms = [Core.CustomInt (length _simpletypeItypevariables)]
                      }
                  ]
                  ++
                  [ DerivingShow.dataShowFunction _self ]
                  ++
                  (if "Show" `elem` map show _derivingsIself
                   then [ DerivingShow.dataDictionary _self ]
                   else []
                  )
                  ++
                  (if "Eq" `elem` map show _derivingsIself
                   then [ DerivingEq.dataDictionary _self ]
                   else []
                  )
              _self =
                  Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              _constructorsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _constructorsOimportEnv =
                  _lhsIimportEnv
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorsIcons,_constructorsIself) =
                  (constructors_ _constructorsOdataTypeName _constructorsOdictionaryEnv _constructorsOimportEnv _constructorsOtag )
              ( _derivingsInames,_derivingsIself) =
                  (derivings_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _rangeIself :: Range
              _typesIself :: Types
              _lhsOdecls =
                  internalError "ToCoreDecl" "Declaration" "'default' not supported"
              _self =
                  Declaration_Default _rangeIself _typesIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              ( _rangeIself) =
                  (range_ )
              ( _typesIself) =
                  (types_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _rangeIself :: Range
              _lhsOdecls =
                  internalError "ToCoreDecl" "Declaration" "empty declarations not supported"
              _self =
                  Declaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _rangeIself :: Range
              _fixityIself :: Fixity
              _priorityIself :: MaybeInt
              _operatorsInames :: ([Name])
              _operatorsIself :: Names
              _lhsOdecls =
                  map
                      ( ( \n ->
                          Core.DeclCustom
                              { Core.declName    = idFromString n
                              , Core.declAccess  = Core.private
                              , Core.declKind    = (Core.DeclKindCustom . idFromString) "infix"
                              , Core.declCustoms =
                                  [ Core.CustomInt
                                       ( case _priorityIself of
                                            MaybeInt_Just i  -> i
                                            MaybeInt_Nothing -> 9 )
                                  , (Core.CustomBytes . bytesFromString)
                                        ( case _fixityIself of
                                             Fixity_Infixr _ -> "right"
                                             Fixity_Infixl _ -> "left"
                                             Fixity_Infix  _ -> "none"
                                             _               -> internalError
                                                                  "ToCoreDecl.ag"
                                                                  "SEM Declaration.Fixity"
                                                                  "unknown fixity"
                                        )
                                  ]
                              }
                        )
                        .
                        getNameName
                      )
                      _operatorsIself
              _self =
                  Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              ( _rangeIself) =
                  (range_ )
              ( _fixityIself) =
                  (fixity_ )
              ( _priorityIself) =
                  (priority_ )
              ( _operatorsInames,_operatorsIself) =
                  (operators_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _bindingsOids :: ( [Id] )
              _bindingsOrange :: Range
              _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _bindingsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _bindingsIarity :: Int
              _bindingsIcore :: (Core.Expr)
              _bindingsIname :: Name
              _bindingsIself :: FunctionBindings
              _ids =
                  freshIds "u$" _bindingsIarity
              _bindingsOids =
                  _ids
              _bindingsOrange =
                  _rangeIself
              _dictionaries =
                  map predicateToId
                     (getPredicateForDecl _bindingsIname _lhsIdictionaryEnv)
              _lhsOdecls =
                  [ Core.DeclValue
                      { Core.declName    = idFromName _bindingsIname
                      , Core.declAccess  = Core.private
                      , Core.valueEnc    = Nothing
                      , Core.valueValue  = foldr Core.Lam _bindingsIcore (_dictionaries ++ _ids)
                      , Core.declCustoms = toplevelType _bindingsIname _lhsIimportEnv _lhsIisTopLevel
                      }
                  ]
              _self =
                  Declaration_FunctionBindings _rangeIself _bindingsIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              _bindingsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _bindingsIarity,_bindingsIcore,_bindingsIname,_bindingsIself) =
                  (bindings_ _bindingsOdictionaryEnv _bindingsOids _bindingsOrange )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _whereOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _contextIself :: ContextItems
              _nameIself :: Name
              _typesIself :: Types
              _whereIcore :: ( Core.Expr -> Core.Expr )
              _whereIself :: MaybeDeclarations
              _lhsOdecls =
                  internalError "ToCoreDecl" "Declaration" "'instance' not supported"
              _self =
                  Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              _whereOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _nameIself) =
                  (name_ )
              ( _typesIself) =
                  (types_ )
              ( _whereIcore,_whereIself) =
                  (where_ _whereOdictionaryEnv )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _constructorOtag :: Int
              _constructorOdataTypeName :: Name
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _constructorOdictionaryEnv :: DictionaryEnvironment
              _constructorOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorIcons :: ( [(Id, CoreDecl)] )
              _constructorIself :: Constructor
              _derivingsInames :: ([Name])
              _derivingsIself :: Names
              _lhsOdecls =
                  internalError "ToCoreDecl" "Declaration" "'newType' not supported"
              _constructorOtag =
                  0
              _constructorOdataTypeName =
                  _simpletypeIname
              _self =
                  Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              _constructorOdictionaryEnv =
                  _lhsIdictionaryEnv
              _constructorOimportEnv =
                  _lhsIimportEnv
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorIcons,_constructorIself) =
                  (constructor_ _constructorOdataTypeName _constructorOdictionaryEnv _constructorOimportEnv _constructorOtag )
              ( _derivingsInames,_derivingsIself) =
                  (derivings_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOpatBindNr :: Int
              _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _righthandsideOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _patternIself :: Pattern
              _patternIvars :: ( [Name] )
              _righthandsideIcore :: ( Core.Expr )
              _righthandsideIisGuarded :: Bool
              _righthandsideIself :: RightHandSide
              _lhsOpatBindNr =
                  _lhsIpatBindNr + 1
              _dictionaries =
                  case _patternIself of
                      Pattern_Variable _ n ->
                         map predicateToId
                            (getPredicateForDecl n _lhsIdictionaryEnv)
                      _ -> []
              _lhsOdecls =
                  case _patternIself of
                      Pattern_Variable _ n ->
                          [ Core.DeclValue
                              { Core.declName    = idFromName n
                              , Core.declAccess  = Core.private
                              , Core.valueEnc    = Nothing
                              , Core.valueValue  =
                                  foldr Core.Lam
                                      ( let_
                                          nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                                          _righthandsideIcore
                                      )
                                      _dictionaries
                              , Core.declCustoms = toplevelType n _lhsIimportEnv _lhsIisTopLevel
                              }
                         ]
                      _ ->
                          Core.DeclValue
                              { Core.declName    = patBindId
                              , Core.declAccess  = Core.private
                              , Core.valueEnc    = Nothing
                              , Core.valueValue  =
                                  let_
                                      nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                                      _righthandsideIcore
                              , Core.declCustoms = [custom "type" "patternbinding"]
                              }
                          :
                          [ Core.DeclValue
                              { Core.declName    = idFromName v
                              , Core.declAccess  = Core.private
                              , Core.valueEnc    = Nothing
                              , Core.valueValue  =
                                  (let_ nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                                      (patternToCore (patBindId, _patternIself) (Core.Var (idFromName v)))
                                  )
                              , Core.declCustoms = toplevelType v _lhsIimportEnv _lhsIisTopLevel
                              }
                          | v <- _patternIvars
                          ]
                          where
                              patBindId = idFromString ("patBind$" ++ show _lhsIpatBindNr)
              _self =
                  Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _righthandsideOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _patternIself,_patternIvars) =
                  (pattern_ )
              ( _righthandsideIcore,_righthandsideIisGuarded,_righthandsideIself) =
                  (righthandside_ _righthandsideOdictionaryEnv )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _rangeIself :: Range
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _typeIself :: Type
              _lhsOdecls =
                  let
                      (t1,[t2])   = convertFromSimpleTypeAndTypes _simpletypeIself [_typeIself]
                      allTypeVars = ftv [t1,t2]
                      (ts1,ts2)   = ( Quantification (allTypeVars, [], [] .=>. t1) :: TpScheme
                                    , Quantification (allTypeVars, [], [] .=>. t2) :: TpScheme
                                    )
                  in
                  [ Core.DeclCustom
                      { Core.declName    = idFromString (getNameName _simpletypeIname)
                      , Core.declAccess  = Core.private
                      , Core.declKind    = Core.DeclKindCustom (idFromString "typedecl")
                      , Core.declCustoms =
                          [ Core.CustomBytes
                              (Byte.bytesFromString
                                  (  show ts1
                                  ++ " = "
                                  ++ show ts2
                                  )
                              )
                          , Core.CustomInt
                              (length _simpletypeItypevariables)
                          ]
                      }
                  ]
                  ++
                  [ DerivingShow.typeShowFunction _self ]
              _self =
                  Declaration_Type _rangeIself _simpletypeIself _typeIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              ( _rangeIself) =
                  (range_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declaration
              _lhsOpatBindNr :: Int
              _rangeIself :: Range
              _namesInames :: ([Name])
              _namesIself :: Names
              _typeIself :: Type
              _lhsOdecls =
                  []
              _self =
                  Declaration_TypeSignature _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
              ( _rangeIself) =
                  (range_ )
              ( _namesInames,_namesIself) =
                  (names_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list  =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list) )
-- semantic domain
type T_Declarations = DictionaryEnvironment ->
                      ImportEnvironment ->
                      Bool ->
                      Int ->
                      ( ( [CoreDecl] ),Int,Declarations)
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declarations
              _lhsOpatBindNr :: Int
              _hdOdictionaryEnv :: DictionaryEnvironment
              _hdOimportEnv :: ImportEnvironment
              _hdOisTopLevel :: Bool
              _hdOpatBindNr :: Int
              _tlOdictionaryEnv :: DictionaryEnvironment
              _tlOimportEnv :: ImportEnvironment
              _tlOisTopLevel :: Bool
              _tlOpatBindNr :: Int
              _hdIdecls :: ( [CoreDecl] )
              _hdIpatBindNr :: Int
              _hdIself :: Declaration
              _tlIdecls :: ( [CoreDecl] )
              _tlIpatBindNr :: Int
              _tlIself :: Declarations
              _lhsOdecls =
                  _hdIdecls  ++  _tlIdecls
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _tlIpatBindNr
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _hdOimportEnv =
                  _lhsIimportEnv
              _hdOisTopLevel =
                  _lhsIisTopLevel
              _hdOpatBindNr =
                  _lhsIpatBindNr
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOimportEnv =
                  _lhsIimportEnv
              _tlOisTopLevel =
                  _lhsIisTopLevel
              _tlOpatBindNr =
                  _hdIpatBindNr
              ( _hdIdecls,_hdIpatBindNr,_hdIself) =
                  (hd_ _hdOdictionaryEnv _hdOimportEnv _hdOisTopLevel _hdOpatBindNr )
              ( _tlIdecls,_tlIpatBindNr,_tlIself) =
                  (tl_ _tlOdictionaryEnv _tlOimportEnv _tlOisTopLevel _tlOpatBindNr )
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil  =
    (\ _lhsIdictionaryEnv
       _lhsIimportEnv
       _lhsIisTopLevel
       _lhsIpatBindNr ->
         (let _lhsOdecls :: ( [CoreDecl] )
              _lhsOself :: Declarations
              _lhsOpatBindNr :: Int
              _lhsOdecls =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOpatBindNr =
                  _lhsIpatBindNr
          in  ( _lhsOdecls,_lhsOpatBindNr,_lhsOself)))
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
type T_Export = ( IdSet,IdSet,Export,IdSet,IdSet)
sem_Export_Module :: T_Range ->
                     T_Name ->
                     T_Export
sem_Export_Module range_ name_  =
    (let _lhsOvalues :: IdSet
         _lhsOtypes :: IdSet
         _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOvalues =
             emptySet
         _lhsOtypes =
             emptySet
         _lhsOcons =
             emptySet
         _lhsOmods =
             singleSet (idFromName _nameIself)
         _self =
             Export_Module _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
sem_Export_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Export
sem_Export_TypeOrClass range_ name_ names_  =
    (let _lhsOvalues :: IdSet
         _lhsOtypes :: IdSet
         _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _namesInames :: ( Maybe [Name] )
         _namesIself :: MaybeNames
         _lhsOvalues =
             emptySet
         _lhsOtypes =
             singleSet (idFromName _nameIself)
         _lhsOcons =
             setFromList (maybe [] (map idFromName) _namesInames)
         _lhsOmods =
             emptySet
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
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
sem_Export_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Export
sem_Export_TypeOrClassComplete range_ name_  =
    (let _lhsOvalues :: IdSet
         _lhsOtypes :: IdSet
         _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOvalues =
             internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
         _lhsOtypes =
             internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
         _lhsOcons =
             internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
         _lhsOmods =
             internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
         _self =
             Export_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
sem_Export_Variable :: T_Range ->
                       T_Name ->
                       T_Export
sem_Export_Variable range_ name_  =
    (let _lhsOvalues :: IdSet
         _lhsOtypes :: IdSet
         _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOvalues =
             singleSet (idFromName _nameIself)
         _lhsOtypes =
             emptySet
         _lhsOcons =
             emptySet
         _lhsOmods =
             emptySet
         _self =
             Export_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports ->
               T_Exports
sem_Exports list  =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list) )
-- semantic domain
type T_Exports = ( IdSet,IdSet,Exports,IdSet,IdSet)
sem_Exports_Cons :: T_Export ->
                    T_Exports ->
                    T_Exports
sem_Exports_Cons hd_ tl_  =
    (let _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOtypes :: IdSet
         _lhsOvalues :: IdSet
         _lhsOself :: Exports
         _hdIcons :: IdSet
         _hdImods :: IdSet
         _hdIself :: Export
         _hdItypes :: IdSet
         _hdIvalues :: IdSet
         _tlIcons :: IdSet
         _tlImods :: IdSet
         _tlIself :: Exports
         _tlItypes :: IdSet
         _tlIvalues :: IdSet
         _lhsOcons =
             _hdIcons  `unionSet`  _tlIcons
         _lhsOmods =
             _hdImods  `unionSet`  _tlImods
         _lhsOtypes =
             _hdItypes  `unionSet`  _tlItypes
         _lhsOvalues =
             _hdIvalues  `unionSet`  _tlIvalues
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIcons,_hdImods,_hdIself,_hdItypes,_hdIvalues) =
             (hd_ )
         ( _tlIcons,_tlImods,_tlIself,_tlItypes,_tlIvalues) =
             (tl_ )
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
sem_Exports_Nil :: T_Exports
sem_Exports_Nil  =
    (let _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOtypes :: IdSet
         _lhsOvalues :: IdSet
         _lhsOself :: Exports
         _lhsOcons =
             emptySet
         _lhsOmods =
             emptySet
         _lhsOtypes =
             emptySet
         _lhsOvalues =
             emptySet
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
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
type T_Expression = DictionaryEnvironment ->
                    ( ( Core.Expr ),Expression)
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _alternativesOcaseRange :: Range
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _alternativesOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _alternativesIcore :: ( Core.Expr )
              _alternativesIself :: Alternatives
              _lhsOcore =
                  let_ caseExprId _expressionIcore _alternativesIcore
              _alternativesOcaseRange =
                  _rangeIself
              _self =
                  Expression_Case _rangeIself _expressionIself _alternativesIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _alternativesOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
              ( _alternativesIcore,_alternativesIself) =
                  (alternatives_ _alternativesOcaseRange _alternativesOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _qualifiersOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _qualifiersIcore :: ( [Core.Expr -> Core.Expr] )
              _qualifiersIself :: Qualifiers
              _lhsOcore =
                  let singleton x = cons x nil
                  in foldr ($) (singleton _expressionIcore) _qualifiersIcore
              _self =
                  Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _qualifiersOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
              ( _qualifiersIcore,_qualifiersIself) =
                  (qualifiers_ _qualifiersOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOcore =
                  Core.Con (Core.ConId (idFromName _nameIself))
              _self =
                  Expression_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _statementsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _statementsIcore :: ( [Maybe Core.Expr -> Core.Expr] )
              _statementsIself :: Statements
              _lhsOcore =
                  chainCode _statementsIcore
              _self =
                  Expression_Do _rangeIself _statementsIself
              _lhsOself =
                  _self
              _statementsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _statementsIcore,_statementsIself) =
                  (statements_ _statementsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _fromOdictionaryEnv :: DictionaryEnvironment
              _thenOdictionaryEnv :: DictionaryEnvironment
              _toOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _fromIcore :: ( Core.Expr )
              _fromIself :: Expression
              _thenIcore :: ( Maybe Core.Expr )
              _thenIself :: MaybeExpression
              _toIcore :: ( Maybe Core.Expr )
              _toIself :: MaybeExpression
              _lhsOcore =
                  case (_thenIcore, _toIcore) of
                      (Just then_, Just to) ->
                          insertDictionaries (setNameRange enumFromThenToName _rangeIself) _lhsIdictionaryEnv
                             `app_` _fromIcore `app_` then_ `app_` to
                      (Just then_, Nothing) ->
                          insertDictionaries (setNameRange enumFromThenName _rangeIself) _lhsIdictionaryEnv
                             `app_` _fromIcore `app_` then_
                      (Nothing, Just to) ->
                          insertDictionaries (setNameRange enumFromToName _rangeIself) _lhsIdictionaryEnv
                             `app_` _fromIcore `app_` to
                      (Nothing, Nothing) ->
                          insertDictionaries (setNameRange enumFromName _rangeIself) _lhsIdictionaryEnv
                             `app_` _fromIcore
              _self =
                  Expression_Enum _rangeIself _fromIself _thenIself _toIself
              _lhsOself =
                  _self
              _fromOdictionaryEnv =
                  _lhsIdictionaryEnv
              _thenOdictionaryEnv =
                  _lhsIdictionaryEnv
              _toOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _fromIcore,_fromIself) =
                  (from_ _fromOdictionaryEnv )
              ( _thenIcore,_thenIself) =
                  (then_ _thenOdictionaryEnv )
              ( _toIcore,_toIself) =
                  (to_ _toOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _guardExpressionOdictionaryEnv :: DictionaryEnvironment
              _thenExpressionOdictionaryEnv :: DictionaryEnvironment
              _elseExpressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _guardExpressionIcore :: ( Core.Expr )
              _guardExpressionIself :: Expression
              _thenExpressionIcore :: ( Core.Expr )
              _thenExpressionIself :: Expression
              _elseExpressionIcore :: ( Core.Expr )
              _elseExpressionIself :: Expression
              _lhsOcore =
                  if_ _guardExpressionIcore _thenExpressionIcore _elseExpressionIcore
              _self =
                  Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
              _lhsOself =
                  _self
              _guardExpressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _thenExpressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _elseExpressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _guardExpressionIcore,_guardExpressionIself) =
                  (guardExpression_ _guardExpressionOdictionaryEnv )
              ( _thenExpressionIcore,_thenExpressionIself) =
                  (thenExpression_ _thenExpressionOdictionaryEnv )
              ( _elseExpressionIcore,_elseExpressionIself) =
                  (elseExpression_ _elseExpressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _leftExpressionOdictionaryEnv :: DictionaryEnvironment
              _operatorOdictionaryEnv :: DictionaryEnvironment
              _rightExpressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _leftExpressionIcore :: ( Maybe Core.Expr )
              _leftExpressionIself :: MaybeExpression
              _operatorIcore :: ( Core.Expr )
              _operatorIself :: Expression
              _rightExpressionIcore :: ( Maybe Core.Expr )
              _rightExpressionIself :: MaybeExpression
              _lhsOcore =
                  case (_leftExpressionIcore, _rightExpressionIcore) of
                      (Nothing, Nothing) -> _operatorIcore
                      (Just l , Nothing) -> Core.Ap _operatorIcore l
                      (Nothing, Just r ) -> Core.Lam parameterId
                                              (foldl Core.Ap _operatorIcore [Core.Var parameterId, r])
                      (Just l , Just r ) -> foldl Core.Ap _operatorIcore [l,r]
              _self =
                  Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
              _lhsOself =
                  _self
              _leftExpressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _operatorOdictionaryEnv =
                  _lhsIdictionaryEnv
              _rightExpressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _leftExpressionIcore,_leftExpressionIself) =
                  (leftExpression_ _leftExpressionOdictionaryEnv )
              ( _operatorIcore,_operatorIself) =
                  (operator_ _operatorOdictionaryEnv )
              ( _rightExpressionIcore,_rightExpressionIself) =
                  (rightExpression_ _rightExpressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _patternsIlength :: Int
              _patternsIself :: Patterns
              _patternsIvars :: ( [Name] )
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  let ids = freshIds "u$" _patternsIlength
                  in let_ nextClauseId (patternMatchFail "lambda expression" _rangeIself)
                      (foldr
                          Core.Lam
                          (patternsToCore
                              (zip ids _patternsIself)
                              _expressionIcore
                          )
                          ids
                      )
              _self =
                  Expression_Lambda _rangeIself _patternsIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _patternsIlength,_patternsIself,_patternsIvars) =
                  (patterns_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _declarationsOpatBindNr :: Int
              _declarationsOisTopLevel :: Bool
              _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _declarationsOdictionaryEnv :: DictionaryEnvironment
              _declarationsOimportEnv :: ImportEnvironment
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _declarationsIdecls :: ( [CoreDecl] )
              _declarationsIpatBindNr :: Int
              _declarationsIself :: Declarations
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _importEnv =
                  internalError "CodeGeneration.ag" "Expression.Let" ""
              _declarationsOpatBindNr =
                  0
              _declarationsOisTopLevel =
                  False
              _lhsOcore =
                  letrec_ _declarationsIdecls _expressionIcore
              _self =
                  Expression_Let _rangeIself _declarationsIself _expressionIself
              _lhsOself =
                  _self
              _declarationsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _declarationsOimportEnv =
                  _importEnv
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIdecls,_declarationsIpatBindNr,_declarationsIself) =
                  (declarations_ _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionsIcore :: ( [Core.Expr] )
              _expressionsIself :: Expressions
              _lhsOcore =
                  coreList _expressionsIcore
              _self =
                  Expression_List _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _expressionsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIcore,_expressionsIself) =
                  (expressions_ _expressionsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _rangeIself :: Range
              _literalIcore :: ( Core.Expr )
              _literalIself :: Literal
              _lhsOcore =
                  _literalIcore
              _self =
                  Expression_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _literalIcore,_literalIself) =
                  (literal_ )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  insertDictionaries (setNameRange intUnaryMinusName _rangeIself) _lhsIdictionaryEnv
                  `app_` _expressionIcore
              _self =
                  Expression_Negate _rangeIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  var "$primNegFloat" `app_` _expressionIcore
              _self =
                  Expression_NegateFloat _rangeIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _functionOdictionaryEnv :: DictionaryEnvironment
              _argumentsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _functionIcore :: ( Core.Expr )
              _functionIself :: Expression
              _argumentsIcore :: ( [Core.Expr] )
              _argumentsIself :: Expressions
              _lhsOcore =
                  foldl Core.Ap _functionIcore _argumentsIcore
              _self =
                  Expression_NormalApplication _rangeIself _functionIself _argumentsIself
              _lhsOself =
                  _self
              _functionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _argumentsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _functionIcore,_functionIself) =
                  (function_ _functionOdictionaryEnv )
              ( _argumentsIcore,_argumentsIself) =
                  (arguments_ _argumentsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  _expressionIcore
              _self =
                  Expression_Parenthesized _rangeIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _recordExpressionBindingsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _nameIself :: Name
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _lhsOcore =
                  internalError "ToCoreExpr" "Expression" "records not supported"
              _self =
                  Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _recordExpressionBindingsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordExpressionBindingsIself) =
                  (recordExpressionBindings_ _recordExpressionBindingsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _recordExpressionBindingsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _lhsOcore =
                  internalError "ToCoreExpr" "Expression" "records not supported"
              _self =
                  Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _recordExpressionBindingsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
              ( _recordExpressionBindingsIself) =
                  (recordExpressionBindings_ _recordExpressionBindingsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionsOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionsIcore :: ( [Core.Expr] )
              _expressionsIself :: Expressions
              _lhsOcore =
                  foldl
                      Core.Ap
                      (Core.Con
                          (Core.ConTag
                              (Core.Lit (Core.LitInt 0))
                              (length _expressionsIcore)
                          )
                      )
                      _expressionsIcore
              _self =
                  Expression_Tuple _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _expressionsOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIcore,_expressionsIself) =
                  (expressions_ _expressionsOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _typeIself :: Type
              _lhsOcore =
                  _expressionIcore
              _self =
                  Expression_Typed _rangeIself _expressionIself _typeIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOcore,_lhsOself)))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOself :: Expression
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOcore =
                  insertDictionaries _nameIself _lhsIdictionaryEnv
              _self =
                  Expression_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcore,_lhsOself)))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list  =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list) )
-- semantic domain
type T_Expressions = DictionaryEnvironment ->
                     ( ( [Core.Expr] ),Expressions)
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr] )
              _lhsOself :: Expressions
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIcore :: ( Core.Expr )
              _hdIself :: Expression
              _tlIcore :: ( [Core.Expr] )
              _tlIself :: Expressions
              _lhsOcore =
                  _hdIcore  :  _tlIcore
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIcore,_hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIcore,_tlIself) =
                  (tl_ _tlOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr] )
              _lhsOself :: Expressions
              _lhsOcore =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
type T_FunctionBinding = DictionaryEnvironment ->
                         ( [Id] ) ->
                         ( Int,( Core.Expr -> Core.Expr ),Name,FunctionBinding)
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_  =
    (\ _lhsIdictionaryEnv
       _lhsIids ->
         (let _lhsOarity :: Int
              _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: FunctionBinding
              _lhsOname :: Name
              _righthandsideOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _lefthandsideIarity :: Int
              _lefthandsideIname :: Name
              _lefthandsideIpatterns :: Patterns
              _lefthandsideIself :: LeftHandSide
              _righthandsideIcore :: ( Core.Expr )
              _righthandsideIisGuarded :: Bool
              _righthandsideIself :: RightHandSide
              _lhsOarity =
                  _lefthandsideIarity
              _lhsOcore =
                  \nextClause ->
                      let thisClause =
                              patternsToCore
                                  (zip _lhsIids _lefthandsideIpatterns)
                                  _righthandsideIcore in
                      if all patternAlwaysSucceeds _lefthandsideIpatterns
                         &&
                         not _righthandsideIisGuarded
                      then
                          thisClause
                      else
                          let_ nextClauseId nextClause thisClause
              _self =
                  FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOname =
                  _lefthandsideIname
              _righthandsideOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIarity,_lefthandsideIname,_lefthandsideIpatterns,_lefthandsideIself) =
                  (lefthandside_ )
              ( _righthandsideIcore,_righthandsideIisGuarded,_righthandsideIself) =
                  (righthandside_ _righthandsideOdictionaryEnv )
          in  ( _lhsOarity,_lhsOcore,_lhsOname,_lhsOself)))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list  =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list) )
-- semantic domain
type T_FunctionBindings = DictionaryEnvironment ->
                          ( [Id] ) ->
                          Range ->
                          ( Int,(Core.Expr),Name,FunctionBindings)
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv
       _lhsIids
       _lhsIrange ->
         (let _lhsOcore :: (Core.Expr)
              _lhsOarity :: Int
              _lhsOname :: Name
              _lhsOself :: FunctionBindings
              _hdOdictionaryEnv :: DictionaryEnvironment
              _hdOids :: ( [Id] )
              _tlOdictionaryEnv :: DictionaryEnvironment
              _tlOids :: ( [Id] )
              _tlOrange :: Range
              _hdIarity :: Int
              _hdIcore :: ( Core.Expr -> Core.Expr )
              _hdIname :: Name
              _hdIself :: FunctionBinding
              _tlIarity :: Int
              _tlIcore :: (Core.Expr)
              _tlIname :: Name
              _tlIself :: FunctionBindings
              _lhsOcore =
                  _hdIcore _tlIcore
              _lhsOarity =
                  _hdIarity
              _lhsOname =
                  _hdIname
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _hdOids =
                  _lhsIids
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOids =
                  _lhsIids
              _tlOrange =
                  _lhsIrange
              ( _hdIarity,_hdIcore,_hdIname,_hdIself) =
                  (hd_ _hdOdictionaryEnv _hdOids )
              ( _tlIarity,_tlIcore,_tlIname,_tlIself) =
                  (tl_ _tlOdictionaryEnv _tlOids _tlOrange )
          in  ( _lhsOarity,_lhsOcore,_lhsOname,_lhsOself)))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil  =
    (\ _lhsIdictionaryEnv
       _lhsIids
       _lhsIrange ->
         (let _lhsOcore :: (Core.Expr)
              _lhsOarity :: Int
              _lhsOname :: Name
              _lhsOself :: FunctionBindings
              _lhsOcore =
                  patternMatchFail "function bindings" _lhsIrange
              _lhsOarity =
                  internalError "ToCoreDecl" "FunctionBindings" "arity: empty list of function bindings"
              _lhsOname =
                  internalError "ToCoreName.ag" "n/a" "empty FunctionBindings"
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOarity,_lhsOcore,_lhsOname,_lhsOself)))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression )  =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range ) (sem_Expression _guard ) (sem_Expression _expression ) )
-- semantic domain
type T_GuardedExpression = DictionaryEnvironment ->
                           ( ( Core.Expr -> Core.Expr ),GuardedExpression)
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: GuardedExpression
              _guardOdictionaryEnv :: DictionaryEnvironment
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _guardIcore :: ( Core.Expr )
              _guardIself :: Expression
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  \fail -> if_ _guardIcore _expressionIcore fail
              _self =
                  GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
              _lhsOself =
                  _self
              _guardOdictionaryEnv =
                  _lhsIdictionaryEnv
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _guardIcore,_guardIself) =
                  (guard_ _guardOdictionaryEnv )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list  =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list) )
-- semantic domain
type T_GuardedExpressions = DictionaryEnvironment ->
                            ( ( [Core.Expr -> Core.Expr] ),GuardedExpressions)
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr -> Core.Expr] )
              _lhsOself :: GuardedExpressions
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIcore :: ( Core.Expr -> Core.Expr )
              _hdIself :: GuardedExpression
              _tlIcore :: ( [Core.Expr -> Core.Expr] )
              _tlIself :: GuardedExpressions
              _lhsOcore =
                  _hdIcore  :  _tlIcore
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIcore,_hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIcore,_tlIself) =
                  (tl_ _tlOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr -> Core.Expr] )
              _lhsOself :: GuardedExpressions
              _lhsOcore =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
         _namesInames :: ( Maybe [Name] )
         _namesIself :: MaybeNames
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
         _asnameIisNothing :: Bool
         _asnameIname :: ( Maybe Name )
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
         ( _asnameIisNothing,_asnameIname,_asnameIself) =
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
type T_LeftHandSide = ( Int,Name,Patterns,LeftHandSide)
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_  =
    (let _lhsOarity :: Int
         _lhsOpatterns :: Patterns
         _lhsOname :: Name
         _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIlength :: Int
         _patternsIself :: Patterns
         _patternsIvars :: ( [Name] )
         _lhsOarity =
             _patternsIlength
         _lhsOpatterns =
             _patternsIself
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
         ( _patternsIlength,_patternsIself,_patternsIvars) =
             (patterns_ )
     in  ( _lhsOarity,_lhsOname,_lhsOpatterns,_lhsOself))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_  =
    (let _lhsOarity :: Int
         _lhsOpatterns :: Patterns
         _lhsOname :: Name
         _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _leftPatternIvars :: ( [Name] )
         _operatorIself :: Name
         _rightPatternIself :: Pattern
         _rightPatternIvars :: ( [Name] )
         _lhsOarity =
             2
         _lhsOpatterns =
             [_leftPatternIself, _rightPatternIself ]
         _lhsOname =
             _operatorIself
         _self =
             LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftPatternIself,_leftPatternIvars) =
             (leftPattern_ )
         ( _operatorIself) =
             (operator_ )
         ( _rightPatternIself,_rightPatternIvars) =
             (rightPattern_ )
     in  ( _lhsOarity,_lhsOname,_lhsOpatterns,_lhsOself))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_  =
    (let _lhsOarity :: Int
         _lhsOpatterns :: Patterns
         _lhsOself :: LeftHandSide
         _lhsOname :: Name
         _rangeIself :: Range
         _lefthandsideIarity :: Int
         _lefthandsideIname :: Name
         _lefthandsideIpatterns :: Patterns
         _lefthandsideIself :: LeftHandSide
         _patternsIlength :: Int
         _patternsIself :: Patterns
         _patternsIvars :: ( [Name] )
         _lhsOarity =
             _lefthandsideIarity + _patternsIlength
         _lhsOpatterns =
             _lefthandsideIpatterns ++ _patternsIself
         _self =
             LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
         _lhsOself =
             _self
         _lhsOname =
             _lefthandsideIname
         ( _rangeIself) =
             (range_ )
         ( _lefthandsideIarity,_lefthandsideIname,_lefthandsideIpatterns,_lefthandsideIself) =
             (lefthandside_ )
         ( _patternsIlength,_patternsIself,_patternsIvars) =
             (patterns_ )
     in  ( _lhsOarity,_lhsOname,_lhsOpatterns,_lhsOself))
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
type T_Literal = ( ( Core.Expr ),Literal)
sem_Literal_Char :: T_Range ->
                    String ->
                    T_Literal
sem_Literal_Char range_ value_  =
    (let _lhsOcore :: ( Core.Expr )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOcore =
             Core.Lit (Core.LitInt (ord
                 (read ("'" ++ value_ ++ "'"))))
         _self =
             Literal_Char _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOcore,_lhsOself))
sem_Literal_Float :: T_Range ->
                     String ->
                     T_Literal
sem_Literal_Float range_ value_  =
    (let _lhsOcore :: ( Core.Expr )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOcore =
             float value_
         _self =
             Literal_Float _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOcore,_lhsOself))
sem_Literal_Int :: T_Range ->
                   String ->
                   T_Literal
sem_Literal_Int range_ value_  =
    (let _lhsOcore :: ( Core.Expr )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOcore =
             Core.Lit (Core.LitInt (read value_))
         _self =
             Literal_Int _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOcore,_lhsOself))
sem_Literal_String :: T_Range ->
                      String ->
                      T_Literal
sem_Literal_String range_ value_  =
    (let _lhsOcore :: ( Core.Expr )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOcore =
             var "$primPackedToString" `app_`
                 packedString (read ("\"" ++ value_ ++ "\""))
         _self =
             Literal_String _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOcore,_lhsOself))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations ->
                         T_MaybeDeclarations
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations )  =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations ) )
sem_MaybeDeclarations (MaybeDeclarations_Nothing )  =
    (sem_MaybeDeclarations_Nothing )
-- semantic domain
type T_MaybeDeclarations = DictionaryEnvironment ->
                           ( ( Core.Expr -> Core.Expr ),MaybeDeclarations)
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_  =
    (\ _lhsIdictionaryEnv ->
         (let _declarationsOpatBindNr :: Int
              _declarationsOisTopLevel :: Bool
              _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: MaybeDeclarations
              _declarationsOdictionaryEnv :: DictionaryEnvironment
              _declarationsOimportEnv :: ImportEnvironment
              _declarationsIdecls :: ( [CoreDecl] )
              _declarationsIpatBindNr :: Int
              _declarationsIself :: Declarations
              _importEnv =
                  internalError "CodeGeneration.ag" "MaybeDeclarations.Just" ""
              _declarationsOpatBindNr =
                  0
              _declarationsOisTopLevel =
                  False
              _lhsOcore =
                  \continue -> letrec_ _declarationsIdecls continue
              _self =
                  MaybeDeclarations_Just _declarationsIself
              _lhsOself =
                  _self
              _declarationsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _declarationsOimportEnv =
                  _importEnv
              ( _declarationsIdecls,_declarationsIpatBindNr,_declarationsIself) =
                  (declarations_ _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr )
          in  ( _lhsOcore,_lhsOself)))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: MaybeDeclarations
              _lhsOcore =
                  \continue -> continue
              _self =
                  MaybeDeclarations_Nothing
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports ->
                    T_MaybeExports
sem_MaybeExports (MaybeExports_Just _exports )  =
    (sem_MaybeExports_Just (sem_Exports _exports ) )
sem_MaybeExports (MaybeExports_Nothing )  =
    (sem_MaybeExports_Nothing )
-- semantic domain
type T_MaybeExports = ( IdSet,IdSet,MaybeExports,IdSet,IdSet)
sem_MaybeExports_Just :: T_Exports ->
                         T_MaybeExports
sem_MaybeExports_Just exports_  =
    (let _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOtypes :: IdSet
         _lhsOvalues :: IdSet
         _lhsOself :: MaybeExports
         _exportsIcons :: IdSet
         _exportsImods :: IdSet
         _exportsIself :: Exports
         _exportsItypes :: IdSet
         _exportsIvalues :: IdSet
         _lhsOcons =
             _exportsIcons
         _lhsOmods =
             _exportsImods
         _lhsOtypes =
             _exportsItypes
         _lhsOvalues =
             _exportsIvalues
         _self =
             MaybeExports_Just _exportsIself
         _lhsOself =
             _self
         ( _exportsIcons,_exportsImods,_exportsIself,_exportsItypes,_exportsIvalues) =
             (exports_ )
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
sem_MaybeExports_Nothing :: T_MaybeExports
sem_MaybeExports_Nothing  =
    (let _lhsOcons :: IdSet
         _lhsOmods :: IdSet
         _lhsOtypes :: IdSet
         _lhsOvalues :: IdSet
         _lhsOself :: MaybeExports
         _lhsOcons =
             emptySet
         _lhsOmods =
             emptySet
         _lhsOtypes =
             emptySet
         _lhsOvalues =
             emptySet
         _self =
             MaybeExports_Nothing
         _lhsOself =
             _self
     in  ( _lhsOcons,_lhsOmods,_lhsOself,_lhsOtypes,_lhsOvalues))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression ->
                       T_MaybeExpression
sem_MaybeExpression (MaybeExpression_Just _expression )  =
    (sem_MaybeExpression_Just (sem_Expression _expression ) )
sem_MaybeExpression (MaybeExpression_Nothing )  =
    (sem_MaybeExpression_Nothing )
-- semantic domain
type T_MaybeExpression = DictionaryEnvironment ->
                         ( ( Maybe Core.Expr ),MaybeExpression)
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Maybe Core.Expr )
              _lhsOself :: MaybeExpression
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  Just _expressionIcore
              _self =
                  MaybeExpression_Just _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Maybe Core.Expr )
              _lhsOself :: MaybeExpression
              _lhsOcore =
                  Nothing
              _self =
                  MaybeExpression_Nothing
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
type T_Module = DictionaryEnvironment ->
                ( [Core.CoreDecl] ) ->
                ImportEnvironment ->
                TypeEnvironment ->
                ( ( Core.CoreModule ),Module)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_  =
    (\ _lhsIdictionaryEnv
       _lhsIextraDecls
       _lhsIimportEnv
       _lhsItoplevelTypes ->
         (let _lhsOcore :: ( Core.CoreModule )
              _lhsOself :: Module
              _bodyOdictionaryEnv :: DictionaryEnvironment
              _bodyOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _nameIisNothing :: Bool
              _nameIname :: ( Maybe Name )
              _nameIself :: MaybeName
              _exportsIcons :: IdSet
              _exportsImods :: IdSet
              _exportsIself :: MaybeExports
              _exportsItypes :: IdSet
              _exportsIvalues :: IdSet
              _bodyIdecls :: ( [CoreDecl] )
              _bodyIself :: Body
              _lhsOcore =
                  _module_ { Module.moduleDecls =
                       insertedMain _lhsItoplevelTypes : Module.moduleDecls _module_ }
              _module_ =
                  everythingPublicButPrelude
                      (makeCoreModule (fmap idFromName _nameIname)
                          ( _bodyIdecls ++ _lhsIextraDecls
                          ))
              _self =
                  Module_Module _rangeIself _nameIself _exportsIself _bodyIself
              _lhsOself =
                  _self
              _bodyOdictionaryEnv =
                  _lhsIdictionaryEnv
              _bodyOimportEnv =
                  _lhsIimportEnv
              ( _rangeIself) =
                  (range_ )
              ( _nameIisNothing,_nameIname,_nameIself) =
                  (name_ )
              ( _exportsIcons,_exportsImods,_exportsIself,_exportsItypes,_exportsIvalues) =
                  (exports_ )
              ( _bodyIdecls,_bodyIself) =
                  (body_ _bodyOdictionaryEnv _bodyOimportEnv )
          in  ( _lhsOcore,_lhsOself)))
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
type T_Pattern = ( Pattern,( [Name] ))
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternIself :: Pattern
         _patternIvars :: ( [Name] )
         _lhsOvars =
             _nameIself : _patternIvars
         _self =
             Pattern_As _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternIself,_patternIvars) =
             (pattern_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIlength :: Int
         _patternsIself :: Patterns
         _patternsIvars :: ( [Name] )
         _lhsOvars =
             _patternsIvars
         _self =
             Pattern_Constructor _rangeIself _nameIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternsIlength,_patternsIself,_patternsIvars) =
             (patterns_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _leftPatternIvars :: ( [Name] )
         _constructorOperatorIself :: Name
         _rightPatternIself :: Pattern
         _rightPatternIvars :: ( [Name] )
         _lhsOvars =
             _leftPatternIvars  ++  _rightPatternIvars
         _self =
             Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _leftPatternIself,_leftPatternIvars) =
             (leftPattern_ )
         ( _constructorOperatorIself) =
             (constructorOperator_ )
         ( _rightPatternIself,_rightPatternIvars) =
             (rightPattern_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _patternIvars :: ( [Name] )
         _lhsOvars =
             _patternIvars
         _self =
             Pattern_Irrefutable _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself,_patternIvars) =
             (pattern_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIlength :: Int
         _patternsIself :: Patterns
         _patternsIvars :: ( [Name] )
         _lhsOvars =
             _patternsIvars
         _self =
             Pattern_List _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternsIlength,_patternsIself,_patternsIvars) =
             (patterns_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIcore :: ( Core.Expr )
         _literalIself :: Literal
         _lhsOvars =
             []
         _self =
             Pattern_Literal _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIcore,_literalIself) =
             (literal_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIcore :: ( Core.Expr )
         _literalIself :: Literal
         _lhsOvars =
             []
         _self =
             Pattern_Negate _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIcore,_literalIself) =
             (literal_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIcore :: ( Core.Expr )
         _literalIself :: Literal
         _lhsOvars =
             []
         _self =
             Pattern_NegateFloat _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _literalIcore,_literalIself) =
             (literal_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _patternIvars :: ( [Name] )
         _lhsOvars =
             _patternIvars
         _self =
             Pattern_Parenthesized _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternIself,_patternIvars) =
             (pattern_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _recordPatternBindingsIself :: RecordPatternBindings
         _lhsOvars =
             []
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
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _literalIcore :: ( Core.Expr )
         _literalIself :: Literal
         _lhsOvars =
             []
         _self =
             Pattern_Successor _rangeIself _nameIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _literalIcore,_literalIself) =
             (literal_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIlength :: Int
         _patternsIself :: Patterns
         _patternsIvars :: ( [Name] )
         _lhsOvars =
             _patternsIvars
         _self =
             Pattern_Tuple _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _patternsIlength,_patternsIself,_patternsIvars) =
             (patterns_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _lhsOvars =
             [ _nameIself ]
         _self =
             Pattern_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself,_lhsOvars))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_  =
    (let _lhsOvars :: ( [Name] )
         _lhsOself :: Pattern
         _rangeIself :: Range
         _lhsOvars =
             []
         _self =
             Pattern_Wildcard _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself,_lhsOvars))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list  =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list) )
-- semantic domain
type T_Patterns = ( Int,Patterns,( [Name] ))
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_  =
    (let _lhsOlength :: Int
         _lhsOvars :: ( [Name] )
         _lhsOself :: Patterns
         _hdIself :: Pattern
         _hdIvars :: ( [Name] )
         _tlIlength :: Int
         _tlIself :: Patterns
         _tlIvars :: ( [Name] )
         _lhsOlength =
             1 + _tlIlength
         _lhsOvars =
             _hdIvars  ++  _tlIvars
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself,_hdIvars) =
             (hd_ )
         ( _tlIlength,_tlIself,_tlIvars) =
             (tl_ )
     in  ( _lhsOlength,_lhsOself,_lhsOvars))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil  =
    (let _lhsOlength :: Int
         _lhsOvars :: ( [Name] )
         _lhsOself :: Patterns
         _lhsOlength =
             0
         _lhsOvars =
             []
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOlength,_lhsOself,_lhsOvars))
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
type T_Qualifier = DictionaryEnvironment ->
                   ( ( Core.Expr -> Core.Expr ),Qualifier)
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Qualifier
              _rangeIself :: Range
              _lhsOcore =
                  internalError "ToCoreExpr" "Qualifier" "empty qualifiers not supported"
              _self =
                  Qualifier_Empty _rangeIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcore,_lhsOself)))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Qualifier
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _patternIself :: Pattern
              _patternIvars :: ( [Name] )
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  \continue ->
                      let_ nextClauseId nil
                          (let_
                              okId
                              (Core.Lam parameterId
                                  (patternToCore (parameterId, _patternIself) continue)
                              )
                              (var "$primConcatMap"
                                  `app_` Core.Var okId
                                  `app_` _expressionIcore
                              )
                          )
              _self =
                  Qualifier_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _patternIself,_patternIvars) =
                  (pattern_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Qualifier
              _guardOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _guardIcore :: ( Core.Expr )
              _guardIself :: Expression
              _lhsOcore =
                  \continue -> if_ _guardIcore continue nil
              _self =
                  Qualifier_Guard _rangeIself _guardIself
              _lhsOself =
                  _self
              _guardOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _guardIcore,_guardIself) =
                  (guard_ _guardOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_  =
    (\ _lhsIdictionaryEnv ->
         (let _declarationsOpatBindNr :: Int
              _declarationsOisTopLevel :: Bool
              _lhsOcore :: ( Core.Expr -> Core.Expr )
              _lhsOself :: Qualifier
              _declarationsOdictionaryEnv :: DictionaryEnvironment
              _declarationsOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _declarationsIdecls :: ( [CoreDecl] )
              _declarationsIpatBindNr :: Int
              _declarationsIself :: Declarations
              _importEnv =
                  internalError "CodeGeneration.ag" "Qualifier.Let" ""
              _declarationsOpatBindNr =
                  0
              _declarationsOisTopLevel =
                  False
              _lhsOcore =
                  \continue -> letrec_ _declarationsIdecls continue
              _self =
                  Qualifier_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _declarationsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _declarationsOimportEnv =
                  _importEnv
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIdecls,_declarationsIpatBindNr,_declarationsIself) =
                  (declarations_ _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr )
          in  ( _lhsOcore,_lhsOself)))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list  =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list) )
-- semantic domain
type T_Qualifiers = DictionaryEnvironment ->
                    ( ( [Core.Expr -> Core.Expr] ),Qualifiers)
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr -> Core.Expr] )
              _lhsOself :: Qualifiers
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIcore :: ( Core.Expr -> Core.Expr )
              _hdIself :: Qualifier
              _tlIcore :: ( [Core.Expr -> Core.Expr] )
              _tlIself :: Qualifiers
              _lhsOcore =
                  _hdIcore  :  _tlIcore
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIcore,_hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIcore,_tlIself) =
                  (tl_ _tlOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Core.Expr -> Core.Expr] )
              _lhsOself :: Qualifiers
              _lhsOcore =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
type T_RecordExpressionBinding = DictionaryEnvironment ->
                                 ( RecordExpressionBinding)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOself :: RecordExpressionBinding
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _nameIself :: Name
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _self =
                  RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOself)))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list  =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list) )
-- semantic domain
type T_RecordExpressionBindings = DictionaryEnvironment ->
                                  ( RecordExpressionBindings)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOself :: RecordExpressionBindings
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIself :: RecordExpressionBinding
              _tlIself :: RecordExpressionBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIself) =
                  (tl_ _tlOdictionaryEnv )
          in  ( _lhsOself)))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOself :: RecordExpressionBindings
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOself)))
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
         _patternIvars :: ( [Name] )
         _self =
             RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _patternIself,_patternIvars) =
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
type T_RightHandSide = DictionaryEnvironment ->
                       ( ( Core.Expr ),Bool,RightHandSide)
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Core.Expr )
              _lhsOisGuarded :: Bool
              _lhsOself :: RightHandSide
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _whereOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _whereIcore :: ( Core.Expr -> Core.Expr )
              _whereIself :: MaybeDeclarations
              _lhsOcore =
                  _whereIcore _expressionIcore
              _lhsOisGuarded =
                  False
              _self =
                  RightHandSide_Expression _rangeIself _expressionIself _whereIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              _whereOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
              ( _whereIcore,_whereIself) =
                  (where_ _whereOdictionaryEnv )
          in  ( _lhsOcore,_lhsOisGuarded,_lhsOself)))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOisGuarded :: Bool
              _lhsOcore :: ( Core.Expr )
              _lhsOself :: RightHandSide
              _guardedexpressionsOdictionaryEnv :: DictionaryEnvironment
              _whereOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _guardedexpressionsIcore :: ( [Core.Expr -> Core.Expr] )
              _guardedexpressionsIself :: GuardedExpressions
              _whereIcore :: ( Core.Expr -> Core.Expr )
              _whereIself :: MaybeDeclarations
              _lhsOisGuarded =
                  True
              _lhsOcore =
                  _whereIcore (foldr ($) (Core.Var nextClauseId) _guardedexpressionsIcore)
              _self =
                  RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
              _lhsOself =
                  _self
              _guardedexpressionsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _whereOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _guardedexpressionsIcore,_guardedexpressionsIself) =
                  (guardedexpressions_ _guardedexpressionsOdictionaryEnv )
              ( _whereIcore,_whereIself) =
                  (where_ _whereOdictionaryEnv )
          in  ( _lhsOcore,_lhsOisGuarded,_lhsOself)))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType ->
                  T_SimpleType
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables )  =
    (sem_SimpleType_SimpleType (sem_Range _range ) (sem_Name _name ) (sem_Names _typevariables ) )
-- semantic domain
type T_SimpleType = ( Name,SimpleType,Names)
sem_SimpleType_SimpleType :: T_Range ->
                             T_Name ->
                             T_Names ->
                             T_SimpleType
sem_SimpleType_SimpleType range_ name_ typevariables_  =
    (let _lhsOname :: Name
         _lhsOtypevariables :: Names
         _lhsOself :: SimpleType
         _rangeIself :: Range
         _nameIself :: Name
         _typevariablesInames :: ([Name])
         _typevariablesIself :: Names
         _lhsOname =
             _nameIself
         _lhsOtypevariables =
             _typevariablesIself
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
     in  ( _lhsOname,_lhsOself,_lhsOtypevariables))
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
type T_Statement = DictionaryEnvironment ->
                   ( ( Maybe Core.Expr -> Core.Expr ),Statement)
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Maybe Core.Expr -> Core.Expr )
              _lhsOself :: Statement
              _rangeIself :: Range
              _lhsOcore =
                  \rest ->
                      case rest of
                          Nothing   -> internalError "ToCoreExpr" "Statement" "empty statements not supported"
                          Just rest -> rest
              _self =
                  Statement_Empty _rangeIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcore,_lhsOself)))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Maybe Core.Expr -> Core.Expr )
              _lhsOself :: Statement
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  \rest ->
                      case rest of
                          Nothing   -> _expressionIcore
                          Just rest -> bind _expressionIcore (Core.Lam dummyId rest)
              _self =
                  Statement_Expression _rangeIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( Maybe Core.Expr -> Core.Expr )
              _lhsOself :: Statement
              _expressionOdictionaryEnv :: DictionaryEnvironment
              _rangeIself :: Range
              _patternIself :: Pattern
              _patternIvars :: ( [Name] )
              _expressionIcore :: ( Core.Expr )
              _expressionIself :: Expression
              _lhsOcore =
                  \rest -> case rest of
                      Nothing   -> internalError "ToCoreExpr" "Statement" "generator can't be last in 'do'"
                      Just rest ->
                          let_ nextClauseId (patternMatchFail "generator" _rangeIself)
                              (let_
                                  okId
                                  (Core.Lam parameterId
                                      (patternToCore (parameterId, _patternIself) rest)
                                  )
                                  (_expressionIcore `bind` Core.Var okId)
                              )
              _self =
                  Statement_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _expressionOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _rangeIself) =
                  (range_ )
              ( _patternIself,_patternIvars) =
                  (pattern_ )
              ( _expressionIcore,_expressionIself) =
                  (expression_ _expressionOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_  =
    (\ _lhsIdictionaryEnv ->
         (let _declarationsOpatBindNr :: Int
              _declarationsOisTopLevel :: Bool
              _lhsOcore :: ( Maybe Core.Expr -> Core.Expr )
              _lhsOself :: Statement
              _declarationsOdictionaryEnv :: DictionaryEnvironment
              _declarationsOimportEnv :: ImportEnvironment
              _rangeIself :: Range
              _declarationsIdecls :: ( [CoreDecl] )
              _declarationsIpatBindNr :: Int
              _declarationsIself :: Declarations
              _importEnv =
                  internalError "CodeGeneration.ag" "Statement.Let" ""
              _declarationsOpatBindNr =
                  0
              _declarationsOisTopLevel =
                  False
              _lhsOcore =
                  \rest ->
                      case rest of
                          Nothing   -> internalError "ToCoreExpr" "Statement" "'let' can't be last in 'do'"
                          Just rest -> letrec_ _declarationsIdecls rest
              _self =
                  Statement_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _declarationsOdictionaryEnv =
                  _lhsIdictionaryEnv
              _declarationsOimportEnv =
                  _importEnv
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIdecls,_declarationsIpatBindNr,_declarationsIself) =
                  (declarations_ _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr )
          in  ( _lhsOcore,_lhsOself)))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list  =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list) )
-- semantic domain
type T_Statements = DictionaryEnvironment ->
                    ( ( [Maybe Core.Expr -> Core.Expr] ),Statements)
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Maybe Core.Expr -> Core.Expr] )
              _lhsOself :: Statements
              _hdOdictionaryEnv :: DictionaryEnvironment
              _tlOdictionaryEnv :: DictionaryEnvironment
              _hdIcore :: ( Maybe Core.Expr -> Core.Expr )
              _hdIself :: Statement
              _tlIcore :: ( [Maybe Core.Expr -> Core.Expr] )
              _tlIself :: Statements
              _lhsOcore =
                  _hdIcore  :  _tlIcore
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOdictionaryEnv =
                  _lhsIdictionaryEnv
              _tlOdictionaryEnv =
                  _lhsIdictionaryEnv
              ( _hdIcore,_hdIself) =
                  (hd_ _hdOdictionaryEnv )
              ( _tlIcore,_tlIself) =
                  (tl_ _tlOdictionaryEnv )
          in  ( _lhsOcore,_lhsOself)))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil  =
    (\ _lhsIdictionaryEnv ->
         (let _lhsOcore :: ( [Maybe Core.Expr -> Core.Expr] )
              _lhsOself :: Statements
              _lhsOcore =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOcore,_lhsOself)))
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
