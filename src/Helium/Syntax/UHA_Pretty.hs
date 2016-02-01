{-# LANGUAGE Rank2Types, GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Helium.Syntax.UHA_Pretty where

-- Below two imports are to avoid clashes of "list" as used by the AG system.
-- Effectively, only list from the imported library needs to be qualified.
import Prelude hiding ((<$>))
import Text.PrettyPrint.Leijen hiding (list)
import qualified Text.PrettyPrint.Leijen as PPrint
import Data.Char
import Top.Types (isTupleConstructor)

import Helium.Syntax.UHA_Syntax
import Helium.Utils.Utils (internalError, hole)

import Control.Monad.Identity (Identity)
import qualified Control.Monad.Identity

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

-- Alternative -------------------------------------------------
-- wrapper
data Inh_Alternative  = Inh_Alternative {  }
data Syn_Alternative  = Syn_Alternative { text_Syn_Alternative :: (Doc) }
{-# INLINABLE wrap_Alternative #-}
wrap_Alternative :: T_Alternative  -> Inh_Alternative  -> (Syn_Alternative )
wrap_Alternative (T_Alternative act) (Inh_Alternative ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg1 = T_Alternative_vIn1 
        (T_Alternative_vOut1 _lhsOtext) <- return (inv_Alternative_s2 sem arg1)
        return (Syn_Alternative _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Alternative #-}
sem_Alternative :: Alternative  -> T_Alternative 
sem_Alternative ( Alternative_Hole range_ id_ ) = sem_Alternative_Hole ( sem_Range range_ ) id_
sem_Alternative ( Alternative_Feedback range_ feedback_ alternative_ ) = sem_Alternative_Feedback ( sem_Range range_ ) feedback_ ( sem_Alternative alternative_ )
sem_Alternative ( Alternative_Alternative range_ pattern_ righthandside_ ) = sem_Alternative_Alternative ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_RightHandSide righthandside_ )
sem_Alternative ( Alternative_Empty range_ ) = sem_Alternative_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Alternative  = T_Alternative {
                                       attach_T_Alternative :: Identity (T_Alternative_s2 )
                                       }
newtype T_Alternative_s2  = C_Alternative_s2 {
                                             inv_Alternative_s2 :: (T_Alternative_v1 )
                                             }
data T_Alternative_s3  = C_Alternative_s3
type T_Alternative_v1  = (T_Alternative_vIn1 ) -> (T_Alternative_vOut1 )
data T_Alternative_vIn1  = T_Alternative_vIn1 
data T_Alternative_vOut1  = T_Alternative_vOut1 (Doc)
{-# NOINLINE sem_Alternative_Hole #-}
sem_Alternative_Hole :: T_Range  -> (Integer) -> T_Alternative 
sem_Alternative_Hole arg_range_ _ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule0  ()
         _lhsOtext :: Doc
         _lhsOtext = rule1 _text
         __result_ = T_Alternative_vOut1 _lhsOtext
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule0 #-}
   rule0 = \  (_ :: ()) ->
                                     text hole
   {-# INLINE rule1 #-}
   rule1 = \ _text ->
     _text
{-# NOINLINE sem_Alternative_Feedback #-}
sem_Alternative_Feedback :: T_Range  -> (String) -> T_Alternative  -> T_Alternative 
sem_Alternative_Feedback arg_range_ _ arg_alternative_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _alternativeX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_alternative_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Alternative_vOut1 _alternativeItext) = inv_Alternative_s2 _alternativeX2 (T_Alternative_vIn1 )
         _lhsOtext :: Doc
         _lhsOtext = rule2 _alternativeItext
         __result_ = T_Alternative_vOut1 _lhsOtext
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule2 #-}
   rule2 = \ ((_alternativeItext) :: Doc) ->
     _alternativeItext
{-# NOINLINE sem_Alternative_Alternative #-}
sem_Alternative_Alternative :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Alternative 
sem_Alternative_Alternative arg_range_ arg_pattern_ arg_righthandside_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_RightHandSide_vOut148 _righthandsideItext) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 )
         _text = rule3 _patternItext _righthandsideItext
         _lhsOtext :: Doc
         _lhsOtext = rule4 _text
         __result_ = T_Alternative_vOut1 _lhsOtext
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule3 #-}
   rule3 = \ ((_patternItext) :: Doc) ((_righthandsideItext) ::  Doc        -> Doc  ) ->
                                     _patternItext <$> indent 2 (_righthandsideItext (text "->"))
   {-# INLINE rule4 #-}
   rule4 = \ _text ->
     _text
{-# NOINLINE sem_Alternative_Empty #-}
sem_Alternative_Empty :: T_Range  -> T_Alternative 
sem_Alternative_Empty arg_range_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule5  ()
         _lhsOtext :: Doc
         _lhsOtext = rule6 _text
         __result_ = T_Alternative_vOut1 _lhsOtext
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule5 #-}
   rule5 = \  (_ :: ()) ->
                                     empty
   {-# INLINE rule6 #-}
   rule6 = \ _text ->
     _text

-- Alternatives ------------------------------------------------
-- wrapper
data Inh_Alternatives  = Inh_Alternatives {  }
data Syn_Alternatives  = Syn_Alternatives { text_Syn_Alternatives :: ( [       Doc ] ) }
{-# INLINABLE wrap_Alternatives #-}
wrap_Alternatives :: T_Alternatives  -> Inh_Alternatives  -> (Syn_Alternatives )
wrap_Alternatives (T_Alternatives act) (Inh_Alternatives ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg4 = T_Alternatives_vIn4 
        (T_Alternatives_vOut4 _lhsOtext) <- return (inv_Alternatives_s5 sem arg4)
        return (Syn_Alternatives _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Alternatives #-}
sem_Alternatives :: Alternatives  -> T_Alternatives 
sem_Alternatives list = Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list)

-- semantic domain
newtype T_Alternatives  = T_Alternatives {
                                         attach_T_Alternatives :: Identity (T_Alternatives_s5 )
                                         }
newtype T_Alternatives_s5  = C_Alternatives_s5 {
                                               inv_Alternatives_s5 :: (T_Alternatives_v4 )
                                               }
data T_Alternatives_s6  = C_Alternatives_s6
type T_Alternatives_v4  = (T_Alternatives_vIn4 ) -> (T_Alternatives_vOut4 )
data T_Alternatives_vIn4  = T_Alternatives_vIn4 
data T_Alternatives_vOut4  = T_Alternatives_vOut4 ( [       Doc ] )
{-# NOINLINE sem_Alternatives_Cons #-}
sem_Alternatives_Cons :: T_Alternative  -> T_Alternatives  -> T_Alternatives 
sem_Alternatives_Cons arg_hd_ arg_tl_ = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 ) -> ( let
         _hdX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_hd_))
         _tlX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_tl_))
         (T_Alternative_vOut1 _hdItext) = inv_Alternative_s2 _hdX2 (T_Alternative_vIn1 )
         (T_Alternatives_vOut4 _tlItext) = inv_Alternatives_s5 _tlX5 (T_Alternatives_vIn4 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule7 _hdItext _tlItext
         __result_ = T_Alternatives_vOut4 _lhsOtext
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule7 #-}
   rule7 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Alternatives_Nil #-}
sem_Alternatives_Nil ::  T_Alternatives 
sem_Alternatives_Nil  = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule8  ()
         __result_ = T_Alternatives_vOut4 _lhsOtext
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule8 #-}
   rule8 = \  (_ :: ()) ->
     []

-- AnnotatedType -----------------------------------------------
-- wrapper
data Inh_AnnotatedType  = Inh_AnnotatedType {  }
data Syn_AnnotatedType  = Syn_AnnotatedType { text_Syn_AnnotatedType :: (Doc) }
{-# INLINABLE wrap_AnnotatedType #-}
wrap_AnnotatedType :: T_AnnotatedType  -> Inh_AnnotatedType  -> (Syn_AnnotatedType )
wrap_AnnotatedType (T_AnnotatedType act) (Inh_AnnotatedType ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg7 = T_AnnotatedType_vIn7 
        (T_AnnotatedType_vOut7 _lhsOtext) <- return (inv_AnnotatedType_s8 sem arg7)
        return (Syn_AnnotatedType _lhsOtext)
   )

-- cata
{-# INLINE sem_AnnotatedType #-}
sem_AnnotatedType :: AnnotatedType  -> T_AnnotatedType 
sem_AnnotatedType ( AnnotatedType_AnnotatedType range_ strict_ type_ ) = sem_AnnotatedType_AnnotatedType ( sem_Range range_ ) strict_ ( sem_Type type_ )

-- semantic domain
newtype T_AnnotatedType  = T_AnnotatedType {
                                           attach_T_AnnotatedType :: Identity (T_AnnotatedType_s8 )
                                           }
newtype T_AnnotatedType_s8  = C_AnnotatedType_s8 {
                                                 inv_AnnotatedType_s8 :: (T_AnnotatedType_v7 )
                                                 }
data T_AnnotatedType_s9  = C_AnnotatedType_s9
type T_AnnotatedType_v7  = (T_AnnotatedType_vIn7 ) -> (T_AnnotatedType_vOut7 )
data T_AnnotatedType_vIn7  = T_AnnotatedType_vIn7 
data T_AnnotatedType_vOut7  = T_AnnotatedType_vOut7 (Doc)
{-# NOINLINE sem_AnnotatedType_AnnotatedType #-}
sem_AnnotatedType_AnnotatedType :: T_Range  -> (Bool) -> T_Type  -> T_AnnotatedType 
sem_AnnotatedType_AnnotatedType arg_range_ arg_strict_ arg_type_ = T_AnnotatedType (return st8) where
   {-# NOINLINE st8 #-}
   st8 = let
      v7 :: T_AnnotatedType_v7 
      v7 = \ (T_AnnotatedType_vIn7 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule9 _typeItext arg_strict_
         _lhsOtext :: Doc
         _lhsOtext = rule10 _text
         __result_ = T_AnnotatedType_vOut7 _lhsOtext
         in __result_ )
     in C_AnnotatedType_s8 v7
   {-# INLINE rule9 #-}
   rule9 = \ ((_typeItext) :: Doc) strict_ ->
                                   (if strict_ then (text "!" <+>) else id) _typeItext
   {-# INLINE rule10 #-}
   rule10 = \ _text ->
     _text

-- AnnotatedTypes ----------------------------------------------
-- wrapper
data Inh_AnnotatedTypes  = Inh_AnnotatedTypes {  }
data Syn_AnnotatedTypes  = Syn_AnnotatedTypes { text_Syn_AnnotatedTypes :: ( [       Doc ] ) }
{-# INLINABLE wrap_AnnotatedTypes #-}
wrap_AnnotatedTypes :: T_AnnotatedTypes  -> Inh_AnnotatedTypes  -> (Syn_AnnotatedTypes )
wrap_AnnotatedTypes (T_AnnotatedTypes act) (Inh_AnnotatedTypes ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg10 = T_AnnotatedTypes_vIn10 
        (T_AnnotatedTypes_vOut10 _lhsOtext) <- return (inv_AnnotatedTypes_s11 sem arg10)
        return (Syn_AnnotatedTypes _lhsOtext)
   )

-- cata
{-# NOINLINE sem_AnnotatedTypes #-}
sem_AnnotatedTypes :: AnnotatedTypes  -> T_AnnotatedTypes 
sem_AnnotatedTypes list = Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list)

-- semantic domain
newtype T_AnnotatedTypes  = T_AnnotatedTypes {
                                             attach_T_AnnotatedTypes :: Identity (T_AnnotatedTypes_s11 )
                                             }
newtype T_AnnotatedTypes_s11  = C_AnnotatedTypes_s11 {
                                                     inv_AnnotatedTypes_s11 :: (T_AnnotatedTypes_v10 )
                                                     }
data T_AnnotatedTypes_s12  = C_AnnotatedTypes_s12
type T_AnnotatedTypes_v10  = (T_AnnotatedTypes_vIn10 ) -> (T_AnnotatedTypes_vOut10 )
data T_AnnotatedTypes_vIn10  = T_AnnotatedTypes_vIn10 
data T_AnnotatedTypes_vOut10  = T_AnnotatedTypes_vOut10 ( [       Doc ] )
{-# NOINLINE sem_AnnotatedTypes_Cons #-}
sem_AnnotatedTypes_Cons :: T_AnnotatedType  -> T_AnnotatedTypes  -> T_AnnotatedTypes 
sem_AnnotatedTypes_Cons arg_hd_ arg_tl_ = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 ) -> ( let
         _hdX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_hd_))
         _tlX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_tl_))
         (T_AnnotatedType_vOut7 _hdItext) = inv_AnnotatedType_s8 _hdX8 (T_AnnotatedType_vIn7 )
         (T_AnnotatedTypes_vOut10 _tlItext) = inv_AnnotatedTypes_s11 _tlX11 (T_AnnotatedTypes_vIn10 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule11 _hdItext _tlItext
         __result_ = T_AnnotatedTypes_vOut10 _lhsOtext
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule11 #-}
   rule11 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_AnnotatedTypes_Nil #-}
sem_AnnotatedTypes_Nil ::  T_AnnotatedTypes 
sem_AnnotatedTypes_Nil  = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule12  ()
         __result_ = T_AnnotatedTypes_vOut10 _lhsOtext
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule12 #-}
   rule12 = \  (_ :: ()) ->
     []

-- Body --------------------------------------------------------
-- wrapper
data Inh_Body  = Inh_Body {  }
data Syn_Body  = Syn_Body { text_Syn_Body :: (Doc) }
{-# INLINABLE wrap_Body #-}
wrap_Body :: T_Body  -> Inh_Body  -> (Syn_Body )
wrap_Body (T_Body act) (Inh_Body ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg13 = T_Body_vIn13 
        (T_Body_vOut13 _lhsOtext) <- return (inv_Body_s14 sem arg13)
        return (Syn_Body _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Body #-}
sem_Body :: Body  -> T_Body 
sem_Body ( Body_Hole range_ id_ ) = sem_Body_Hole ( sem_Range range_ ) id_
sem_Body ( Body_Body range_ importdeclarations_ declarations_ ) = sem_Body_Body ( sem_Range range_ ) ( sem_ImportDeclarations importdeclarations_ ) ( sem_Declarations declarations_ )

-- semantic domain
newtype T_Body  = T_Body {
                         attach_T_Body :: Identity (T_Body_s14 )
                         }
newtype T_Body_s14  = C_Body_s14 {
                                 inv_Body_s14 :: (T_Body_v13 )
                                 }
data T_Body_s15  = C_Body_s15
type T_Body_v13  = (T_Body_vIn13 ) -> (T_Body_vOut13 )
data T_Body_vIn13  = T_Body_vIn13 
data T_Body_vOut13  = T_Body_vOut13 (Doc)
{-# NOINLINE sem_Body_Hole #-}
sem_Body_Hole :: T_Range  -> (Integer) -> T_Body 
sem_Body_Hole arg_range_ _ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule13  ()
         _lhsOtext :: Doc
         _lhsOtext = rule14 _text
         __result_ = T_Body_vOut13 _lhsOtext
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule13 #-}
   rule13 = \  (_ :: ()) ->
                                            text hole
   {-# INLINE rule14 #-}
   rule14 = \ _text ->
     _text
{-# NOINLINE sem_Body_Body #-}
sem_Body_Body :: T_Range  -> T_ImportDeclarations  -> T_Declarations  -> T_Body 
sem_Body_Body arg_range_ arg_importdeclarations_ arg_declarations_ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _importdeclarationsX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_importdeclarations_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ImportDeclarations_vOut73 _importdeclarationsItext) = inv_ImportDeclarations_s74 _importdeclarationsX74 (T_ImportDeclarations_vIn73 )
         (T_Declarations_vOut31 _declarationsItext) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 )
         _text = rule15 _declarationsItext _importdeclarationsItext
         _lhsOtext :: Doc
         _lhsOtext = rule16 _text
         __result_ = T_Body_vOut13 _lhsOtext
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule15 #-}
   rule15 = \ ((_declarationsItext) ::  [       Doc ] ) ((_importdeclarationsItext) ::  [       Doc ] ) ->
                                             vcat
                                                      (   _importdeclarationsItext
                                                      ++                        _declarationsItext
                                                      )
   {-# INLINE rule16 #-}
   rule16 = \ _text ->
     _text

-- Constructor -------------------------------------------------
-- wrapper
data Inh_Constructor  = Inh_Constructor {  }
data Syn_Constructor  = Syn_Constructor { text_Syn_Constructor :: (Doc) }
{-# INLINABLE wrap_Constructor #-}
wrap_Constructor :: T_Constructor  -> Inh_Constructor  -> (Syn_Constructor )
wrap_Constructor (T_Constructor act) (Inh_Constructor ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg16 = T_Constructor_vIn16 
        (T_Constructor_vOut16 _lhsOtext) <- return (inv_Constructor_s17 sem arg16)
        return (Syn_Constructor _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Constructor #-}
sem_Constructor :: Constructor  -> T_Constructor 
sem_Constructor ( Constructor_Constructor range_ constructor_ types_ ) = sem_Constructor_Constructor ( sem_Range range_ ) ( sem_Name constructor_ ) ( sem_AnnotatedTypes types_ )
sem_Constructor ( Constructor_Infix range_ leftType_ constructorOperator_ rightType_ ) = sem_Constructor_Infix ( sem_Range range_ ) ( sem_AnnotatedType leftType_ ) ( sem_Name constructorOperator_ ) ( sem_AnnotatedType rightType_ )
sem_Constructor ( Constructor_Record range_ constructor_ fieldDeclarations_ ) = sem_Constructor_Record ( sem_Range range_ ) ( sem_Name constructor_ ) ( sem_FieldDeclarations fieldDeclarations_ )

-- semantic domain
newtype T_Constructor  = T_Constructor {
                                       attach_T_Constructor :: Identity (T_Constructor_s17 )
                                       }
newtype T_Constructor_s17  = C_Constructor_s17 {
                                               inv_Constructor_s17 :: (T_Constructor_v16 )
                                               }
data T_Constructor_s18  = C_Constructor_s18
type T_Constructor_v16  = (T_Constructor_vIn16 ) -> (T_Constructor_vOut16 )
data T_Constructor_vIn16  = T_Constructor_vIn16 
data T_Constructor_vOut16  = T_Constructor_vOut16 (Doc)
{-# NOINLINE sem_Constructor_Constructor #-}
sem_Constructor_Constructor :: T_Range  -> T_Name  -> T_AnnotatedTypes  -> T_Constructor 
sem_Constructor_Constructor arg_range_ arg_constructor_ arg_types_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _typesX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_types_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIisIdentifier _constructorIisOperator _constructorIisSpecial _constructorItext) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_AnnotatedTypes_vOut10 _typesItext) = inv_AnnotatedTypes_s11 _typesX11 (T_AnnotatedTypes_vIn10 )
         _text = rule17 _constructorIisOperator _constructorItext _typesItext
         _lhsOtext :: Doc
         _lhsOtext = rule18 _text
         __result_ = T_Constructor_vOut16 _lhsOtext
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule17 #-}
   rule17 = \ ((_constructorIisOperator) :: Bool) ((_constructorItext) :: Doc) ((_typesItext) ::  [       Doc ] ) ->
                                     foldl (<+>) (parensIf _constructorIisOperator _constructorItext) _typesItext
   {-# INLINE rule18 #-}
   rule18 = \ _text ->
     _text
{-# NOINLINE sem_Constructor_Infix #-}
sem_Constructor_Infix :: T_Range  -> T_AnnotatedType  -> T_Name  -> T_AnnotatedType  -> T_Constructor 
sem_Constructor_Infix arg_range_ arg_leftType_ arg_constructorOperator_ arg_rightType_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_leftType_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_rightType_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_AnnotatedType_vOut7 _leftTypeItext) = inv_AnnotatedType_s8 _leftTypeX8 (T_AnnotatedType_vIn7 )
         (T_Name_vOut112 _constructorOperatorIisIdentifier _constructorOperatorIisOperator _constructorOperatorIisSpecial _constructorOperatorItext) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_AnnotatedType_vOut7 _rightTypeItext) = inv_AnnotatedType_s8 _rightTypeX8 (T_AnnotatedType_vIn7 )
         _text = rule19 _constructorOperatorItext _leftTypeItext _rightTypeItext
         _lhsOtext :: Doc
         _lhsOtext = rule20 _text
         __result_ = T_Constructor_vOut16 _lhsOtext
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule19 #-}
   rule19 = \ ((_constructorOperatorItext) :: Doc) ((_leftTypeItext) :: Doc) ((_rightTypeItext) :: Doc) ->
                                     _leftTypeItext <+> _constructorOperatorItext <+> _rightTypeItext
   {-# INLINE rule20 #-}
   rule20 = \ _text ->
     _text
{-# NOINLINE sem_Constructor_Record #-}
sem_Constructor_Record :: T_Range  -> T_Name  -> T_FieldDeclarations  -> T_Constructor 
sem_Constructor_Record arg_range_ arg_constructor_ arg_fieldDeclarations_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _fieldDeclarationsX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_fieldDeclarations_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIisIdentifier _constructorIisOperator _constructorIisSpecial _constructorItext) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_FieldDeclarations_vOut49 _fieldDeclarationsItext) = inv_FieldDeclarations_s50 _fieldDeclarationsX50 (T_FieldDeclarations_vIn49 )
         _text = rule21  ()
         _lhsOtext :: Doc
         _lhsOtext = rule22 _text
         __result_ = T_Constructor_vOut16 _lhsOtext
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule21 #-}
   rule21 = \  (_ :: ()) ->
                                     text "{- !!! record constructor -}"
   {-# INLINE rule22 #-}
   rule22 = \ _text ->
     _text

-- Constructors ------------------------------------------------
-- wrapper
data Inh_Constructors  = Inh_Constructors {  }
data Syn_Constructors  = Syn_Constructors { text_Syn_Constructors :: ( [       Doc ] ) }
{-# INLINABLE wrap_Constructors #-}
wrap_Constructors :: T_Constructors  -> Inh_Constructors  -> (Syn_Constructors )
wrap_Constructors (T_Constructors act) (Inh_Constructors ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg19 = T_Constructors_vIn19 
        (T_Constructors_vOut19 _lhsOtext) <- return (inv_Constructors_s20 sem arg19)
        return (Syn_Constructors _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Constructors #-}
sem_Constructors :: Constructors  -> T_Constructors 
sem_Constructors list = Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list)

-- semantic domain
newtype T_Constructors  = T_Constructors {
                                         attach_T_Constructors :: Identity (T_Constructors_s20 )
                                         }
newtype T_Constructors_s20  = C_Constructors_s20 {
                                                 inv_Constructors_s20 :: (T_Constructors_v19 )
                                                 }
data T_Constructors_s21  = C_Constructors_s21
type T_Constructors_v19  = (T_Constructors_vIn19 ) -> (T_Constructors_vOut19 )
data T_Constructors_vIn19  = T_Constructors_vIn19 
data T_Constructors_vOut19  = T_Constructors_vOut19 ( [       Doc ] )
{-# NOINLINE sem_Constructors_Cons #-}
sem_Constructors_Cons :: T_Constructor  -> T_Constructors  -> T_Constructors 
sem_Constructors_Cons arg_hd_ arg_tl_ = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 ) -> ( let
         _hdX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_hd_))
         _tlX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_tl_))
         (T_Constructor_vOut16 _hdItext) = inv_Constructor_s17 _hdX17 (T_Constructor_vIn16 )
         (T_Constructors_vOut19 _tlItext) = inv_Constructors_s20 _tlX20 (T_Constructors_vIn19 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule23 _hdItext _tlItext
         __result_ = T_Constructors_vOut19 _lhsOtext
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule23 #-}
   rule23 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Constructors_Nil #-}
sem_Constructors_Nil ::  T_Constructors 
sem_Constructors_Nil  = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule24  ()
         __result_ = T_Constructors_vOut19 _lhsOtext
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule24 #-}
   rule24 = \  (_ :: ()) ->
     []

-- ContextItem -------------------------------------------------
-- wrapper
data Inh_ContextItem  = Inh_ContextItem {  }
data Syn_ContextItem  = Syn_ContextItem { text_Syn_ContextItem :: (Doc) }
{-# INLINABLE wrap_ContextItem #-}
wrap_ContextItem :: T_ContextItem  -> Inh_ContextItem  -> (Syn_ContextItem )
wrap_ContextItem (T_ContextItem act) (Inh_ContextItem ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg22 = T_ContextItem_vIn22 
        (T_ContextItem_vOut22 _lhsOtext) <- return (inv_ContextItem_s23 sem arg22)
        return (Syn_ContextItem _lhsOtext)
   )

-- cata
{-# NOINLINE sem_ContextItem #-}
sem_ContextItem :: ContextItem  -> T_ContextItem 
sem_ContextItem ( ContextItem_ContextItem range_ name_ types_ ) = sem_ContextItem_ContextItem ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Types types_ )

-- semantic domain
newtype T_ContextItem  = T_ContextItem {
                                       attach_T_ContextItem :: Identity (T_ContextItem_s23 )
                                       }
newtype T_ContextItem_s23  = C_ContextItem_s23 {
                                               inv_ContextItem_s23 :: (T_ContextItem_v22 )
                                               }
data T_ContextItem_s24  = C_ContextItem_s24
type T_ContextItem_v22  = (T_ContextItem_vIn22 ) -> (T_ContextItem_vOut22 )
data T_ContextItem_vIn22  = T_ContextItem_vIn22 
data T_ContextItem_vOut22  = T_ContextItem_vOut22 (Doc)
{-# NOINLINE sem_ContextItem_ContextItem #-}
sem_ContextItem_ContextItem :: T_Range  -> T_Name  -> T_Types  -> T_ContextItem 
sem_ContextItem_ContextItem arg_range_ arg_name_ arg_types_ = T_ContextItem (return st23) where
   {-# NOINLINE st23 #-}
   st23 = let
      v22 :: T_ContextItem_v22 
      v22 = \ (T_ContextItem_vIn22 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesItext) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         _text = rule25 _nameItext _typesItext
         _lhsOtext :: Doc
         _lhsOtext = rule26 _text
         __result_ = T_ContextItem_vOut22 _lhsOtext
         in __result_ )
     in C_ContextItem_s23 v22
   {-# INLINE rule25 #-}
   rule25 = \ ((_nameItext) :: Doc) ((_typesItext) ::  [       Doc ] ) ->
                                     _nameItext <+> head _typesItext
   {-# INLINE rule26 #-}
   rule26 = \ _text ->
     _text

-- ContextItems ------------------------------------------------
-- wrapper
data Inh_ContextItems  = Inh_ContextItems {  }
data Syn_ContextItems  = Syn_ContextItems { text_Syn_ContextItems :: ( [       Doc ] ) }
{-# INLINABLE wrap_ContextItems #-}
wrap_ContextItems :: T_ContextItems  -> Inh_ContextItems  -> (Syn_ContextItems )
wrap_ContextItems (T_ContextItems act) (Inh_ContextItems ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg25 = T_ContextItems_vIn25 
        (T_ContextItems_vOut25 _lhsOtext) <- return (inv_ContextItems_s26 sem arg25)
        return (Syn_ContextItems _lhsOtext)
   )

-- cata
{-# NOINLINE sem_ContextItems #-}
sem_ContextItems :: ContextItems  -> T_ContextItems 
sem_ContextItems list = Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list)

-- semantic domain
newtype T_ContextItems  = T_ContextItems {
                                         attach_T_ContextItems :: Identity (T_ContextItems_s26 )
                                         }
newtype T_ContextItems_s26  = C_ContextItems_s26 {
                                                 inv_ContextItems_s26 :: (T_ContextItems_v25 )
                                                 }
data T_ContextItems_s27  = C_ContextItems_s27
type T_ContextItems_v25  = (T_ContextItems_vIn25 ) -> (T_ContextItems_vOut25 )
data T_ContextItems_vIn25  = T_ContextItems_vIn25 
data T_ContextItems_vOut25  = T_ContextItems_vOut25 ( [       Doc ] )
{-# NOINLINE sem_ContextItems_Cons #-}
sem_ContextItems_Cons :: T_ContextItem  -> T_ContextItems  -> T_ContextItems 
sem_ContextItems_Cons arg_hd_ arg_tl_ = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 ) -> ( let
         _hdX23 = Control.Monad.Identity.runIdentity (attach_T_ContextItem (arg_hd_))
         _tlX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_tl_))
         (T_ContextItem_vOut22 _hdItext) = inv_ContextItem_s23 _hdX23 (T_ContextItem_vIn22 )
         (T_ContextItems_vOut25 _tlItext) = inv_ContextItems_s26 _tlX26 (T_ContextItems_vIn25 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule27 _hdItext _tlItext
         __result_ = T_ContextItems_vOut25 _lhsOtext
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule27 #-}
   rule27 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_ContextItems_Nil #-}
sem_ContextItems_Nil ::  T_ContextItems 
sem_ContextItems_Nil  = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule28  ()
         __result_ = T_ContextItems_vOut25 _lhsOtext
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule28 #-}
   rule28 = \  (_ :: ()) ->
     []

-- Declaration -------------------------------------------------
-- wrapper
data Inh_Declaration  = Inh_Declaration {  }
data Syn_Declaration  = Syn_Declaration { text_Syn_Declaration :: (Doc) }
{-# INLINABLE wrap_Declaration #-}
wrap_Declaration :: T_Declaration  -> Inh_Declaration  -> (Syn_Declaration )
wrap_Declaration (T_Declaration act) (Inh_Declaration ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg28 = T_Declaration_vIn28 
        (T_Declaration_vOut28 _lhsOtext) <- return (inv_Declaration_s29 sem arg28)
        return (Syn_Declaration _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Declaration #-}
sem_Declaration :: Declaration  -> T_Declaration 
sem_Declaration ( Declaration_Hole range_ id_ ) = sem_Declaration_Hole ( sem_Range range_ ) id_
sem_Declaration ( Declaration_Type range_ simpletype_ type_ ) = sem_Declaration_Type ( sem_Range range_ ) ( sem_SimpleType simpletype_ ) ( sem_Type type_ )
sem_Declaration ( Declaration_Data range_ context_ simpletype_ constructors_ derivings_ ) = sem_Declaration_Data ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_Constructors constructors_ ) ( sem_Names derivings_ )
sem_Declaration ( Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_ ) = sem_Declaration_Newtype ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_Constructor constructor_ ) ( sem_Names derivings_ )
sem_Declaration ( Declaration_Class range_ context_ simpletype_ where_ ) = sem_Declaration_Class ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_MaybeDeclarations where_ )
sem_Declaration ( Declaration_Instance range_ context_ name_ types_ where_ ) = sem_Declaration_Instance ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_Name name_ ) ( sem_Types types_ ) ( sem_MaybeDeclarations where_ )
sem_Declaration ( Declaration_Default range_ types_ ) = sem_Declaration_Default ( sem_Range range_ ) ( sem_Types types_ )
sem_Declaration ( Declaration_FunctionBindings range_ bindings_ ) = sem_Declaration_FunctionBindings ( sem_Range range_ ) ( sem_FunctionBindings bindings_ )
sem_Declaration ( Declaration_PatternBinding range_ pattern_ righthandside_ ) = sem_Declaration_PatternBinding ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_RightHandSide righthandside_ )
sem_Declaration ( Declaration_TypeSignature range_ names_ type_ ) = sem_Declaration_TypeSignature ( sem_Range range_ ) ( sem_Names names_ ) ( sem_Type type_ )
sem_Declaration ( Declaration_Fixity range_ fixity_ priority_ operators_ ) = sem_Declaration_Fixity ( sem_Range range_ ) ( sem_Fixity fixity_ ) ( sem_MaybeInt priority_ ) ( sem_Names operators_ )
sem_Declaration ( Declaration_Empty range_ ) = sem_Declaration_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Declaration  = T_Declaration {
                                       attach_T_Declaration :: Identity (T_Declaration_s29 )
                                       }
newtype T_Declaration_s29  = C_Declaration_s29 {
                                               inv_Declaration_s29 :: (T_Declaration_v28 )
                                               }
data T_Declaration_s30  = C_Declaration_s30
type T_Declaration_v28  = (T_Declaration_vIn28 ) -> (T_Declaration_vOut28 )
data T_Declaration_vIn28  = T_Declaration_vIn28 
data T_Declaration_vOut28  = T_Declaration_vOut28 (Doc)
{-# NOINLINE sem_Declaration_Hole #-}
sem_Declaration_Hole :: T_Range  -> (Integer) -> T_Declaration 
sem_Declaration_Hole arg_range_ _ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule29  ()
         _lhsOtext :: Doc
         _lhsOtext = rule30 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule29 #-}
   rule29 = \  (_ :: ()) ->
                                     text hole
   {-# INLINE rule30 #-}
   rule30 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Type #-}
sem_Declaration_Type :: T_Range  -> T_SimpleType  -> T_Type  -> T_Declaration 
sem_Declaration_Type arg_range_ arg_simpletype_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_SimpleType_vOut151 _simpletypeItext) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule31 _simpletypeItext _typeItext
         _lhsOtext :: Doc
         _lhsOtext = rule32 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule31 #-}
   rule31 = \ ((_simpletypeItext) :: Doc) ((_typeItext) :: Doc) ->
                                     text "type" <+> _simpletypeItext <+> text "=" <+> _typeItext
   {-# INLINE rule32 #-}
   rule32 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Data #-}
sem_Declaration_Data :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructors  -> T_Names  -> T_Declaration 
sem_Declaration_Data arg_range_ arg_context_ arg_simpletype_ arg_constructors_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorsX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_constructors_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextItext) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeItext) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructors_vOut19 _constructorsItext) = inv_Constructors_s20 _constructorsX20 (T_Constructors_vIn19 )
         (T_Names_vOut115 _derivingsIisIdentifier _derivingsIisOperator _derivingsIisSpecial _derivingsItext) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _text = rule33 _constructorsItext _contextDoc _derivingDoc _simpletypeItext
         _contextDoc = rule34 _contextItext
         _derivingDoc = rule35 _derivingsItext
         _lhsOtext :: Doc
         _lhsOtext = rule36 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule33 #-}
   rule33 = \ ((_constructorsItext) ::  [       Doc ] ) _contextDoc _derivingDoc ((_simpletypeItext) :: Doc) ->
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
   {-# INLINE rule34 #-}
   rule34 = \ ((_contextItext) ::  [       Doc ] ) ->
                                             case _contextItext of
                                              []  -> empty
                                              [x] -> x <+> text "=>" <+> empty
                                              xs  -> tupled xs <+> text "=>" <+> empty
   {-# INLINE rule35 #-}
   rule35 = \ ((_derivingsItext) ::  [       Doc ] ) ->
                              if null _derivingsItext then
                                  empty
                              else
                                  (    empty
                                  <+>  text "deriving"
                                  <+>  tupledUnit _derivingsItext
                                  )
   {-# INLINE rule36 #-}
   rule36 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Newtype #-}
sem_Declaration_Newtype :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructor  -> T_Names  -> T_Declaration 
sem_Declaration_Newtype arg_range_ arg_context_ arg_simpletype_ arg_constructor_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_constructor_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextItext) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeItext) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructor_vOut16 _constructorItext) = inv_Constructor_s17 _constructorX17 (T_Constructor_vIn16 )
         (T_Names_vOut115 _derivingsIisIdentifier _derivingsIisOperator _derivingsIisSpecial _derivingsItext) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _text = rule37 _constructorItext _contextDoc _derivingDoc _simpletypeItext
         _contextDoc = rule38 _contextItext
         _derivingDoc = rule39 _derivingsItext
         _lhsOtext :: Doc
         _lhsOtext = rule40 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule37 #-}
   rule37 = \ ((_constructorItext) :: Doc) _contextDoc _derivingDoc ((_simpletypeItext) :: Doc) ->
                                      text "newtype"
                                      <+>
                                      _contextDoc
                                      <>
                                      _simpletypeItext
                                      <+>
                                      _constructorItext
                                      <>
                                      _derivingDoc
   {-# INLINE rule38 #-}
   rule38 = \ ((_contextItext) ::  [       Doc ] ) ->
                                             case _contextItext of
                                              []  -> empty
                                              [x] -> x <+> text "=>" <+> empty
                                              xs  -> tupled xs <+> text "=>" <+> empty
   {-# INLINE rule39 #-}
   rule39 = \ ((_derivingsItext) ::  [       Doc ] ) ->
                              if null _derivingsItext then
                                  empty
                              else
                                  (    empty
                                  <+>  text "deriving"
                                  <+>  tupledUnit _derivingsItext
                                  )
   {-# INLINE rule40 #-}
   rule40 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Class #-}
sem_Declaration_Class :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Class arg_range_ arg_context_ arg_simpletype_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextItext) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeItext) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_MaybeDeclarations_vOut88 _whereItext) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 )
         _text = rule41  ()
         _lhsOtext :: Doc
         _lhsOtext = rule42 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule41 #-}
   rule41 = \  (_ :: ()) ->
                                     text "{- !!! class decl -}"
   {-# INLINE rule42 #-}
   rule42 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Instance #-}
sem_Declaration_Instance :: T_Range  -> T_ContextItems  -> T_Name  -> T_Types  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Instance arg_range_ arg_context_ arg_name_ arg_types_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextItext) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesItext) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         (T_MaybeDeclarations_vOut88 _whereItext) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 )
         _text = rule43  ()
         _lhsOtext :: Doc
         _lhsOtext = rule44 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule43 #-}
   rule43 = \  (_ :: ()) ->
                                     text "{- !!! instance decl -}"
   {-# INLINE rule44 #-}
   rule44 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Default #-}
sem_Declaration_Default :: T_Range  -> T_Types  -> T_Declaration 
sem_Declaration_Default arg_range_ arg_types_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Types_vOut166 _typesItext) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         _text = rule45 _typesItext
         _lhsOtext :: Doc
         _lhsOtext = rule46 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule45 #-}
   rule45 = \ ((_typesItext) ::  [       Doc ] ) ->
                                     text "default" <+> tupled _typesItext
   {-# INLINE rule46 #-}
   rule46 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_FunctionBindings #-}
sem_Declaration_FunctionBindings :: T_Range  -> T_FunctionBindings  -> T_Declaration 
sem_Declaration_FunctionBindings arg_range_ arg_bindings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _bindingsX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_bindings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBindings_vOut58 _bindingsItext) = inv_FunctionBindings_s59 _bindingsX59 (T_FunctionBindings_vIn58 )
         _text = rule47 _bindingsItext
         _lhsOtext :: Doc
         _lhsOtext = rule48 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule47 #-}
   rule47 = \ ((_bindingsItext) ::  [       Doc ] ) ->
           case filter ((/= "") . show) _bindingsItext of
              [] -> text hole
              xs -> foldl1  (<$>) xs
   {-# INLINE rule48 #-}
   rule48 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_PatternBinding #-}
sem_Declaration_PatternBinding :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Declaration 
sem_Declaration_PatternBinding arg_range_ arg_pattern_ arg_righthandside_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_RightHandSide_vOut148 _righthandsideItext) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 )
         _text = rule49 _patternItext _righthandsideItext
         _lhsOtext :: Doc
         _lhsOtext = rule50 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule49 #-}
   rule49 = \ ((_patternItext) :: Doc) ((_righthandsideItext) ::  Doc        -> Doc  ) ->
                                     _patternItext <+> _righthandsideItext (text "=")
   {-# INLINE rule50 #-}
   rule50 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_TypeSignature #-}
sem_Declaration_TypeSignature :: T_Range  -> T_Names  -> T_Type  -> T_Declaration 
sem_Declaration_TypeSignature arg_range_ arg_names_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesIisIdentifier _namesIisOperator _namesIisSpecial _namesItext) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule51 _namesDocs _typeItext
         _namesDocs = rule52 _namesIisOperator _namesItext
         _lhsOtext :: Doc
         _lhsOtext = rule53 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule51 #-}
   rule51 = \ _namesDocs ((_typeItext) :: Doc) ->
                                     commas _namesDocs <+> text "::" <+> _typeItext
   {-# INLINE rule52 #-}
   rule52 = \ ((_namesIisOperator) ::  [Bool] ) ((_namesItext) ::  [       Doc ] ) ->
                                 parensIfList _namesIisOperator _namesItext
   {-# INLINE rule53 #-}
   rule53 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Fixity #-}
sem_Declaration_Fixity :: T_Range  -> T_Fixity  -> T_MaybeInt  -> T_Names  -> T_Declaration 
sem_Declaration_Fixity arg_range_ arg_fixity_ arg_priority_ arg_operators_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fixityX53 = Control.Monad.Identity.runIdentity (attach_T_Fixity (arg_fixity_))
         _priorityX101 = Control.Monad.Identity.runIdentity (attach_T_MaybeInt (arg_priority_))
         _operatorsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_operators_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Fixity_vOut52 _fixityItext) = inv_Fixity_s53 _fixityX53 (T_Fixity_vIn52 )
         (T_MaybeInt_vOut100 _priorityItext) = inv_MaybeInt_s101 _priorityX101 (T_MaybeInt_vIn100 )
         (T_Names_vOut115 _operatorsIisIdentifier _operatorsIisOperator _operatorsIisSpecial _operatorsItext) = inv_Names_s116 _operatorsX116 (T_Names_vIn115 )
         _text = rule54 _fixityItext _ops
         _ops = rule55 _operatorsIisIdentifier _operatorsItext _priorityItext
         _lhsOtext :: Doc
         _lhsOtext = rule56 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule54 #-}
   rule54 = \ ((_fixityItext) :: Doc) _ops ->
                                     _fixityItext <+> _ops
   {-# INLINE rule55 #-}
   rule55 = \ ((_operatorsIisIdentifier) ::  [Bool] ) ((_operatorsItext) ::  [       Doc ] ) ((_priorityItext) ::         Maybe Doc  ) ->
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
   {-# INLINE rule56 #-}
   rule56 = \ _text ->
     _text
{-# NOINLINE sem_Declaration_Empty #-}
sem_Declaration_Empty :: T_Range  -> T_Declaration 
sem_Declaration_Empty arg_range_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule57  ()
         _lhsOtext :: Doc
         _lhsOtext = rule58 _text
         __result_ = T_Declaration_vOut28 _lhsOtext
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule57 #-}
   rule57 = \  (_ :: ()) ->
                                     empty
   {-# INLINE rule58 #-}
   rule58 = \ _text ->
     _text

-- Declarations ------------------------------------------------
-- wrapper
data Inh_Declarations  = Inh_Declarations {  }
data Syn_Declarations  = Syn_Declarations { text_Syn_Declarations :: ( [       Doc ] ) }
{-# INLINABLE wrap_Declarations #-}
wrap_Declarations :: T_Declarations  -> Inh_Declarations  -> (Syn_Declarations )
wrap_Declarations (T_Declarations act) (Inh_Declarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg31 = T_Declarations_vIn31 
        (T_Declarations_vOut31 _lhsOtext) <- return (inv_Declarations_s32 sem arg31)
        return (Syn_Declarations _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Declarations #-}
sem_Declarations :: Declarations  -> T_Declarations 
sem_Declarations list = Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list)

-- semantic domain
newtype T_Declarations  = T_Declarations {
                                         attach_T_Declarations :: Identity (T_Declarations_s32 )
                                         }
newtype T_Declarations_s32  = C_Declarations_s32 {
                                                 inv_Declarations_s32 :: (T_Declarations_v31 )
                                                 }
data T_Declarations_s33  = C_Declarations_s33
type T_Declarations_v31  = (T_Declarations_vIn31 ) -> (T_Declarations_vOut31 )
data T_Declarations_vIn31  = T_Declarations_vIn31 
data T_Declarations_vOut31  = T_Declarations_vOut31 ( [       Doc ] )
{-# NOINLINE sem_Declarations_Cons #-}
sem_Declarations_Cons :: T_Declaration  -> T_Declarations  -> T_Declarations 
sem_Declarations_Cons arg_hd_ arg_tl_ = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 ) -> ( let
         _hdX29 = Control.Monad.Identity.runIdentity (attach_T_Declaration (arg_hd_))
         _tlX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_tl_))
         (T_Declaration_vOut28 _hdItext) = inv_Declaration_s29 _hdX29 (T_Declaration_vIn28 )
         (T_Declarations_vOut31 _tlItext) = inv_Declarations_s32 _tlX32 (T_Declarations_vIn31 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule59 _hdItext _tlItext
         __result_ = T_Declarations_vOut31 _lhsOtext
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule59 #-}
   rule59 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Declarations_Nil #-}
sem_Declarations_Nil ::  T_Declarations 
sem_Declarations_Nil  = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule60  ()
         __result_ = T_Declarations_vOut31 _lhsOtext
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule60 #-}
   rule60 = \  (_ :: ()) ->
     []

-- Export ------------------------------------------------------
-- wrapper
data Inh_Export  = Inh_Export {  }
data Syn_Export  = Syn_Export { text_Syn_Export :: (Doc) }
{-# INLINABLE wrap_Export #-}
wrap_Export :: T_Export  -> Inh_Export  -> (Syn_Export )
wrap_Export (T_Export act) (Inh_Export ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg34 = T_Export_vIn34 
        (T_Export_vOut34 _lhsOtext) <- return (inv_Export_s35 sem arg34)
        return (Syn_Export _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Export #-}
sem_Export :: Export  -> T_Export 
sem_Export ( Export_Variable range_ name_ ) = sem_Export_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Export ( Export_TypeOrClass range_ name_ names_ ) = sem_Export_TypeOrClass ( sem_Range range_ ) ( sem_Name name_ ) ( sem_MaybeNames names_ )
sem_Export ( Export_TypeOrClassComplete range_ name_ ) = sem_Export_TypeOrClassComplete ( sem_Range range_ ) ( sem_Name name_ )
sem_Export ( Export_Module range_ name_ ) = sem_Export_Module ( sem_Range range_ ) ( sem_Name name_ )

-- semantic domain
newtype T_Export  = T_Export {
                             attach_T_Export :: Identity (T_Export_s35 )
                             }
newtype T_Export_s35  = C_Export_s35 {
                                     inv_Export_s35 :: (T_Export_v34 )
                                     }
data T_Export_s36  = C_Export_s36
type T_Export_v34  = (T_Export_vIn34 ) -> (T_Export_vOut34 )
data T_Export_vIn34  = T_Export_vIn34 
data T_Export_vOut34  = T_Export_vOut34 (Doc)
{-# NOINLINE sem_Export_Variable #-}
sem_Export_Variable :: T_Range  -> T_Name  -> T_Export 
sem_Export_Variable arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule61 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule62 _text
         __result_ = T_Export_vOut34 _lhsOtext
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule61 #-}
   rule61 = \ ((_nameItext) :: Doc) ->
                                          _nameItext
   {-# INLINE rule62 #-}
   rule62 = \ _text ->
     _text
{-# NOINLINE sem_Export_TypeOrClass #-}
sem_Export_TypeOrClass :: T_Range  -> T_Name  -> T_MaybeNames  -> T_Export 
sem_Export_TypeOrClass arg_range_ arg_name_ arg_names_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _namesX107 = Control.Monad.Identity.runIdentity (attach_T_MaybeNames (arg_names_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeNames_vOut106 _namesItext) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _text = rule63 _nameItext _namesItext
         _lhsOtext :: Doc
         _lhsOtext = rule64 _text
         __result_ = T_Export_vOut34 _lhsOtext
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule63 #-}
   rule63 = \ ((_nameItext) :: Doc) ((_namesItext) ::  Maybe [       Doc ] ) ->
                                          _nameItext <> maybe empty tupled (_namesItext)
   {-# INLINE rule64 #-}
   rule64 = \ _text ->
     _text
{-# NOINLINE sem_Export_TypeOrClassComplete #-}
sem_Export_TypeOrClassComplete :: T_Range  -> T_Name  -> T_Export 
sem_Export_TypeOrClassComplete arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule65 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule66 _text
         __result_ = T_Export_vOut34 _lhsOtext
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule65 #-}
   rule65 = \ ((_nameItext) :: Doc) ->
                                          _nameItext
   {-# INLINE rule66 #-}
   rule66 = \ _text ->
     _text
{-# NOINLINE sem_Export_Module #-}
sem_Export_Module :: T_Range  -> T_Name  -> T_Export 
sem_Export_Module arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule67 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule68 _text
         __result_ = T_Export_vOut34 _lhsOtext
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule67 #-}
   rule67 = \ ((_nameItext) :: Doc) ->
                                          text "module" <+> _nameItext
   {-# INLINE rule68 #-}
   rule68 = \ _text ->
     _text

-- Exports -----------------------------------------------------
-- wrapper
data Inh_Exports  = Inh_Exports {  }
data Syn_Exports  = Syn_Exports { text_Syn_Exports :: ( [       Doc ] ) }
{-# INLINABLE wrap_Exports #-}
wrap_Exports :: T_Exports  -> Inh_Exports  -> (Syn_Exports )
wrap_Exports (T_Exports act) (Inh_Exports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg37 = T_Exports_vIn37 
        (T_Exports_vOut37 _lhsOtext) <- return (inv_Exports_s38 sem arg37)
        return (Syn_Exports _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Exports #-}
sem_Exports :: Exports  -> T_Exports 
sem_Exports list = Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list)

-- semantic domain
newtype T_Exports  = T_Exports {
                               attach_T_Exports :: Identity (T_Exports_s38 )
                               }
newtype T_Exports_s38  = C_Exports_s38 {
                                       inv_Exports_s38 :: (T_Exports_v37 )
                                       }
data T_Exports_s39  = C_Exports_s39
type T_Exports_v37  = (T_Exports_vIn37 ) -> (T_Exports_vOut37 )
data T_Exports_vIn37  = T_Exports_vIn37 
data T_Exports_vOut37  = T_Exports_vOut37 ( [       Doc ] )
{-# NOINLINE sem_Exports_Cons #-}
sem_Exports_Cons :: T_Export  -> T_Exports  -> T_Exports 
sem_Exports_Cons arg_hd_ arg_tl_ = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 ) -> ( let
         _hdX35 = Control.Monad.Identity.runIdentity (attach_T_Export (arg_hd_))
         _tlX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_tl_))
         (T_Export_vOut34 _hdItext) = inv_Export_s35 _hdX35 (T_Export_vIn34 )
         (T_Exports_vOut37 _tlItext) = inv_Exports_s38 _tlX38 (T_Exports_vIn37 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule69 _hdItext _tlItext
         __result_ = T_Exports_vOut37 _lhsOtext
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule69 #-}
   rule69 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Exports_Nil #-}
sem_Exports_Nil ::  T_Exports 
sem_Exports_Nil  = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule70  ()
         __result_ = T_Exports_vOut37 _lhsOtext
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule70 #-}
   rule70 = \  (_ :: ()) ->
     []

-- Expression --------------------------------------------------
-- wrapper
data Inh_Expression  = Inh_Expression {  }
data Syn_Expression  = Syn_Expression { text_Syn_Expression :: (Doc) }
{-# INLINABLE wrap_Expression #-}
wrap_Expression :: T_Expression  -> Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg40 = T_Expression_vIn40 
        (T_Expression_vOut40 _lhsOtext) <- return (inv_Expression_s41 sem arg40)
        return (Syn_Expression _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Expression #-}
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Expression_Hole range_ id_ ) = sem_Expression_Hole ( sem_Range range_ ) id_
sem_Expression ( Expression_Feedback range_ feedback_ expression_ ) = sem_Expression_Feedback ( sem_Range range_ ) feedback_ ( sem_Expression expression_ )
sem_Expression ( Expression_MustUse range_ expression_ ) = sem_Expression_MustUse ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Literal range_ literal_ ) = sem_Expression_Literal ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Expression ( Expression_Variable range_ name_ ) = sem_Expression_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Expression ( Expression_Constructor range_ name_ ) = sem_Expression_Constructor ( sem_Range range_ ) ( sem_Name name_ )
sem_Expression ( Expression_Parenthesized range_ expression_ ) = sem_Expression_Parenthesized ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_NormalApplication range_ function_ arguments_ ) = sem_Expression_NormalApplication ( sem_Range range_ ) ( sem_Expression function_ ) ( sem_Expressions arguments_ )
sem_Expression ( Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_ ) = sem_Expression_InfixApplication ( sem_Range range_ ) ( sem_MaybeExpression leftExpression_ ) ( sem_Expression operator_ ) ( sem_MaybeExpression rightExpression_ )
sem_Expression ( Expression_If range_ guardExpression_ thenExpression_ elseExpression_ ) = sem_Expression_If ( sem_Range range_ ) ( sem_Expression guardExpression_ ) ( sem_Expression thenExpression_ ) ( sem_Expression elseExpression_ )
sem_Expression ( Expression_Lambda range_ patterns_ expression_ ) = sem_Expression_Lambda ( sem_Range range_ ) ( sem_Patterns patterns_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Case range_ expression_ alternatives_ ) = sem_Expression_Case ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Alternatives alternatives_ )
sem_Expression ( Expression_Let range_ declarations_ expression_ ) = sem_Expression_Let ( sem_Range range_ ) ( sem_Declarations declarations_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Do range_ statements_ ) = sem_Expression_Do ( sem_Range range_ ) ( sem_Statements statements_ )
sem_Expression ( Expression_List range_ expressions_ ) = sem_Expression_List ( sem_Range range_ ) ( sem_Expressions expressions_ )
sem_Expression ( Expression_Tuple range_ expressions_ ) = sem_Expression_Tuple ( sem_Range range_ ) ( sem_Expressions expressions_ )
sem_Expression ( Expression_Comprehension range_ expression_ qualifiers_ ) = sem_Expression_Comprehension ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Qualifiers qualifiers_ )
sem_Expression ( Expression_Typed range_ expression_ type_ ) = sem_Expression_Typed ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Type type_ )
sem_Expression ( Expression_RecordConstruction range_ name_ recordExpressionBindings_ ) = sem_Expression_RecordConstruction ( sem_Range range_ ) ( sem_Name name_ ) ( sem_RecordExpressionBindings recordExpressionBindings_ )
sem_Expression ( Expression_RecordUpdate range_ expression_ recordExpressionBindings_ ) = sem_Expression_RecordUpdate ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_RecordExpressionBindings recordExpressionBindings_ )
sem_Expression ( Expression_Enum range_ from_ then_ to_ ) = sem_Expression_Enum ( sem_Range range_ ) ( sem_Expression from_ ) ( sem_MaybeExpression then_ ) ( sem_MaybeExpression to_ )
sem_Expression ( Expression_Negate range_ expression_ ) = sem_Expression_Negate ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_NegateFloat range_ expression_ ) = sem_Expression_NegateFloat ( sem_Range range_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_Expression  = T_Expression {
                                     attach_T_Expression :: Identity (T_Expression_s41 )
                                     }
newtype T_Expression_s41  = C_Expression_s41 {
                                             inv_Expression_s41 :: (T_Expression_v40 )
                                             }
data T_Expression_s42  = C_Expression_s42
type T_Expression_v40  = (T_Expression_vIn40 ) -> (T_Expression_vOut40 )
data T_Expression_vIn40  = T_Expression_vIn40 
data T_Expression_vOut40  = T_Expression_vOut40 (Doc)
{-# NOINLINE sem_Expression_Hole #-}
sem_Expression_Hole :: T_Range  -> (Integer) -> T_Expression 
sem_Expression_Hole arg_range_ _ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule71  ()
         _lhsOtext :: Doc
         _lhsOtext = rule72 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule71 #-}
   rule71 = \  (_ :: ()) ->
                                      text hole
   {-# INLINE rule72 #-}
   rule72 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Feedback #-}
sem_Expression_Feedback :: T_Range  -> (String) -> T_Expression  -> T_Expression 
sem_Expression_Feedback arg_range_ _ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _lhsOtext :: Doc
         _lhsOtext = rule73 _expressionItext
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule73 #-}
   rule73 = \ ((_expressionItext) :: Doc) ->
     _expressionItext
{-# NOINLINE sem_Expression_MustUse #-}
sem_Expression_MustUse :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_MustUse arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _lhsOtext :: Doc
         _lhsOtext = rule74 _expressionItext
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule74 #-}
   rule74 = \ ((_expressionItext) :: Doc) ->
     _expressionItext
{-# NOINLINE sem_Expression_Literal #-}
sem_Expression_Literal :: T_Range  -> T_Literal  -> T_Expression 
sem_Expression_Literal arg_range_ arg_literal_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalItext) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _text = rule75 _literalItext
         _lhsOtext :: Doc
         _lhsOtext = rule76 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule75 #-}
   rule75 = \ ((_literalItext) :: Doc) ->
                                      _literalItext
   {-# INLINE rule76 #-}
   rule76 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Variable #-}
sem_Expression_Variable :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Variable arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule77 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule78 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule77 #-}
   rule77 = \ ((_nameItext) :: Doc) ->
                                      _nameItext
   {-# INLINE rule78 #-}
   rule78 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Constructor #-}
sem_Expression_Constructor :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Constructor arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule79 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule80 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule79 #-}
   rule79 = \ ((_nameItext) :: Doc) ->
                                      _nameItext
   {-# INLINE rule80 #-}
   rule80 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Parenthesized #-}
sem_Expression_Parenthesized :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Parenthesized arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule81 _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule82 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule81 #-}
   rule81 = \ ((_expressionItext) :: Doc) ->
                                      parens _expressionItext
   {-# INLINE rule82 #-}
   rule82 = \ _text ->
     _text
{-# NOINLINE sem_Expression_NormalApplication #-}
sem_Expression_NormalApplication :: T_Range  -> T_Expression  -> T_Expressions  -> T_Expression 
sem_Expression_NormalApplication arg_range_ arg_function_ arg_arguments_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_function_))
         _argumentsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_arguments_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _functionItext) = inv_Expression_s41 _functionX41 (T_Expression_vIn40 )
         (T_Expressions_vOut43 _argumentsItext) = inv_Expressions_s44 _argumentsX44 (T_Expressions_vIn43 )
         _text = rule83 _argumentsItext _functionItext
         _lhsOtext :: Doc
         _lhsOtext = rule84 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule83 #-}
   rule83 = \ ((_argumentsItext) ::  [       Doc ] ) ((_functionItext) :: Doc) ->
                                      foldl (<+>) _functionItext _argumentsItext
   {-# INLINE rule84 #-}
   rule84 = \ _text ->
     _text
{-# NOINLINE sem_Expression_InfixApplication #-}
sem_Expression_InfixApplication :: T_Range  -> T_MaybeExpression  -> T_Expression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_InfixApplication arg_range_ arg_leftExpression_ arg_operator_ arg_rightExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_leftExpression_))
         _operatorX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_operator_))
         _rightExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_rightExpression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeExpression_vOut94 _leftExpressionItext) = inv_MaybeExpression_s95 _leftExpressionX95 (T_MaybeExpression_vIn94 )
         (T_Expression_vOut40 _operatorItext) = inv_Expression_s41 _operatorX41 (T_Expression_vIn40 )
         (T_MaybeExpression_vOut94 _rightExpressionItext) = inv_MaybeExpression_s95 _rightExpressionX95 (T_MaybeExpression_vIn94 )
         _text = rule85 _leftExpressionItext _operatorItext _rightExpressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule86 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule85 #-}
   rule85 = \ ((_leftExpressionItext) ::         Maybe Doc  ) ((_operatorItext) :: Doc) ((_rightExpressionItext) ::         Maybe Doc  ) ->
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
   {-# INLINE rule86 #-}
   rule86 = \ _text ->
     _text
{-# NOINLINE sem_Expression_If #-}
sem_Expression_If :: T_Range  -> T_Expression  -> T_Expression  -> T_Expression  -> T_Expression 
sem_Expression_If arg_range_ arg_guardExpression_ arg_thenExpression_ arg_elseExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guardExpression_))
         _thenExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_thenExpression_))
         _elseExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_elseExpression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardExpressionItext) = inv_Expression_s41 _guardExpressionX41 (T_Expression_vIn40 )
         (T_Expression_vOut40 _thenExpressionItext) = inv_Expression_s41 _thenExpressionX41 (T_Expression_vIn40 )
         (T_Expression_vOut40 _elseExpressionItext) = inv_Expression_s41 _elseExpressionX41 (T_Expression_vIn40 )
         _text = rule87 _elseExpressionItext _guardExpressionItext _thenExpressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule88 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule87 #-}
   rule87 = \ ((_elseExpressionItext) :: Doc) ((_guardExpressionItext) :: Doc) ((_thenExpressionItext) :: Doc) ->
                                       text "if" <+> _guardExpressionItext <$>
                                          indent 4 (text "then" <+> _thenExpressionItext <$>
                                                    text "else" <+> _elseExpressionItext)
   {-# INLINE rule88 #-}
   rule88 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Lambda #-}
sem_Expression_Lambda :: T_Range  -> T_Patterns  -> T_Expression  -> T_Expression 
sem_Expression_Lambda arg_range_ arg_patterns_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule89 _expressionItext _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule90 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule89 #-}
   rule89 = \ ((_expressionItext) :: Doc) ((_patternsItext) ::  [       Doc ] ) ->
                                      text "\\" <+> foldl1 (<+>) _patternsItext <+> text "->" <+> _expressionItext
   {-# INLINE rule90 #-}
   rule90 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Case #-}
sem_Expression_Case :: T_Range  -> T_Expression  -> T_Alternatives  -> T_Expression 
sem_Expression_Case arg_range_ arg_expression_ arg_alternatives_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _alternativesX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_alternatives_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         (T_Alternatives_vOut4 _alternativesItext) = inv_Alternatives_s5 _alternativesX5 (T_Alternatives_vIn4 )
         _text = rule91 _alternativesItext _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule92 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule91 #-}
   rule91 = \ ((_alternativesItext) ::  [       Doc ] ) ((_expressionItext) :: Doc) ->
                                       (text "case" <+> _expressionItext <+> text "of" <$>
                                                      (indent 4 $ vcat _alternativesItext) <$> empty
                                                  )
   {-# INLINE rule92 #-}
   rule92 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Let #-}
sem_Expression_Let :: T_Range  -> T_Declarations  -> T_Expression  -> T_Expression 
sem_Expression_Let arg_range_ arg_declarations_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsItext) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule93 _declarationsItext _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule94 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule93 #-}
   rule93 = \ ((_declarationsItext) ::  [       Doc ] ) ((_expressionItext) :: Doc) ->
                                       (text "let"<$>
                                                      (indent 4 $ vcat _declarationsItext) <+>
                                                   text "in" <$>
                                                      (indent 4 $ _expressionItext)
                                                  ) <$> empty
   {-# INLINE rule94 #-}
   rule94 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Do #-}
sem_Expression_Do :: T_Range  -> T_Statements  -> T_Expression 
sem_Expression_Do arg_range_ arg_statements_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _statementsX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_statements_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Statements_vOut157 _statementsItext) = inv_Statements_s158 _statementsX158 (T_Statements_vIn157 )
         _text = rule95 _statementsItext
         _lhsOtext :: Doc
         _lhsOtext = rule96 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule95 #-}
   rule95 = \ ((_statementsItext) ::  [       Doc ] ) ->
                                      text "do" <$> (indent 4 $ vcat _statementsItext) <$> empty
   {-# INLINE rule96 #-}
   rule96 = \ _text ->
     _text
{-# NOINLINE sem_Expression_List #-}
sem_Expression_List :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_List arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsItext) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 )
         _text = rule97 _expressionsItext
         _lhsOtext :: Doc
         _lhsOtext = rule98 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule97 #-}
   rule97 = \ ((_expressionsItext) ::  [       Doc ] ) ->
                                      PPrint.list _expressionsItext
   {-# INLINE rule98 #-}
   rule98 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Tuple #-}
sem_Expression_Tuple :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_Tuple arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsItext) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 )
         _text = rule99 _expressionsItext
         _lhsOtext :: Doc
         _lhsOtext = rule100 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule99 #-}
   rule99 = \ ((_expressionsItext) ::  [       Doc ] ) ->
                                      tupled _expressionsItext
   {-# INLINE rule100 #-}
   rule100 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Comprehension #-}
sem_Expression_Comprehension :: T_Range  -> T_Expression  -> T_Qualifiers  -> T_Expression 
sem_Expression_Comprehension arg_range_ arg_expression_ arg_qualifiers_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _qualifiersX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_qualifiers_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         (T_Qualifiers_vOut130 _qualifiersItext) = inv_Qualifiers_s131 _qualifiersX131 (T_Qualifiers_vIn130 )
         _text = rule101 _expressionItext _qualifiersItext
         _lhsOtext :: Doc
         _lhsOtext = rule102 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule101 #-}
   rule101 = \ ((_expressionItext) :: Doc) ((_qualifiersItext) ::  [       Doc ] ) ->
                                      text "[" <+> _expressionItext <+>
                                      text "|" <+> commas _qualifiersItext <+> text "]"
   {-# INLINE rule102 #-}
   rule102 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Typed #-}
sem_Expression_Typed :: T_Range  -> T_Expression  -> T_Type  -> T_Expression 
sem_Expression_Typed arg_range_ arg_expression_ arg_type_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule103 _expressionItext _typeItext
         _lhsOtext :: Doc
         _lhsOtext = rule104 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule103 #-}
   rule103 = \ ((_expressionItext) :: Doc) ((_typeItext) :: Doc) ->
                                      _expressionItext <+> text "::" <+> _typeItext
   {-# INLINE rule104 #-}
   rule104 = \ _text ->
     _text
{-# NOINLINE sem_Expression_RecordConstruction #-}
sem_Expression_RecordConstruction :: T_Range  -> T_Name  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordConstruction arg_range_ arg_name_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsItext) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 )
         _text = rule105  ()
         _lhsOtext :: Doc
         _lhsOtext = rule106 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule105 #-}
   rule105 = \  (_ :: ()) ->
                                      intErr "Expression" "record construction"
   {-# INLINE rule106 #-}
   rule106 = \ _text ->
     _text
{-# NOINLINE sem_Expression_RecordUpdate #-}
sem_Expression_RecordUpdate :: T_Range  -> T_Expression  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordUpdate arg_range_ arg_expression_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsItext) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 )
         _text = rule107  ()
         _lhsOtext :: Doc
         _lhsOtext = rule108 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule107 #-}
   rule107 = \  (_ :: ()) ->
                                      intErr "Expression" "record update"
   {-# INLINE rule108 #-}
   rule108 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Enum #-}
sem_Expression_Enum :: T_Range  -> T_Expression  -> T_MaybeExpression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_Enum arg_range_ arg_from_ arg_then_ arg_to_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fromX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_from_))
         _thenX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_then_))
         _toX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_to_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _fromItext) = inv_Expression_s41 _fromX41 (T_Expression_vIn40 )
         (T_MaybeExpression_vOut94 _thenItext) = inv_MaybeExpression_s95 _thenX95 (T_MaybeExpression_vIn94 )
         (T_MaybeExpression_vOut94 _toItext) = inv_MaybeExpression_s95 _toX95 (T_MaybeExpression_vIn94 )
         _text = rule109 _fromItext _thenItext _toItext
         _lhsOtext :: Doc
         _lhsOtext = rule110 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule109 #-}
   rule109 = \ ((_fromItext) :: Doc) ((_thenItext) ::         Maybe Doc  ) ((_toItext) ::         Maybe Doc  ) ->
                  text "[" <>
                  _fromItext <>
                  maybe empty (text "," <+>)  _thenItext <+>
                  text ".." <+>
                  opt _toItext <>
                  text "]"
   {-# INLINE rule110 #-}
   rule110 = \ _text ->
     _text
{-# NOINLINE sem_Expression_Negate #-}
sem_Expression_Negate :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Negate arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule111 _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule112 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule111 #-}
   rule111 = \ ((_expressionItext) :: Doc) ->
                                      text "-"  <> _expressionItext
   {-# INLINE rule112 #-}
   rule112 = \ _text ->
     _text
{-# NOINLINE sem_Expression_NegateFloat #-}
sem_Expression_NegateFloat :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_NegateFloat arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule113 _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule114 _text
         __result_ = T_Expression_vOut40 _lhsOtext
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule113 #-}
   rule113 = \ ((_expressionItext) :: Doc) ->
                                      text "-." <> _expressionItext
   {-# INLINE rule114 #-}
   rule114 = \ _text ->
     _text

-- Expressions -------------------------------------------------
-- wrapper
data Inh_Expressions  = Inh_Expressions {  }
data Syn_Expressions  = Syn_Expressions { text_Syn_Expressions :: ( [       Doc ] ) }
{-# INLINABLE wrap_Expressions #-}
wrap_Expressions :: T_Expressions  -> Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg43 = T_Expressions_vIn43 
        (T_Expressions_vOut43 _lhsOtext) <- return (inv_Expressions_s44 sem arg43)
        return (Syn_Expressions _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Expressions #-}
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list)

-- semantic domain
newtype T_Expressions  = T_Expressions {
                                       attach_T_Expressions :: Identity (T_Expressions_s44 )
                                       }
newtype T_Expressions_s44  = C_Expressions_s44 {
                                               inv_Expressions_s44 :: (T_Expressions_v43 )
                                               }
data T_Expressions_s45  = C_Expressions_s45
type T_Expressions_v43  = (T_Expressions_vIn43 ) -> (T_Expressions_vOut43 )
data T_Expressions_vIn43  = T_Expressions_vIn43 
data T_Expressions_vOut43  = T_Expressions_vOut43 ( [       Doc ] )
{-# NOINLINE sem_Expressions_Cons #-}
sem_Expressions_Cons :: T_Expression  -> T_Expressions  -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 ) -> ( let
         _hdX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_hd_))
         _tlX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_tl_))
         (T_Expression_vOut40 _hdItext) = inv_Expression_s41 _hdX41 (T_Expression_vIn40 )
         (T_Expressions_vOut43 _tlItext) = inv_Expressions_s44 _tlX44 (T_Expressions_vIn43 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule115 _hdItext _tlItext
         __result_ = T_Expressions_vOut43 _lhsOtext
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule115 #-}
   rule115 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Expressions_Nil #-}
sem_Expressions_Nil ::  T_Expressions 
sem_Expressions_Nil  = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule116  ()
         __result_ = T_Expressions_vOut43 _lhsOtext
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule116 #-}
   rule116 = \  (_ :: ()) ->
     []

-- FieldDeclaration --------------------------------------------
-- wrapper
data Inh_FieldDeclaration  = Inh_FieldDeclaration {  }
data Syn_FieldDeclaration  = Syn_FieldDeclaration { text_Syn_FieldDeclaration :: (Doc) }
{-# INLINABLE wrap_FieldDeclaration #-}
wrap_FieldDeclaration :: T_FieldDeclaration  -> Inh_FieldDeclaration  -> (Syn_FieldDeclaration )
wrap_FieldDeclaration (T_FieldDeclaration act) (Inh_FieldDeclaration ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg46 = T_FieldDeclaration_vIn46 
        (T_FieldDeclaration_vOut46 _lhsOtext) <- return (inv_FieldDeclaration_s47 sem arg46)
        return (Syn_FieldDeclaration _lhsOtext)
   )

-- cata
{-# INLINE sem_FieldDeclaration #-}
sem_FieldDeclaration :: FieldDeclaration  -> T_FieldDeclaration 
sem_FieldDeclaration ( FieldDeclaration_FieldDeclaration range_ names_ type_ ) = sem_FieldDeclaration_FieldDeclaration ( sem_Range range_ ) ( sem_Names names_ ) ( sem_AnnotatedType type_ )

-- semantic domain
newtype T_FieldDeclaration  = T_FieldDeclaration {
                                                 attach_T_FieldDeclaration :: Identity (T_FieldDeclaration_s47 )
                                                 }
newtype T_FieldDeclaration_s47  = C_FieldDeclaration_s47 {
                                                         inv_FieldDeclaration_s47 :: (T_FieldDeclaration_v46 )
                                                         }
data T_FieldDeclaration_s48  = C_FieldDeclaration_s48
type T_FieldDeclaration_v46  = (T_FieldDeclaration_vIn46 ) -> (T_FieldDeclaration_vOut46 )
data T_FieldDeclaration_vIn46  = T_FieldDeclaration_vIn46 
data T_FieldDeclaration_vOut46  = T_FieldDeclaration_vOut46 (Doc)
{-# NOINLINE sem_FieldDeclaration_FieldDeclaration #-}
sem_FieldDeclaration_FieldDeclaration :: T_Range  -> T_Names  -> T_AnnotatedType  -> T_FieldDeclaration 
sem_FieldDeclaration_FieldDeclaration arg_range_ arg_names_ arg_type_ = T_FieldDeclaration (return st47) where
   {-# NOINLINE st47 #-}
   st47 = let
      v46 :: T_FieldDeclaration_v46 
      v46 = \ (T_FieldDeclaration_vIn46 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesIisIdentifier _namesIisOperator _namesIisSpecial _namesItext) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_AnnotatedType_vOut7 _typeItext) = inv_AnnotatedType_s8 _typeX8 (T_AnnotatedType_vIn7 )
         _text = rule117  ()
         _lhsOtext :: Doc
         _lhsOtext = rule118 _text
         __result_ = T_FieldDeclaration_vOut46 _lhsOtext
         in __result_ )
     in C_FieldDeclaration_s47 v46
   {-# INLINE rule117 #-}
   rule117 = \  (_ :: ()) ->
                                    text "{- !!! field declaration -}"
   {-# INLINE rule118 #-}
   rule118 = \ _text ->
     _text

-- FieldDeclarations -------------------------------------------
-- wrapper
data Inh_FieldDeclarations  = Inh_FieldDeclarations {  }
data Syn_FieldDeclarations  = Syn_FieldDeclarations { text_Syn_FieldDeclarations :: ( [       Doc ] ) }
{-# INLINABLE wrap_FieldDeclarations #-}
wrap_FieldDeclarations :: T_FieldDeclarations  -> Inh_FieldDeclarations  -> (Syn_FieldDeclarations )
wrap_FieldDeclarations (T_FieldDeclarations act) (Inh_FieldDeclarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg49 = T_FieldDeclarations_vIn49 
        (T_FieldDeclarations_vOut49 _lhsOtext) <- return (inv_FieldDeclarations_s50 sem arg49)
        return (Syn_FieldDeclarations _lhsOtext)
   )

-- cata
{-# NOINLINE sem_FieldDeclarations #-}
sem_FieldDeclarations :: FieldDeclarations  -> T_FieldDeclarations 
sem_FieldDeclarations list = Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list)

-- semantic domain
newtype T_FieldDeclarations  = T_FieldDeclarations {
                                                   attach_T_FieldDeclarations :: Identity (T_FieldDeclarations_s50 )
                                                   }
newtype T_FieldDeclarations_s50  = C_FieldDeclarations_s50 {
                                                           inv_FieldDeclarations_s50 :: (T_FieldDeclarations_v49 )
                                                           }
data T_FieldDeclarations_s51  = C_FieldDeclarations_s51
type T_FieldDeclarations_v49  = (T_FieldDeclarations_vIn49 ) -> (T_FieldDeclarations_vOut49 )
data T_FieldDeclarations_vIn49  = T_FieldDeclarations_vIn49 
data T_FieldDeclarations_vOut49  = T_FieldDeclarations_vOut49 ( [       Doc ] )
{-# NOINLINE sem_FieldDeclarations_Cons #-}
sem_FieldDeclarations_Cons :: T_FieldDeclaration  -> T_FieldDeclarations  -> T_FieldDeclarations 
sem_FieldDeclarations_Cons arg_hd_ arg_tl_ = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 ) -> ( let
         _hdX47 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclaration (arg_hd_))
         _tlX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_tl_))
         (T_FieldDeclaration_vOut46 _hdItext) = inv_FieldDeclaration_s47 _hdX47 (T_FieldDeclaration_vIn46 )
         (T_FieldDeclarations_vOut49 _tlItext) = inv_FieldDeclarations_s50 _tlX50 (T_FieldDeclarations_vIn49 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule119 _hdItext _tlItext
         __result_ = T_FieldDeclarations_vOut49 _lhsOtext
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule119 #-}
   rule119 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_FieldDeclarations_Nil #-}
sem_FieldDeclarations_Nil ::  T_FieldDeclarations 
sem_FieldDeclarations_Nil  = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule120  ()
         __result_ = T_FieldDeclarations_vOut49 _lhsOtext
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule120 #-}
   rule120 = \  (_ :: ()) ->
     []

-- Fixity ------------------------------------------------------
-- wrapper
data Inh_Fixity  = Inh_Fixity {  }
data Syn_Fixity  = Syn_Fixity { text_Syn_Fixity :: (Doc) }
{-# INLINABLE wrap_Fixity #-}
wrap_Fixity :: T_Fixity  -> Inh_Fixity  -> (Syn_Fixity )
wrap_Fixity (T_Fixity act) (Inh_Fixity ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg52 = T_Fixity_vIn52 
        (T_Fixity_vOut52 _lhsOtext) <- return (inv_Fixity_s53 sem arg52)
        return (Syn_Fixity _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Fixity #-}
sem_Fixity :: Fixity  -> T_Fixity 
sem_Fixity ( Fixity_Infixl range_ ) = sem_Fixity_Infixl ( sem_Range range_ )
sem_Fixity ( Fixity_Infixr range_ ) = sem_Fixity_Infixr ( sem_Range range_ )
sem_Fixity ( Fixity_Infix range_ ) = sem_Fixity_Infix ( sem_Range range_ )

-- semantic domain
newtype T_Fixity  = T_Fixity {
                             attach_T_Fixity :: Identity (T_Fixity_s53 )
                             }
newtype T_Fixity_s53  = C_Fixity_s53 {
                                     inv_Fixity_s53 :: (T_Fixity_v52 )
                                     }
data T_Fixity_s54  = C_Fixity_s54
type T_Fixity_v52  = (T_Fixity_vIn52 ) -> (T_Fixity_vOut52 )
data T_Fixity_vIn52  = T_Fixity_vIn52 
data T_Fixity_vOut52  = T_Fixity_vOut52 (Doc)
{-# NOINLINE sem_Fixity_Infixl #-}
sem_Fixity_Infixl :: T_Range  -> T_Fixity 
sem_Fixity_Infixl arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule121  ()
         _lhsOtext :: Doc
         _lhsOtext = rule122 _text
         __result_ = T_Fixity_vOut52 _lhsOtext
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule121 #-}
   rule121 = \  (_ :: ()) ->
                                          text "infixl"
   {-# INLINE rule122 #-}
   rule122 = \ _text ->
     _text
{-# NOINLINE sem_Fixity_Infixr #-}
sem_Fixity_Infixr :: T_Range  -> T_Fixity 
sem_Fixity_Infixr arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule123  ()
         _lhsOtext :: Doc
         _lhsOtext = rule124 _text
         __result_ = T_Fixity_vOut52 _lhsOtext
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule123 #-}
   rule123 = \  (_ :: ()) ->
                                          text "infixr"
   {-# INLINE rule124 #-}
   rule124 = \ _text ->
     _text
{-# NOINLINE sem_Fixity_Infix #-}
sem_Fixity_Infix :: T_Range  -> T_Fixity 
sem_Fixity_Infix arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule125  ()
         _lhsOtext :: Doc
         _lhsOtext = rule126 _text
         __result_ = T_Fixity_vOut52 _lhsOtext
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule125 #-}
   rule125 = \  (_ :: ()) ->
                                          text "infix "
   {-# INLINE rule126 #-}
   rule126 = \ _text ->
     _text

-- FunctionBinding ---------------------------------------------
-- wrapper
data Inh_FunctionBinding  = Inh_FunctionBinding {  }
data Syn_FunctionBinding  = Syn_FunctionBinding { text_Syn_FunctionBinding :: (Doc) }
{-# INLINABLE wrap_FunctionBinding #-}
wrap_FunctionBinding :: T_FunctionBinding  -> Inh_FunctionBinding  -> (Syn_FunctionBinding )
wrap_FunctionBinding (T_FunctionBinding act) (Inh_FunctionBinding ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg55 = T_FunctionBinding_vIn55 
        (T_FunctionBinding_vOut55 _lhsOtext) <- return (inv_FunctionBinding_s56 sem arg55)
        return (Syn_FunctionBinding _lhsOtext)
   )

-- cata
{-# NOINLINE sem_FunctionBinding #-}
sem_FunctionBinding :: FunctionBinding  -> T_FunctionBinding 
sem_FunctionBinding ( FunctionBinding_Hole range_ id_ ) = sem_FunctionBinding_Hole ( sem_Range range_ ) id_
sem_FunctionBinding ( FunctionBinding_Feedback range_ feedback_ functionBinding_ ) = sem_FunctionBinding_Feedback ( sem_Range range_ ) feedback_ ( sem_FunctionBinding functionBinding_ )
sem_FunctionBinding ( FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_ ) = sem_FunctionBinding_FunctionBinding ( sem_Range range_ ) ( sem_LeftHandSide lefthandside_ ) ( sem_RightHandSide righthandside_ )

-- semantic domain
newtype T_FunctionBinding  = T_FunctionBinding {
                                               attach_T_FunctionBinding :: Identity (T_FunctionBinding_s56 )
                                               }
newtype T_FunctionBinding_s56  = C_FunctionBinding_s56 {
                                                       inv_FunctionBinding_s56 :: (T_FunctionBinding_v55 )
                                                       }
data T_FunctionBinding_s57  = C_FunctionBinding_s57
type T_FunctionBinding_v55  = (T_FunctionBinding_vIn55 ) -> (T_FunctionBinding_vOut55 )
data T_FunctionBinding_vIn55  = T_FunctionBinding_vIn55 
data T_FunctionBinding_vOut55  = T_FunctionBinding_vOut55 (Doc)
{-# NOINLINE sem_FunctionBinding_Hole #-}
sem_FunctionBinding_Hole :: T_Range  -> (Integer) -> T_FunctionBinding 
sem_FunctionBinding_Hole arg_range_ _ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule127  ()
         _lhsOtext :: Doc
         _lhsOtext = rule128 _text
         __result_ = T_FunctionBinding_vOut55 _lhsOtext
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule127 #-}
   rule127 = \  (_ :: ()) ->
                                   empty
   {-# INLINE rule128 #-}
   rule128 = \ _text ->
     _text
{-# NOINLINE sem_FunctionBinding_Feedback #-}
sem_FunctionBinding_Feedback :: T_Range  -> (String) -> T_FunctionBinding  -> T_FunctionBinding 
sem_FunctionBinding_Feedback arg_range_ _ arg_functionBinding_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionBindingX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_functionBinding_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBinding_vOut55 _functionBindingItext) = inv_FunctionBinding_s56 _functionBindingX56 (T_FunctionBinding_vIn55 )
         _lhsOtext :: Doc
         _lhsOtext = rule129 _functionBindingItext
         __result_ = T_FunctionBinding_vOut55 _lhsOtext
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule129 #-}
   rule129 = \ ((_functionBindingItext) :: Doc) ->
     _functionBindingItext
{-# NOINLINE sem_FunctionBinding_FunctionBinding #-}
sem_FunctionBinding_FunctionBinding :: T_Range  -> T_LeftHandSide  -> T_RightHandSide  -> T_FunctionBinding 
sem_FunctionBinding_FunctionBinding arg_range_ arg_lefthandside_ arg_righthandside_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideItext) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 )
         (T_RightHandSide_vOut148 _righthandsideItext) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 )
         _text = rule130 _lefthandsideItext _righthandsideItext
         _lhsOtext :: Doc
         _lhsOtext = rule131 _text
         __result_ = T_FunctionBinding_vOut55 _lhsOtext
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule130 #-}
   rule130 = \ ((_lefthandsideItext) :: Doc) ((_righthandsideItext) ::  Doc        -> Doc  ) ->
                                   _lefthandsideItext <+> _righthandsideItext (text "=")
   {-# INLINE rule131 #-}
   rule131 = \ _text ->
     _text

-- FunctionBindings --------------------------------------------
-- wrapper
data Inh_FunctionBindings  = Inh_FunctionBindings {  }
data Syn_FunctionBindings  = Syn_FunctionBindings { text_Syn_FunctionBindings :: ( [       Doc ] ) }
{-# INLINABLE wrap_FunctionBindings #-}
wrap_FunctionBindings :: T_FunctionBindings  -> Inh_FunctionBindings  -> (Syn_FunctionBindings )
wrap_FunctionBindings (T_FunctionBindings act) (Inh_FunctionBindings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg58 = T_FunctionBindings_vIn58 
        (T_FunctionBindings_vOut58 _lhsOtext) <- return (inv_FunctionBindings_s59 sem arg58)
        return (Syn_FunctionBindings _lhsOtext)
   )

-- cata
{-# NOINLINE sem_FunctionBindings #-}
sem_FunctionBindings :: FunctionBindings  -> T_FunctionBindings 
sem_FunctionBindings list = Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list)

-- semantic domain
newtype T_FunctionBindings  = T_FunctionBindings {
                                                 attach_T_FunctionBindings :: Identity (T_FunctionBindings_s59 )
                                                 }
newtype T_FunctionBindings_s59  = C_FunctionBindings_s59 {
                                                         inv_FunctionBindings_s59 :: (T_FunctionBindings_v58 )
                                                         }
data T_FunctionBindings_s60  = C_FunctionBindings_s60
type T_FunctionBindings_v58  = (T_FunctionBindings_vIn58 ) -> (T_FunctionBindings_vOut58 )
data T_FunctionBindings_vIn58  = T_FunctionBindings_vIn58 
data T_FunctionBindings_vOut58  = T_FunctionBindings_vOut58 ( [       Doc ] )
{-# NOINLINE sem_FunctionBindings_Cons #-}
sem_FunctionBindings_Cons :: T_FunctionBinding  -> T_FunctionBindings  -> T_FunctionBindings 
sem_FunctionBindings_Cons arg_hd_ arg_tl_ = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 ) -> ( let
         _hdX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_hd_))
         _tlX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_tl_))
         (T_FunctionBinding_vOut55 _hdItext) = inv_FunctionBinding_s56 _hdX56 (T_FunctionBinding_vIn55 )
         (T_FunctionBindings_vOut58 _tlItext) = inv_FunctionBindings_s59 _tlX59 (T_FunctionBindings_vIn58 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule132 _hdItext _tlItext
         __result_ = T_FunctionBindings_vOut58 _lhsOtext
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule132 #-}
   rule132 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_FunctionBindings_Nil #-}
sem_FunctionBindings_Nil ::  T_FunctionBindings 
sem_FunctionBindings_Nil  = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule133  ()
         __result_ = T_FunctionBindings_vOut58 _lhsOtext
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule133 #-}
   rule133 = \  (_ :: ()) ->
     []

-- GuardedExpression -------------------------------------------
-- wrapper
data Inh_GuardedExpression  = Inh_GuardedExpression {  }
data Syn_GuardedExpression  = Syn_GuardedExpression { text_Syn_GuardedExpression :: ( Doc        -> Doc  ) }
{-# INLINABLE wrap_GuardedExpression #-}
wrap_GuardedExpression :: T_GuardedExpression  -> Inh_GuardedExpression  -> (Syn_GuardedExpression )
wrap_GuardedExpression (T_GuardedExpression act) (Inh_GuardedExpression ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg61 = T_GuardedExpression_vIn61 
        (T_GuardedExpression_vOut61 _lhsOtext) <- return (inv_GuardedExpression_s62 sem arg61)
        return (Syn_GuardedExpression _lhsOtext)
   )

-- cata
{-# NOINLINE sem_GuardedExpression #-}
sem_GuardedExpression :: GuardedExpression  -> T_GuardedExpression 
sem_GuardedExpression ( GuardedExpression_GuardedExpression range_ guard_ expression_ ) = sem_GuardedExpression_GuardedExpression ( sem_Range range_ ) ( sem_Expression guard_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_GuardedExpression  = T_GuardedExpression {
                                                   attach_T_GuardedExpression :: Identity (T_GuardedExpression_s62 )
                                                   }
newtype T_GuardedExpression_s62  = C_GuardedExpression_s62 {
                                                           inv_GuardedExpression_s62 :: (T_GuardedExpression_v61 )
                                                           }
data T_GuardedExpression_s63  = C_GuardedExpression_s63
type T_GuardedExpression_v61  = (T_GuardedExpression_vIn61 ) -> (T_GuardedExpression_vOut61 )
data T_GuardedExpression_vIn61  = T_GuardedExpression_vIn61 
data T_GuardedExpression_vOut61  = T_GuardedExpression_vOut61 ( Doc        -> Doc  )
{-# NOINLINE sem_GuardedExpression_GuardedExpression #-}
sem_GuardedExpression_GuardedExpression :: T_Range  -> T_Expression  -> T_Expression  -> T_GuardedExpression 
sem_GuardedExpression_GuardedExpression arg_range_ arg_guard_ arg_expression_ = T_GuardedExpression (return st62) where
   {-# NOINLINE st62 #-}
   st62 = let
      v61 :: T_GuardedExpression_v61 
      v61 = \ (T_GuardedExpression_vIn61 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardItext) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule134 _expressionItext _guardItext
         _lhsOtext ::  Doc        -> Doc  
         _lhsOtext = rule135 _text
         __result_ = T_GuardedExpression_vOut61 _lhsOtext
         in __result_ )
     in C_GuardedExpression_s62 v61
   {-# INLINE rule134 #-}
   rule134 = \ ((_expressionItext) :: Doc) ((_guardItext) :: Doc) ->
                                     \assign -> text "|" <+> _guardItext <+> assign <+> _expressionItext
   {-# INLINE rule135 #-}
   rule135 = \ _text ->
     _text

-- GuardedExpressions ------------------------------------------
-- wrapper
data Inh_GuardedExpressions  = Inh_GuardedExpressions {  }
data Syn_GuardedExpressions  = Syn_GuardedExpressions { text_Syn_GuardedExpressions :: ( [        Doc -> Doc  ] ) }
{-# INLINABLE wrap_GuardedExpressions #-}
wrap_GuardedExpressions :: T_GuardedExpressions  -> Inh_GuardedExpressions  -> (Syn_GuardedExpressions )
wrap_GuardedExpressions (T_GuardedExpressions act) (Inh_GuardedExpressions ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg64 = T_GuardedExpressions_vIn64 
        (T_GuardedExpressions_vOut64 _lhsOtext) <- return (inv_GuardedExpressions_s65 sem arg64)
        return (Syn_GuardedExpressions _lhsOtext)
   )

-- cata
{-# NOINLINE sem_GuardedExpressions #-}
sem_GuardedExpressions :: GuardedExpressions  -> T_GuardedExpressions 
sem_GuardedExpressions list = Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list)

-- semantic domain
newtype T_GuardedExpressions  = T_GuardedExpressions {
                                                     attach_T_GuardedExpressions :: Identity (T_GuardedExpressions_s65 )
                                                     }
newtype T_GuardedExpressions_s65  = C_GuardedExpressions_s65 {
                                                             inv_GuardedExpressions_s65 :: (T_GuardedExpressions_v64 )
                                                             }
data T_GuardedExpressions_s66  = C_GuardedExpressions_s66
type T_GuardedExpressions_v64  = (T_GuardedExpressions_vIn64 ) -> (T_GuardedExpressions_vOut64 )
data T_GuardedExpressions_vIn64  = T_GuardedExpressions_vIn64 
data T_GuardedExpressions_vOut64  = T_GuardedExpressions_vOut64 ( [        Doc -> Doc  ] )
{-# NOINLINE sem_GuardedExpressions_Cons #-}
sem_GuardedExpressions_Cons :: T_GuardedExpression  -> T_GuardedExpressions  -> T_GuardedExpressions 
sem_GuardedExpressions_Cons arg_hd_ arg_tl_ = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 ) -> ( let
         _hdX62 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpression (arg_hd_))
         _tlX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_tl_))
         (T_GuardedExpression_vOut61 _hdItext) = inv_GuardedExpression_s62 _hdX62 (T_GuardedExpression_vIn61 )
         (T_GuardedExpressions_vOut64 _tlItext) = inv_GuardedExpressions_s65 _tlX65 (T_GuardedExpressions_vIn64 )
         _lhsOtext ::  [        Doc -> Doc  ] 
         _lhsOtext = rule136 _hdItext _tlItext
         __result_ = T_GuardedExpressions_vOut64 _lhsOtext
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule136 #-}
   rule136 = \ ((_hdItext) ::  Doc        -> Doc  ) ((_tlItext) ::  [        Doc -> Doc  ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_GuardedExpressions_Nil #-}
sem_GuardedExpressions_Nil ::  T_GuardedExpressions 
sem_GuardedExpressions_Nil  = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 ) -> ( let
         _lhsOtext ::  [        Doc -> Doc  ] 
         _lhsOtext = rule137  ()
         __result_ = T_GuardedExpressions_vOut64 _lhsOtext
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule137 #-}
   rule137 = \  (_ :: ()) ->
     []

-- Import ------------------------------------------------------
-- wrapper
data Inh_Import  = Inh_Import {  }
data Syn_Import  = Syn_Import { text_Syn_Import :: (Doc) }
{-# INLINABLE wrap_Import #-}
wrap_Import :: T_Import  -> Inh_Import  -> (Syn_Import )
wrap_Import (T_Import act) (Inh_Import ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg67 = T_Import_vIn67 
        (T_Import_vOut67 _lhsOtext) <- return (inv_Import_s68 sem arg67)
        return (Syn_Import _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Import #-}
sem_Import :: Import  -> T_Import 
sem_Import ( Import_Variable range_ name_ ) = sem_Import_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Import ( Import_TypeOrClass range_ name_ names_ ) = sem_Import_TypeOrClass ( sem_Range range_ ) ( sem_Name name_ ) ( sem_MaybeNames names_ )
sem_Import ( Import_TypeOrClassComplete range_ name_ ) = sem_Import_TypeOrClassComplete ( sem_Range range_ ) ( sem_Name name_ )

-- semantic domain
newtype T_Import  = T_Import {
                             attach_T_Import :: Identity (T_Import_s68 )
                             }
newtype T_Import_s68  = C_Import_s68 {
                                     inv_Import_s68 :: (T_Import_v67 )
                                     }
data T_Import_s69  = C_Import_s69
type T_Import_v67  = (T_Import_vIn67 ) -> (T_Import_vOut67 )
data T_Import_vIn67  = T_Import_vIn67 
data T_Import_vOut67  = T_Import_vOut67 (Doc)
{-# NOINLINE sem_Import_Variable #-}
sem_Import_Variable :: T_Range  -> T_Name  -> T_Import 
sem_Import_Variable arg_range_ arg_name_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule138 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule139 _text
         __result_ = T_Import_vOut67 _lhsOtext
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule138 #-}
   rule138 = \ ((_nameItext) :: Doc) ->
                                           _nameItext
   {-# INLINE rule139 #-}
   rule139 = \ _text ->
     _text
{-# NOINLINE sem_Import_TypeOrClass #-}
sem_Import_TypeOrClass :: T_Range  -> T_Name  -> T_MaybeNames  -> T_Import 
sem_Import_TypeOrClass arg_range_ arg_name_ arg_names_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _namesX107 = Control.Monad.Identity.runIdentity (attach_T_MaybeNames (arg_names_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeNames_vOut106 _namesItext) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _text = rule140 _nameItext _namesItext
         _lhsOtext :: Doc
         _lhsOtext = rule141 _text
         __result_ = T_Import_vOut67 _lhsOtext
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule140 #-}
   rule140 = \ ((_nameItext) :: Doc) ((_namesItext) ::  Maybe [       Doc ] ) ->
                                           _nameItext <> maybe empty tupled1 _namesItext
   {-# INLINE rule141 #-}
   rule141 = \ _text ->
     _text
{-# NOINLINE sem_Import_TypeOrClassComplete #-}
sem_Import_TypeOrClassComplete :: T_Range  -> T_Name  -> T_Import 
sem_Import_TypeOrClassComplete arg_range_ arg_name_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule142 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule143 _text
         __result_ = T_Import_vOut67 _lhsOtext
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule142 #-}
   rule142 = \ ((_nameItext) :: Doc) ->
                                           _nameItext
   {-# INLINE rule143 #-}
   rule143 = \ _text ->
     _text

-- ImportDeclaration -------------------------------------------
-- wrapper
data Inh_ImportDeclaration  = Inh_ImportDeclaration {  }
data Syn_ImportDeclaration  = Syn_ImportDeclaration { text_Syn_ImportDeclaration :: (Doc) }
{-# INLINABLE wrap_ImportDeclaration #-}
wrap_ImportDeclaration :: T_ImportDeclaration  -> Inh_ImportDeclaration  -> (Syn_ImportDeclaration )
wrap_ImportDeclaration (T_ImportDeclaration act) (Inh_ImportDeclaration ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg70 = T_ImportDeclaration_vIn70 
        (T_ImportDeclaration_vOut70 _lhsOtext) <- return (inv_ImportDeclaration_s71 sem arg70)
        return (Syn_ImportDeclaration _lhsOtext)
   )

-- cata
{-# NOINLINE sem_ImportDeclaration #-}
sem_ImportDeclaration :: ImportDeclaration  -> T_ImportDeclaration 
sem_ImportDeclaration ( ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_ ) = sem_ImportDeclaration_Import ( sem_Range range_ ) qualified_ ( sem_Name name_ ) ( sem_MaybeName asname_ ) ( sem_MaybeImportSpecification importspecification_ )
sem_ImportDeclaration ( ImportDeclaration_Empty range_ ) = sem_ImportDeclaration_Empty ( sem_Range range_ )

-- semantic domain
newtype T_ImportDeclaration  = T_ImportDeclaration {
                                                   attach_T_ImportDeclaration :: Identity (T_ImportDeclaration_s71 )
                                                   }
newtype T_ImportDeclaration_s71  = C_ImportDeclaration_s71 {
                                                           inv_ImportDeclaration_s71 :: (T_ImportDeclaration_v70 )
                                                           }
data T_ImportDeclaration_s72  = C_ImportDeclaration_s72
type T_ImportDeclaration_v70  = (T_ImportDeclaration_vIn70 ) -> (T_ImportDeclaration_vOut70 )
data T_ImportDeclaration_vIn70  = T_ImportDeclaration_vIn70 
data T_ImportDeclaration_vOut70  = T_ImportDeclaration_vOut70 (Doc)
{-# NOINLINE sem_ImportDeclaration_Import #-}
sem_ImportDeclaration_Import :: T_Range  -> (Bool) -> T_Name  -> T_MaybeName  -> T_MaybeImportSpecification  -> T_ImportDeclaration 
sem_ImportDeclaration_Import arg_range_ arg_qualified_ arg_name_ arg_asname_ arg_importspecification_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _asnameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_asname_))
         _importspecificationX98 = Control.Monad.Identity.runIdentity (attach_T_MaybeImportSpecification (arg_importspecification_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeName_vOut103 _asnameItext) = inv_MaybeName_s104 _asnameX104 (T_MaybeName_vIn103 )
         (T_MaybeImportSpecification_vOut97 _importspecificationItext) = inv_MaybeImportSpecification_s98 _importspecificationX98 (T_MaybeImportSpecification_vIn97 )
         _text = rule144 _importspecificationItext _nameItext arg_qualified_
         _lhsOtext :: Doc
         _lhsOtext = rule145 _text
         __result_ = T_ImportDeclaration_vOut70 _lhsOtext
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule144 #-}
   rule144 = \ ((_importspecificationItext) ::         Maybe Doc  ) ((_nameItext) :: Doc) qualified_ ->
                               text "import" <+> (if qualified_ then (text "qualified" <+>) else id) _nameItext <+> maybe empty id _importspecificationItext
   {-# INLINE rule145 #-}
   rule145 = \ _text ->
     _text
{-# NOINLINE sem_ImportDeclaration_Empty #-}
sem_ImportDeclaration_Empty :: T_Range  -> T_ImportDeclaration 
sem_ImportDeclaration_Empty arg_range_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule146  ()
         _lhsOtext :: Doc
         _lhsOtext = rule147 _text
         __result_ = T_ImportDeclaration_vOut70 _lhsOtext
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule146 #-}
   rule146 = \  (_ :: ()) ->
                               empty
   {-# INLINE rule147 #-}
   rule147 = \ _text ->
     _text

-- ImportDeclarations ------------------------------------------
-- wrapper
data Inh_ImportDeclarations  = Inh_ImportDeclarations {  }
data Syn_ImportDeclarations  = Syn_ImportDeclarations { text_Syn_ImportDeclarations :: ( [       Doc ] ) }
{-# INLINABLE wrap_ImportDeclarations #-}
wrap_ImportDeclarations :: T_ImportDeclarations  -> Inh_ImportDeclarations  -> (Syn_ImportDeclarations )
wrap_ImportDeclarations (T_ImportDeclarations act) (Inh_ImportDeclarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg73 = T_ImportDeclarations_vIn73 
        (T_ImportDeclarations_vOut73 _lhsOtext) <- return (inv_ImportDeclarations_s74 sem arg73)
        return (Syn_ImportDeclarations _lhsOtext)
   )

-- cata
{-# NOINLINE sem_ImportDeclarations #-}
sem_ImportDeclarations :: ImportDeclarations  -> T_ImportDeclarations 
sem_ImportDeclarations list = Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list)

-- semantic domain
newtype T_ImportDeclarations  = T_ImportDeclarations {
                                                     attach_T_ImportDeclarations :: Identity (T_ImportDeclarations_s74 )
                                                     }
newtype T_ImportDeclarations_s74  = C_ImportDeclarations_s74 {
                                                             inv_ImportDeclarations_s74 :: (T_ImportDeclarations_v73 )
                                                             }
data T_ImportDeclarations_s75  = C_ImportDeclarations_s75
type T_ImportDeclarations_v73  = (T_ImportDeclarations_vIn73 ) -> (T_ImportDeclarations_vOut73 )
data T_ImportDeclarations_vIn73  = T_ImportDeclarations_vIn73 
data T_ImportDeclarations_vOut73  = T_ImportDeclarations_vOut73 ( [       Doc ] )
{-# NOINLINE sem_ImportDeclarations_Cons #-}
sem_ImportDeclarations_Cons :: T_ImportDeclaration  -> T_ImportDeclarations  -> T_ImportDeclarations 
sem_ImportDeclarations_Cons arg_hd_ arg_tl_ = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 ) -> ( let
         _hdX71 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclaration (arg_hd_))
         _tlX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_tl_))
         (T_ImportDeclaration_vOut70 _hdItext) = inv_ImportDeclaration_s71 _hdX71 (T_ImportDeclaration_vIn70 )
         (T_ImportDeclarations_vOut73 _tlItext) = inv_ImportDeclarations_s74 _tlX74 (T_ImportDeclarations_vIn73 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule148 _hdItext _tlItext
         __result_ = T_ImportDeclarations_vOut73 _lhsOtext
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule148 #-}
   rule148 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_ImportDeclarations_Nil #-}
sem_ImportDeclarations_Nil ::  T_ImportDeclarations 
sem_ImportDeclarations_Nil  = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule149  ()
         __result_ = T_ImportDeclarations_vOut73 _lhsOtext
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule149 #-}
   rule149 = \  (_ :: ()) ->
     []

-- ImportSpecification -----------------------------------------
-- wrapper
data Inh_ImportSpecification  = Inh_ImportSpecification {  }
data Syn_ImportSpecification  = Syn_ImportSpecification { text_Syn_ImportSpecification :: (Doc) }
{-# INLINABLE wrap_ImportSpecification #-}
wrap_ImportSpecification :: T_ImportSpecification  -> Inh_ImportSpecification  -> (Syn_ImportSpecification )
wrap_ImportSpecification (T_ImportSpecification act) (Inh_ImportSpecification ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg76 = T_ImportSpecification_vIn76 
        (T_ImportSpecification_vOut76 _lhsOtext) <- return (inv_ImportSpecification_s77 sem arg76)
        return (Syn_ImportSpecification _lhsOtext)
   )

-- cata
{-# INLINE sem_ImportSpecification #-}
sem_ImportSpecification :: ImportSpecification  -> T_ImportSpecification 
sem_ImportSpecification ( ImportSpecification_Import range_ hiding_ imports_ ) = sem_ImportSpecification_Import ( sem_Range range_ ) hiding_ ( sem_Imports imports_ )

-- semantic domain
newtype T_ImportSpecification  = T_ImportSpecification {
                                                       attach_T_ImportSpecification :: Identity (T_ImportSpecification_s77 )
                                                       }
newtype T_ImportSpecification_s77  = C_ImportSpecification_s77 {
                                                               inv_ImportSpecification_s77 :: (T_ImportSpecification_v76 )
                                                               }
data T_ImportSpecification_s78  = C_ImportSpecification_s78
type T_ImportSpecification_v76  = (T_ImportSpecification_vIn76 ) -> (T_ImportSpecification_vOut76 )
data T_ImportSpecification_vIn76  = T_ImportSpecification_vIn76 
data T_ImportSpecification_vOut76  = T_ImportSpecification_vOut76 (Doc)
{-# NOINLINE sem_ImportSpecification_Import #-}
sem_ImportSpecification_Import :: T_Range  -> (Bool) -> T_Imports  -> T_ImportSpecification 
sem_ImportSpecification_Import arg_range_ arg_hiding_ arg_imports_ = T_ImportSpecification (return st77) where
   {-# NOINLINE st77 #-}
   st77 = let
      v76 :: T_ImportSpecification_v76 
      v76 = \ (T_ImportSpecification_vIn76 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _importsX80 = Control.Monad.Identity.runIdentity (attach_T_Imports (arg_imports_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Imports_vOut79 _importsItext) = inv_Imports_s80 _importsX80 (T_Imports_vIn79 )
         _text = rule150 _importsItext arg_hiding_
         _lhsOtext :: Doc
         _lhsOtext = rule151 _text
         __result_ = T_ImportSpecification_vOut76 _lhsOtext
         in __result_ )
     in C_ImportSpecification_s77 v76
   {-# INLINE rule150 #-}
   rule150 = \ ((_importsItext) ::  [       Doc ] ) hiding_ ->
                             (if hiding_ then (text "hiding" <+>) else id)
                                                      (tupled _importsItext)
   {-# INLINE rule151 #-}
   rule151 = \ _text ->
     _text

-- Imports -----------------------------------------------------
-- wrapper
data Inh_Imports  = Inh_Imports {  }
data Syn_Imports  = Syn_Imports { text_Syn_Imports :: ( [       Doc ] ) }
{-# INLINABLE wrap_Imports #-}
wrap_Imports :: T_Imports  -> Inh_Imports  -> (Syn_Imports )
wrap_Imports (T_Imports act) (Inh_Imports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg79 = T_Imports_vIn79 
        (T_Imports_vOut79 _lhsOtext) <- return (inv_Imports_s80 sem arg79)
        return (Syn_Imports _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Imports #-}
sem_Imports :: Imports  -> T_Imports 
sem_Imports list = Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list)

-- semantic domain
newtype T_Imports  = T_Imports {
                               attach_T_Imports :: Identity (T_Imports_s80 )
                               }
newtype T_Imports_s80  = C_Imports_s80 {
                                       inv_Imports_s80 :: (T_Imports_v79 )
                                       }
data T_Imports_s81  = C_Imports_s81
type T_Imports_v79  = (T_Imports_vIn79 ) -> (T_Imports_vOut79 )
data T_Imports_vIn79  = T_Imports_vIn79 
data T_Imports_vOut79  = T_Imports_vOut79 ( [       Doc ] )
{-# NOINLINE sem_Imports_Cons #-}
sem_Imports_Cons :: T_Import  -> T_Imports  -> T_Imports 
sem_Imports_Cons arg_hd_ arg_tl_ = T_Imports (return st80) where
   {-# NOINLINE st80 #-}
   st80 = let
      v79 :: T_Imports_v79 
      v79 = \ (T_Imports_vIn79 ) -> ( let
         _hdX68 = Control.Monad.Identity.runIdentity (attach_T_Import (arg_hd_))
         _tlX80 = Control.Monad.Identity.runIdentity (attach_T_Imports (arg_tl_))
         (T_Import_vOut67 _hdItext) = inv_Import_s68 _hdX68 (T_Import_vIn67 )
         (T_Imports_vOut79 _tlItext) = inv_Imports_s80 _tlX80 (T_Imports_vIn79 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule152 _hdItext _tlItext
         __result_ = T_Imports_vOut79 _lhsOtext
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule152 #-}
   rule152 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Imports_Nil #-}
sem_Imports_Nil ::  T_Imports 
sem_Imports_Nil  = T_Imports (return st80) where
   {-# NOINLINE st80 #-}
   st80 = let
      v79 :: T_Imports_v79 
      v79 = \ (T_Imports_vIn79 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule153  ()
         __result_ = T_Imports_vOut79 _lhsOtext
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule153 #-}
   rule153 = \  (_ :: ()) ->
     []

-- LeftHandSide ------------------------------------------------
-- wrapper
data Inh_LeftHandSide  = Inh_LeftHandSide {  }
data Syn_LeftHandSide  = Syn_LeftHandSide { text_Syn_LeftHandSide :: (Doc) }
{-# INLINABLE wrap_LeftHandSide #-}
wrap_LeftHandSide :: T_LeftHandSide  -> Inh_LeftHandSide  -> (Syn_LeftHandSide )
wrap_LeftHandSide (T_LeftHandSide act) (Inh_LeftHandSide ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg82 = T_LeftHandSide_vIn82 
        (T_LeftHandSide_vOut82 _lhsOtext) <- return (inv_LeftHandSide_s83 sem arg82)
        return (Syn_LeftHandSide _lhsOtext)
   )

-- cata
{-# NOINLINE sem_LeftHandSide #-}
sem_LeftHandSide :: LeftHandSide  -> T_LeftHandSide 
sem_LeftHandSide ( LeftHandSide_Function range_ name_ patterns_ ) = sem_LeftHandSide_Function ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Patterns patterns_ )
sem_LeftHandSide ( LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_ ) = sem_LeftHandSide_Infix ( sem_Range range_ ) ( sem_Pattern leftPattern_ ) ( sem_Name operator_ ) ( sem_Pattern rightPattern_ )
sem_LeftHandSide ( LeftHandSide_Parenthesized range_ lefthandside_ patterns_ ) = sem_LeftHandSide_Parenthesized ( sem_Range range_ ) ( sem_LeftHandSide lefthandside_ ) ( sem_Patterns patterns_ )

-- semantic domain
newtype T_LeftHandSide  = T_LeftHandSide {
                                         attach_T_LeftHandSide :: Identity (T_LeftHandSide_s83 )
                                         }
newtype T_LeftHandSide_s83  = C_LeftHandSide_s83 {
                                                 inv_LeftHandSide_s83 :: (T_LeftHandSide_v82 )
                                                 }
data T_LeftHandSide_s84  = C_LeftHandSide_s84
type T_LeftHandSide_v82  = (T_LeftHandSide_vIn82 ) -> (T_LeftHandSide_vOut82 )
data T_LeftHandSide_vIn82  = T_LeftHandSide_vIn82 
data T_LeftHandSide_vOut82  = T_LeftHandSide_vOut82 (Doc)
{-# NOINLINE sem_LeftHandSide_Function #-}
sem_LeftHandSide_Function :: T_Range  -> T_Name  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Function arg_range_ arg_name_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _text = rule154 _nameIisOperator _nameItext _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule155 _text
         __result_ = T_LeftHandSide_vOut82 _lhsOtext
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule154 #-}
   rule154 = \ ((_nameIisOperator) :: Bool) ((_nameItext) :: Doc) ((_patternsItext) ::  [       Doc ] ) ->
                                    foldl (<+>) (parensIf _nameIisOperator _nameItext) _patternsItext
   {-# INLINE rule155 #-}
   rule155 = \ _text ->
     _text
{-# NOINLINE sem_LeftHandSide_Infix #-}
sem_LeftHandSide_Infix :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_LeftHandSide 
sem_LeftHandSide_Infix arg_range_ arg_leftPattern_ arg_operator_ arg_rightPattern_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _operatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_operator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternItext) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 )
         (T_Name_vOut112 _operatorIisIdentifier _operatorIisOperator _operatorIisSpecial _operatorItext) = inv_Name_s113 _operatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternItext) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 )
         _text = rule156 _leftPatternItext _operatorIisOperator _operatorItext _rightPatternItext
         _lhsOtext :: Doc
         _lhsOtext = rule157 _text
         __result_ = T_LeftHandSide_vOut82 _lhsOtext
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule156 #-}
   rule156 = \ ((_leftPatternItext) :: Doc) ((_operatorIisOperator) :: Bool) ((_operatorItext) :: Doc) ((_rightPatternItext) :: Doc) ->
                                    _leftPatternItext <+> backQuotesIf (not _operatorIisOperator) _operatorItext <+> _rightPatternItext
   {-# INLINE rule157 #-}
   rule157 = \ _text ->
     _text
{-# NOINLINE sem_LeftHandSide_Parenthesized #-}
sem_LeftHandSide_Parenthesized :: T_Range  -> T_LeftHandSide  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Parenthesized arg_range_ arg_lefthandside_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideItext) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _text = rule158 _lefthandsideItext _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule159 _text
         __result_ = T_LeftHandSide_vOut82 _lhsOtext
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule158 #-}
   rule158 = \ ((_lefthandsideItext) :: Doc) ((_patternsItext) ::  [       Doc ] ) ->
                                    foldl (<+>) (parens _lefthandsideItext) _patternsItext
   {-# INLINE rule159 #-}
   rule159 = \ _text ->
     _text

-- Literal -----------------------------------------------------
-- wrapper
data Inh_Literal  = Inh_Literal {  }
data Syn_Literal  = Syn_Literal { text_Syn_Literal :: (Doc) }
{-# INLINABLE wrap_Literal #-}
wrap_Literal :: T_Literal  -> Inh_Literal  -> (Syn_Literal )
wrap_Literal (T_Literal act) (Inh_Literal ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg85 = T_Literal_vIn85 
        (T_Literal_vOut85 _lhsOtext) <- return (inv_Literal_s86 sem arg85)
        return (Syn_Literal _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Literal #-}
sem_Literal :: Literal  -> T_Literal 
sem_Literal ( Literal_Int range_ value_ ) = sem_Literal_Int ( sem_Range range_ ) value_
sem_Literal ( Literal_Char range_ value_ ) = sem_Literal_Char ( sem_Range range_ ) value_
sem_Literal ( Literal_Float range_ value_ ) = sem_Literal_Float ( sem_Range range_ ) value_
sem_Literal ( Literal_String range_ value_ ) = sem_Literal_String ( sem_Range range_ ) value_

-- semantic domain
newtype T_Literal  = T_Literal {
                               attach_T_Literal :: Identity (T_Literal_s86 )
                               }
newtype T_Literal_s86  = C_Literal_s86 {
                                       inv_Literal_s86 :: (T_Literal_v85 )
                                       }
data T_Literal_s87  = C_Literal_s87
type T_Literal_v85  = (T_Literal_vIn85 ) -> (T_Literal_vOut85 )
data T_Literal_vIn85  = T_Literal_vIn85 
data T_Literal_vOut85  = T_Literal_vOut85 (Doc)
{-# NOINLINE sem_Literal_Int #-}
sem_Literal_Int :: T_Range  -> (String) -> T_Literal 
sem_Literal_Int arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule160 arg_value_
         _lhsOtext :: Doc
         _lhsOtext = rule161 _text
         __result_ = T_Literal_vOut85 _lhsOtext
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule160 #-}
   rule160 = \ value_ ->
                                         text value_
   {-# INLINE rule161 #-}
   rule161 = \ _text ->
     _text
{-# NOINLINE sem_Literal_Char #-}
sem_Literal_Char :: T_Range  -> (String) -> T_Literal 
sem_Literal_Char arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule162 arg_value_
         _lhsOtext :: Doc
         _lhsOtext = rule163 _text
         __result_ = T_Literal_vOut85 _lhsOtext
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule162 #-}
   rule162 = \ value_ ->
                                         text ("'" ++ value_ ++ "'")
   {-# INLINE rule163 #-}
   rule163 = \ _text ->
     _text
{-# NOINLINE sem_Literal_Float #-}
sem_Literal_Float :: T_Range  -> (String) -> T_Literal 
sem_Literal_Float arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule164 arg_value_
         _lhsOtext :: Doc
         _lhsOtext = rule165 _text
         __result_ = T_Literal_vOut85 _lhsOtext
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule164 #-}
   rule164 = \ value_ ->
                                         text value_
   {-# INLINE rule165 #-}
   rule165 = \ _text ->
     _text
{-# NOINLINE sem_Literal_String #-}
sem_Literal_String :: T_Range  -> (String) -> T_Literal 
sem_Literal_String arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule166 arg_value_
         _lhsOtext :: Doc
         _lhsOtext = rule167 _text
         __result_ = T_Literal_vOut85 _lhsOtext
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule166 #-}
   rule166 = \ value_ ->
                                         text ("\"" ++ value_ ++ "\"")
   {-# INLINE rule167 #-}
   rule167 = \ _text ->
     _text

-- MaybeDeclarations -------------------------------------------
-- wrapper
data Inh_MaybeDeclarations  = Inh_MaybeDeclarations {  }
data Syn_MaybeDeclarations  = Syn_MaybeDeclarations { text_Syn_MaybeDeclarations :: ( Maybe [       Doc ] ) }
{-# INLINABLE wrap_MaybeDeclarations #-}
wrap_MaybeDeclarations :: T_MaybeDeclarations  -> Inh_MaybeDeclarations  -> (Syn_MaybeDeclarations )
wrap_MaybeDeclarations (T_MaybeDeclarations act) (Inh_MaybeDeclarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg88 = T_MaybeDeclarations_vIn88 
        (T_MaybeDeclarations_vOut88 _lhsOtext) <- return (inv_MaybeDeclarations_s89 sem arg88)
        return (Syn_MaybeDeclarations _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeDeclarations #-}
sem_MaybeDeclarations :: MaybeDeclarations  -> T_MaybeDeclarations 
sem_MaybeDeclarations ( MaybeDeclarations_Nothing  ) = sem_MaybeDeclarations_Nothing 
sem_MaybeDeclarations ( MaybeDeclarations_Just declarations_ ) = sem_MaybeDeclarations_Just ( sem_Declarations declarations_ )

-- semantic domain
newtype T_MaybeDeclarations  = T_MaybeDeclarations {
                                                   attach_T_MaybeDeclarations :: Identity (T_MaybeDeclarations_s89 )
                                                   }
newtype T_MaybeDeclarations_s89  = C_MaybeDeclarations_s89 {
                                                           inv_MaybeDeclarations_s89 :: (T_MaybeDeclarations_v88 )
                                                           }
data T_MaybeDeclarations_s90  = C_MaybeDeclarations_s90
type T_MaybeDeclarations_v88  = (T_MaybeDeclarations_vIn88 ) -> (T_MaybeDeclarations_vOut88 )
data T_MaybeDeclarations_vIn88  = T_MaybeDeclarations_vIn88 
data T_MaybeDeclarations_vOut88  = T_MaybeDeclarations_vOut88 ( Maybe [       Doc ] )
{-# NOINLINE sem_MaybeDeclarations_Nothing #-}
sem_MaybeDeclarations_Nothing ::  T_MaybeDeclarations 
sem_MaybeDeclarations_Nothing  = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 ) -> ( let
         _text = rule168  ()
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule169 _text
         __result_ = T_MaybeDeclarations_vOut88 _lhsOtext
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule168 #-}
   rule168 = \  (_ :: ()) ->
                               Nothing
   {-# INLINE rule169 #-}
   rule169 = \ _text ->
     _text
{-# NOINLINE sem_MaybeDeclarations_Just #-}
sem_MaybeDeclarations_Just :: T_Declarations  -> T_MaybeDeclarations 
sem_MaybeDeclarations_Just arg_declarations_ = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 ) -> ( let
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Declarations_vOut31 _declarationsItext) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 )
         _text = rule170 _declarationsItext
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule171 _text
         __result_ = T_MaybeDeclarations_vOut88 _lhsOtext
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule170 #-}
   rule170 = \ ((_declarationsItext) ::  [       Doc ] ) ->
                        case filter ((/= "") . show) _declarationsItext of
                          [] -> Nothing
                          xs -> Just xs
   {-# INLINE rule171 #-}
   rule171 = \ _text ->
     _text

-- MaybeExports ------------------------------------------------
-- wrapper
data Inh_MaybeExports  = Inh_MaybeExports {  }
data Syn_MaybeExports  = Syn_MaybeExports { text_Syn_MaybeExports :: ( Maybe [       Doc ] ) }
{-# INLINABLE wrap_MaybeExports #-}
wrap_MaybeExports :: T_MaybeExports  -> Inh_MaybeExports  -> (Syn_MaybeExports )
wrap_MaybeExports (T_MaybeExports act) (Inh_MaybeExports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg91 = T_MaybeExports_vIn91 
        (T_MaybeExports_vOut91 _lhsOtext) <- return (inv_MaybeExports_s92 sem arg91)
        return (Syn_MaybeExports _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeExports #-}
sem_MaybeExports :: MaybeExports  -> T_MaybeExports 
sem_MaybeExports ( MaybeExports_Nothing  ) = sem_MaybeExports_Nothing 
sem_MaybeExports ( MaybeExports_Just exports_ ) = sem_MaybeExports_Just ( sem_Exports exports_ )

-- semantic domain
newtype T_MaybeExports  = T_MaybeExports {
                                         attach_T_MaybeExports :: Identity (T_MaybeExports_s92 )
                                         }
newtype T_MaybeExports_s92  = C_MaybeExports_s92 {
                                                 inv_MaybeExports_s92 :: (T_MaybeExports_v91 )
                                                 }
data T_MaybeExports_s93  = C_MaybeExports_s93
type T_MaybeExports_v91  = (T_MaybeExports_vIn91 ) -> (T_MaybeExports_vOut91 )
data T_MaybeExports_vIn91  = T_MaybeExports_vIn91 
data T_MaybeExports_vOut91  = T_MaybeExports_vOut91 ( Maybe [       Doc ] )
{-# NOINLINE sem_MaybeExports_Nothing #-}
sem_MaybeExports_Nothing ::  T_MaybeExports 
sem_MaybeExports_Nothing  = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 ) -> ( let
         _text = rule172  ()
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule173 _text
         __result_ = T_MaybeExports_vOut91 _lhsOtext
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule172 #-}
   rule172 = \  (_ :: ()) ->
                                    Nothing
   {-# INLINE rule173 #-}
   rule173 = \ _text ->
     _text
{-# NOINLINE sem_MaybeExports_Just #-}
sem_MaybeExports_Just :: T_Exports  -> T_MaybeExports 
sem_MaybeExports_Just arg_exports_ = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 ) -> ( let
         _exportsX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_exports_))
         (T_Exports_vOut37 _exportsItext) = inv_Exports_s38 _exportsX38 (T_Exports_vIn37 )
         _text = rule174 _exportsItext
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule175 _text
         __result_ = T_MaybeExports_vOut91 _lhsOtext
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule174 #-}
   rule174 = \ ((_exportsItext) ::  [       Doc ] ) ->
                                    Just _exportsItext
   {-# INLINE rule175 #-}
   rule175 = \ _text ->
     _text

-- MaybeExpression ---------------------------------------------
-- wrapper
data Inh_MaybeExpression  = Inh_MaybeExpression {  }
data Syn_MaybeExpression  = Syn_MaybeExpression { text_Syn_MaybeExpression :: (        Maybe Doc  ) }
{-# INLINABLE wrap_MaybeExpression #-}
wrap_MaybeExpression :: T_MaybeExpression  -> Inh_MaybeExpression  -> (Syn_MaybeExpression )
wrap_MaybeExpression (T_MaybeExpression act) (Inh_MaybeExpression ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg94 = T_MaybeExpression_vIn94 
        (T_MaybeExpression_vOut94 _lhsOtext) <- return (inv_MaybeExpression_s95 sem arg94)
        return (Syn_MaybeExpression _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeExpression #-}
sem_MaybeExpression :: MaybeExpression  -> T_MaybeExpression 
sem_MaybeExpression ( MaybeExpression_Nothing  ) = sem_MaybeExpression_Nothing 
sem_MaybeExpression ( MaybeExpression_Just expression_ ) = sem_MaybeExpression_Just ( sem_Expression expression_ )

-- semantic domain
newtype T_MaybeExpression  = T_MaybeExpression {
                                               attach_T_MaybeExpression :: Identity (T_MaybeExpression_s95 )
                                               }
newtype T_MaybeExpression_s95  = C_MaybeExpression_s95 {
                                                       inv_MaybeExpression_s95 :: (T_MaybeExpression_v94 )
                                                       }
data T_MaybeExpression_s96  = C_MaybeExpression_s96
type T_MaybeExpression_v94  = (T_MaybeExpression_vIn94 ) -> (T_MaybeExpression_vOut94 )
data T_MaybeExpression_vIn94  = T_MaybeExpression_vIn94 
data T_MaybeExpression_vOut94  = T_MaybeExpression_vOut94 (        Maybe Doc  )
{-# NOINLINE sem_MaybeExpression_Nothing #-}
sem_MaybeExpression_Nothing ::  T_MaybeExpression 
sem_MaybeExpression_Nothing  = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 ) -> ( let
         _text = rule176  ()
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule177 _text
         __result_ = T_MaybeExpression_vOut94 _lhsOtext
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule176 #-}
   rule176 = \  (_ :: ()) ->
                                 Nothing
   {-# INLINE rule177 #-}
   rule177 = \ _text ->
     _text
{-# NOINLINE sem_MaybeExpression_Just #-}
sem_MaybeExpression_Just :: T_Expression  -> T_MaybeExpression 
sem_MaybeExpression_Just arg_expression_ = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 ) -> ( let
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule178 _expressionItext
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule179 _text
         __result_ = T_MaybeExpression_vOut94 _lhsOtext
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule178 #-}
   rule178 = \ ((_expressionItext) :: Doc) ->
                                 Just _expressionItext
   {-# INLINE rule179 #-}
   rule179 = \ _text ->
     _text

-- MaybeImportSpecification ------------------------------------
-- wrapper
data Inh_MaybeImportSpecification  = Inh_MaybeImportSpecification {  }
data Syn_MaybeImportSpecification  = Syn_MaybeImportSpecification { text_Syn_MaybeImportSpecification :: (        Maybe Doc  ) }
{-# INLINABLE wrap_MaybeImportSpecification #-}
wrap_MaybeImportSpecification :: T_MaybeImportSpecification  -> Inh_MaybeImportSpecification  -> (Syn_MaybeImportSpecification )
wrap_MaybeImportSpecification (T_MaybeImportSpecification act) (Inh_MaybeImportSpecification ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg97 = T_MaybeImportSpecification_vIn97 
        (T_MaybeImportSpecification_vOut97 _lhsOtext) <- return (inv_MaybeImportSpecification_s98 sem arg97)
        return (Syn_MaybeImportSpecification _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeImportSpecification #-}
sem_MaybeImportSpecification :: MaybeImportSpecification  -> T_MaybeImportSpecification 
sem_MaybeImportSpecification ( MaybeImportSpecification_Nothing  ) = sem_MaybeImportSpecification_Nothing 
sem_MaybeImportSpecification ( MaybeImportSpecification_Just importspecification_ ) = sem_MaybeImportSpecification_Just ( sem_ImportSpecification importspecification_ )

-- semantic domain
newtype T_MaybeImportSpecification  = T_MaybeImportSpecification {
                                                                 attach_T_MaybeImportSpecification :: Identity (T_MaybeImportSpecification_s98 )
                                                                 }
newtype T_MaybeImportSpecification_s98  = C_MaybeImportSpecification_s98 {
                                                                         inv_MaybeImportSpecification_s98 :: (T_MaybeImportSpecification_v97 )
                                                                         }
data T_MaybeImportSpecification_s99  = C_MaybeImportSpecification_s99
type T_MaybeImportSpecification_v97  = (T_MaybeImportSpecification_vIn97 ) -> (T_MaybeImportSpecification_vOut97 )
data T_MaybeImportSpecification_vIn97  = T_MaybeImportSpecification_vIn97 
data T_MaybeImportSpecification_vOut97  = T_MaybeImportSpecification_vOut97 (        Maybe Doc  )
{-# NOINLINE sem_MaybeImportSpecification_Nothing #-}
sem_MaybeImportSpecification_Nothing ::  T_MaybeImportSpecification 
sem_MaybeImportSpecification_Nothing  = T_MaybeImportSpecification (return st98) where
   {-# NOINLINE st98 #-}
   st98 = let
      v97 :: T_MaybeImportSpecification_v97 
      v97 = \ (T_MaybeImportSpecification_vIn97 ) -> ( let
         _text = rule180  ()
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule181 _text
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOtext
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule180 #-}
   rule180 = \  (_ :: ()) ->
                               Nothing
   {-# INLINE rule181 #-}
   rule181 = \ _text ->
     _text
{-# NOINLINE sem_MaybeImportSpecification_Just #-}
sem_MaybeImportSpecification_Just :: T_ImportSpecification  -> T_MaybeImportSpecification 
sem_MaybeImportSpecification_Just arg_importspecification_ = T_MaybeImportSpecification (return st98) where
   {-# NOINLINE st98 #-}
   st98 = let
      v97 :: T_MaybeImportSpecification_v97 
      v97 = \ (T_MaybeImportSpecification_vIn97 ) -> ( let
         _importspecificationX77 = Control.Monad.Identity.runIdentity (attach_T_ImportSpecification (arg_importspecification_))
         (T_ImportSpecification_vOut76 _importspecificationItext) = inv_ImportSpecification_s77 _importspecificationX77 (T_ImportSpecification_vIn76 )
         _text = rule182 _importspecificationItext
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule183 _text
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOtext
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule182 #-}
   rule182 = \ ((_importspecificationItext) :: Doc) ->
                               Just _importspecificationItext
   {-# INLINE rule183 #-}
   rule183 = \ _text ->
     _text

-- MaybeInt ----------------------------------------------------
-- wrapper
data Inh_MaybeInt  = Inh_MaybeInt {  }
data Syn_MaybeInt  = Syn_MaybeInt { text_Syn_MaybeInt :: (        Maybe Doc  ) }
{-# INLINABLE wrap_MaybeInt #-}
wrap_MaybeInt :: T_MaybeInt  -> Inh_MaybeInt  -> (Syn_MaybeInt )
wrap_MaybeInt (T_MaybeInt act) (Inh_MaybeInt ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg100 = T_MaybeInt_vIn100 
        (T_MaybeInt_vOut100 _lhsOtext) <- return (inv_MaybeInt_s101 sem arg100)
        return (Syn_MaybeInt _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeInt #-}
sem_MaybeInt :: MaybeInt  -> T_MaybeInt 
sem_MaybeInt ( MaybeInt_Nothing  ) = sem_MaybeInt_Nothing 
sem_MaybeInt ( MaybeInt_Just int_ ) = sem_MaybeInt_Just int_

-- semantic domain
newtype T_MaybeInt  = T_MaybeInt {
                                 attach_T_MaybeInt :: Identity (T_MaybeInt_s101 )
                                 }
newtype T_MaybeInt_s101  = C_MaybeInt_s101 {
                                           inv_MaybeInt_s101 :: (T_MaybeInt_v100 )
                                           }
data T_MaybeInt_s102  = C_MaybeInt_s102
type T_MaybeInt_v100  = (T_MaybeInt_vIn100 ) -> (T_MaybeInt_vOut100 )
data T_MaybeInt_vIn100  = T_MaybeInt_vIn100 
data T_MaybeInt_vOut100  = T_MaybeInt_vOut100 (        Maybe Doc  )
{-# NOINLINE sem_MaybeInt_Nothing #-}
sem_MaybeInt_Nothing ::  T_MaybeInt 
sem_MaybeInt_Nothing  = T_MaybeInt (return st101) where
   {-# NOINLINE st101 #-}
   st101 = let
      v100 :: T_MaybeInt_v100 
      v100 = \ (T_MaybeInt_vIn100 ) -> ( let
         _text = rule184  ()
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule185 _text
         __result_ = T_MaybeInt_vOut100 _lhsOtext
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule184 #-}
   rule184 = \  (_ :: ()) ->
                                        Nothing
   {-# INLINE rule185 #-}
   rule185 = \ _text ->
     _text
{-# NOINLINE sem_MaybeInt_Just #-}
sem_MaybeInt_Just :: (Int) -> T_MaybeInt 
sem_MaybeInt_Just arg_int_ = T_MaybeInt (return st101) where
   {-# NOINLINE st101 #-}
   st101 = let
      v100 :: T_MaybeInt_v100 
      v100 = \ (T_MaybeInt_vIn100 ) -> ( let
         _text = rule186 arg_int_
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule187 _text
         __result_ = T_MaybeInt_vOut100 _lhsOtext
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule186 #-}
   rule186 = \ int_ ->
                                        Just (int int_)
   {-# INLINE rule187 #-}
   rule187 = \ _text ->
     _text

-- MaybeName ---------------------------------------------------
-- wrapper
data Inh_MaybeName  = Inh_MaybeName {  }
data Syn_MaybeName  = Syn_MaybeName { text_Syn_MaybeName :: (        Maybe Doc  ) }
{-# INLINABLE wrap_MaybeName #-}
wrap_MaybeName :: T_MaybeName  -> Inh_MaybeName  -> (Syn_MaybeName )
wrap_MaybeName (T_MaybeName act) (Inh_MaybeName ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg103 = T_MaybeName_vIn103 
        (T_MaybeName_vOut103 _lhsOtext) <- return (inv_MaybeName_s104 sem arg103)
        return (Syn_MaybeName _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeName #-}
sem_MaybeName :: MaybeName  -> T_MaybeName 
sem_MaybeName ( MaybeName_Nothing  ) = sem_MaybeName_Nothing 
sem_MaybeName ( MaybeName_Just name_ ) = sem_MaybeName_Just ( sem_Name name_ )

-- semantic domain
newtype T_MaybeName  = T_MaybeName {
                                   attach_T_MaybeName :: Identity (T_MaybeName_s104 )
                                   }
newtype T_MaybeName_s104  = C_MaybeName_s104 {
                                             inv_MaybeName_s104 :: (T_MaybeName_v103 )
                                             }
data T_MaybeName_s105  = C_MaybeName_s105
type T_MaybeName_v103  = (T_MaybeName_vIn103 ) -> (T_MaybeName_vOut103 )
data T_MaybeName_vIn103  = T_MaybeName_vIn103 
data T_MaybeName_vOut103  = T_MaybeName_vOut103 (        Maybe Doc  )
{-# NOINLINE sem_MaybeName_Nothing #-}
sem_MaybeName_Nothing ::  T_MaybeName 
sem_MaybeName_Nothing  = T_MaybeName (return st104) where
   {-# NOINLINE st104 #-}
   st104 = let
      v103 :: T_MaybeName_v103 
      v103 = \ (T_MaybeName_vIn103 ) -> ( let
         _text = rule188  ()
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule189 _text
         __result_ = T_MaybeName_vOut103 _lhsOtext
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule188 #-}
   rule188 = \  (_ :: ()) ->
                                       Nothing
   {-# INLINE rule189 #-}
   rule189 = \ _text ->
     _text
{-# NOINLINE sem_MaybeName_Just #-}
sem_MaybeName_Just :: T_Name  -> T_MaybeName 
sem_MaybeName_Just arg_name_ = T_MaybeName (return st104) where
   {-# NOINLINE st104 #-}
   st104 = let
      v103 :: T_MaybeName_v103 
      v103 = \ (T_MaybeName_vIn103 ) -> ( let
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule190 _nameItext
         _lhsOtext ::         Maybe Doc  
         _lhsOtext = rule191 _text
         __result_ = T_MaybeName_vOut103 _lhsOtext
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule190 #-}
   rule190 = \ ((_nameItext) :: Doc) ->
                                       Just _nameItext
   {-# INLINE rule191 #-}
   rule191 = \ _text ->
     _text

-- MaybeNames --------------------------------------------------
-- wrapper
data Inh_MaybeNames  = Inh_MaybeNames {  }
data Syn_MaybeNames  = Syn_MaybeNames { text_Syn_MaybeNames :: ( Maybe [       Doc ] ) }
{-# INLINABLE wrap_MaybeNames #-}
wrap_MaybeNames :: T_MaybeNames  -> Inh_MaybeNames  -> (Syn_MaybeNames )
wrap_MaybeNames (T_MaybeNames act) (Inh_MaybeNames ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg106 = T_MaybeNames_vIn106 
        (T_MaybeNames_vOut106 _lhsOtext) <- return (inv_MaybeNames_s107 sem arg106)
        return (Syn_MaybeNames _lhsOtext)
   )

-- cata
{-# NOINLINE sem_MaybeNames #-}
sem_MaybeNames :: MaybeNames  -> T_MaybeNames 
sem_MaybeNames ( MaybeNames_Nothing  ) = sem_MaybeNames_Nothing 
sem_MaybeNames ( MaybeNames_Just names_ ) = sem_MaybeNames_Just ( sem_Names names_ )

-- semantic domain
newtype T_MaybeNames  = T_MaybeNames {
                                     attach_T_MaybeNames :: Identity (T_MaybeNames_s107 )
                                     }
newtype T_MaybeNames_s107  = C_MaybeNames_s107 {
                                               inv_MaybeNames_s107 :: (T_MaybeNames_v106 )
                                               }
data T_MaybeNames_s108  = C_MaybeNames_s108
type T_MaybeNames_v106  = (T_MaybeNames_vIn106 ) -> (T_MaybeNames_vOut106 )
data T_MaybeNames_vIn106  = T_MaybeNames_vIn106 
data T_MaybeNames_vOut106  = T_MaybeNames_vOut106 ( Maybe [       Doc ] )
{-# NOINLINE sem_MaybeNames_Nothing #-}
sem_MaybeNames_Nothing ::  T_MaybeNames 
sem_MaybeNames_Nothing  = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _text = rule192  ()
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule193 _text
         __result_ = T_MaybeNames_vOut106 _lhsOtext
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule192 #-}
   rule192 = \  (_ :: ()) ->
                                    Nothing
   {-# INLINE rule193 #-}
   rule193 = \ _text ->
     _text
{-# NOINLINE sem_MaybeNames_Just #-}
sem_MaybeNames_Just :: T_Names  -> T_MaybeNames 
sem_MaybeNames_Just arg_names_ = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         (T_Names_vOut115 _namesIisIdentifier _namesIisOperator _namesIisSpecial _namesItext) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         _text = rule194 _namesItext
         _lhsOtext ::  Maybe [       Doc ] 
         _lhsOtext = rule195 _text
         __result_ = T_MaybeNames_vOut106 _lhsOtext
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule194 #-}
   rule194 = \ ((_namesItext) ::  [       Doc ] ) ->
                                    Just _namesItext
   {-# INLINE rule195 #-}
   rule195 = \ _text ->
     _text

-- Module ------------------------------------------------------
-- wrapper
data Inh_Module  = Inh_Module {  }
data Syn_Module  = Syn_Module { text_Syn_Module :: (Doc) }
{-# INLINABLE wrap_Module #-}
wrap_Module :: T_Module  -> Inh_Module  -> (Syn_Module )
wrap_Module (T_Module act) (Inh_Module ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg109 = T_Module_vIn109 
        (T_Module_vOut109 _lhsOtext) <- return (inv_Module_s110 sem arg109)
        return (Syn_Module _lhsOtext)
   )

-- cata
{-# INLINE sem_Module #-}
sem_Module :: Module  -> T_Module 
sem_Module ( Module_Module range_ name_ exports_ body_ ) = sem_Module_Module ( sem_Range range_ ) ( sem_MaybeName name_ ) ( sem_MaybeExports exports_ ) ( sem_Body body_ )

-- semantic domain
newtype T_Module  = T_Module {
                             attach_T_Module :: Identity (T_Module_s110 )
                             }
newtype T_Module_s110  = C_Module_s110 {
                                       inv_Module_s110 :: (T_Module_v109 )
                                       }
data T_Module_s111  = C_Module_s111
type T_Module_v109  = (T_Module_vIn109 ) -> (T_Module_vOut109 )
data T_Module_vIn109  = T_Module_vIn109 
data T_Module_vOut109  = T_Module_vOut109 (Doc)
{-# NOINLINE sem_Module_Module #-}
sem_Module_Module :: T_Range  -> T_MaybeName  -> T_MaybeExports  -> T_Body  -> T_Module 
sem_Module_Module arg_range_ arg_name_ arg_exports_ arg_body_ = T_Module (return st110) where
   {-# NOINLINE st110 #-}
   st110 = let
      v109 :: T_Module_v109 
      v109 = \ (T_Module_vIn109 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_name_))
         _exportsX92 = Control.Monad.Identity.runIdentity (attach_T_MaybeExports (arg_exports_))
         _bodyX14 = Control.Monad.Identity.runIdentity (attach_T_Body (arg_body_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeName_vOut103 _nameItext) = inv_MaybeName_s104 _nameX104 (T_MaybeName_vIn103 )
         (T_MaybeExports_vOut91 _exportsItext) = inv_MaybeExports_s92 _exportsX92 (T_MaybeExports_vIn91 )
         (T_Body_vOut13 _bodyItext) = inv_Body_s14 _bodyX14 (T_Body_vIn13 )
         _text = rule196 _bodyItext _exportsItext _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule197 _text
         __result_ = T_Module_vOut109 _lhsOtext
         in __result_ )
     in C_Module_s110 v109
   {-# INLINE rule196 #-}
   rule196 = \ ((_bodyItext) :: Doc) ((_exportsItext) ::  Maybe [       Doc ] ) ((_nameItext) ::         Maybe Doc  ) ->
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
   {-# INLINE rule197 #-}
   rule197 = \ _text ->
     _text

-- Name --------------------------------------------------------
-- wrapper
data Inh_Name  = Inh_Name {  }
data Syn_Name  = Syn_Name { isIdentifier_Syn_Name :: (Bool), isOperator_Syn_Name :: (Bool), isSpecial_Syn_Name :: (Bool), text_Syn_Name :: (Doc) }
{-# INLINABLE wrap_Name #-}
wrap_Name :: T_Name  -> Inh_Name  -> (Syn_Name )
wrap_Name (T_Name act) (Inh_Name ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg112 = T_Name_vIn112 
        (T_Name_vOut112 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext) <- return (inv_Name_s113 sem arg112)
        return (Syn_Name _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Name #-}
sem_Name :: Name  -> T_Name 
sem_Name ( Name_Identifier range_ module_ name_ ) = sem_Name_Identifier ( sem_Range range_ ) ( sem_Strings module_ ) name_
sem_Name ( Name_Operator range_ module_ name_ ) = sem_Name_Operator ( sem_Range range_ ) ( sem_Strings module_ ) name_
sem_Name ( Name_Special range_ module_ name_ ) = sem_Name_Special ( sem_Range range_ ) ( sem_Strings module_ ) name_

-- semantic domain
newtype T_Name  = T_Name {
                         attach_T_Name :: Identity (T_Name_s113 )
                         }
newtype T_Name_s113  = C_Name_s113 {
                                   inv_Name_s113 :: (T_Name_v112 )
                                   }
data T_Name_s114  = C_Name_s114
type T_Name_v112  = (T_Name_vIn112 ) -> (T_Name_vOut112 )
data T_Name_vIn112  = T_Name_vIn112 
data T_Name_vOut112  = T_Name_vOut112 (Bool) (Bool) (Bool) (Doc)
{-# NOINLINE sem_Name_Identifier #-}
sem_Name_Identifier :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Identifier arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleItext) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _text = rule198 arg_name_
         _lhsOisIdentifier :: Bool
         _lhsOisIdentifier = rule199  ()
         _lhsOisOperator :: Bool
         _lhsOisOperator = rule200  ()
         _lhsOisSpecial :: Bool
         _lhsOisSpecial = rule201  ()
         _lhsOtext :: Doc
         _lhsOtext = rule202 _text
         __result_ = T_Name_vOut112 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule198 #-}
   rule198 = \ name_ ->
                                            text name_
   {-# INLINE rule199 #-}
   rule199 = \  (_ :: ()) ->
                                                    True
   {-# INLINE rule200 #-}
   rule200 = \  (_ :: ()) ->
     False
   {-# INLINE rule201 #-}
   rule201 = \  (_ :: ()) ->
     False
   {-# INLINE rule202 #-}
   rule202 = \ _text ->
     _text
{-# NOINLINE sem_Name_Operator #-}
sem_Name_Operator :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Operator arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleItext) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _text = rule203 arg_name_
         _lhsOisOperator :: Bool
         _lhsOisOperator = rule204  ()
         _lhsOisIdentifier :: Bool
         _lhsOisIdentifier = rule205  ()
         _lhsOisSpecial :: Bool
         _lhsOisSpecial = rule206  ()
         _lhsOtext :: Doc
         _lhsOtext = rule207 _text
         __result_ = T_Name_vOut112 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule203 #-}
   rule203 = \ name_ ->
                                            text name_
   {-# INLINE rule204 #-}
   rule204 = \  (_ :: ()) ->
                                                  True
   {-# INLINE rule205 #-}
   rule205 = \  (_ :: ()) ->
     False
   {-# INLINE rule206 #-}
   rule206 = \  (_ :: ()) ->
     False
   {-# INLINE rule207 #-}
   rule207 = \ _text ->
     _text
{-# NOINLINE sem_Name_Special #-}
sem_Name_Special :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Special arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleItext) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _text = rule208 arg_name_
         _lhsOisSpecial :: Bool
         _lhsOisSpecial = rule209  ()
         _lhsOisIdentifier :: Bool
         _lhsOisIdentifier = rule210  ()
         _lhsOisOperator :: Bool
         _lhsOisOperator = rule211  ()
         _lhsOtext :: Doc
         _lhsOtext = rule212 _text
         __result_ = T_Name_vOut112 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule208 #-}
   rule208 = \ name_ ->
                                            text name_
   {-# INLINE rule209 #-}
   rule209 = \  (_ :: ()) ->
                                                 True
   {-# INLINE rule210 #-}
   rule210 = \  (_ :: ()) ->
     False
   {-# INLINE rule211 #-}
   rule211 = \  (_ :: ()) ->
     False
   {-# INLINE rule212 #-}
   rule212 = \ _text ->
     _text

-- Names -------------------------------------------------------
-- wrapper
data Inh_Names  = Inh_Names {  }
data Syn_Names  = Syn_Names { isIdentifier_Syn_Names :: ( [Bool] ), isOperator_Syn_Names :: ( [Bool] ), isSpecial_Syn_Names :: ( [Bool] ), text_Syn_Names :: ( [       Doc ] ) }
{-# INLINABLE wrap_Names #-}
wrap_Names :: T_Names  -> Inh_Names  -> (Syn_Names )
wrap_Names (T_Names act) (Inh_Names ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg115 = T_Names_vIn115 
        (T_Names_vOut115 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext) <- return (inv_Names_s116 sem arg115)
        return (Syn_Names _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Names #-}
sem_Names :: Names  -> T_Names 
sem_Names list = Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list)

-- semantic domain
newtype T_Names  = T_Names {
                           attach_T_Names :: Identity (T_Names_s116 )
                           }
newtype T_Names_s116  = C_Names_s116 {
                                     inv_Names_s116 :: (T_Names_v115 )
                                     }
data T_Names_s117  = C_Names_s117
type T_Names_v115  = (T_Names_vIn115 ) -> (T_Names_vOut115 )
data T_Names_vIn115  = T_Names_vIn115 
data T_Names_vOut115  = T_Names_vOut115 ( [Bool] ) ( [Bool] ) ( [Bool] ) ( [       Doc ] )
{-# NOINLINE sem_Names_Cons #-}
sem_Names_Cons :: T_Name  -> T_Names  -> T_Names 
sem_Names_Cons arg_hd_ arg_tl_ = T_Names (return st116) where
   {-# NOINLINE st116 #-}
   st116 = let
      v115 :: T_Names_v115 
      v115 = \ (T_Names_vIn115 ) -> ( let
         _hdX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_hd_))
         _tlX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_tl_))
         (T_Name_vOut112 _hdIisIdentifier _hdIisOperator _hdIisSpecial _hdItext) = inv_Name_s113 _hdX113 (T_Name_vIn112 )
         (T_Names_vOut115 _tlIisIdentifier _tlIisOperator _tlIisSpecial _tlItext) = inv_Names_s116 _tlX116 (T_Names_vIn115 )
         _lhsOisIdentifier ::  [Bool] 
         _lhsOisIdentifier = rule213 _hdIisIdentifier _tlIisIdentifier
         _lhsOisOperator ::  [Bool] 
         _lhsOisOperator = rule214 _hdIisOperator _tlIisOperator
         _lhsOisSpecial ::  [Bool] 
         _lhsOisSpecial = rule215 _hdIisSpecial _tlIisSpecial
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule216 _hdItext _tlItext
         __result_ = T_Names_vOut115 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule213 #-}
   rule213 = \ ((_hdIisIdentifier) :: Bool) ((_tlIisIdentifier) ::  [Bool] ) ->
     _hdIisIdentifier  :  _tlIisIdentifier
   {-# INLINE rule214 #-}
   rule214 = \ ((_hdIisOperator) :: Bool) ((_tlIisOperator) ::  [Bool] ) ->
     _hdIisOperator  :  _tlIisOperator
   {-# INLINE rule215 #-}
   rule215 = \ ((_hdIisSpecial) :: Bool) ((_tlIisSpecial) ::  [Bool] ) ->
     _hdIisSpecial  :  _tlIisSpecial
   {-# INLINE rule216 #-}
   rule216 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Names_Nil #-}
sem_Names_Nil ::  T_Names 
sem_Names_Nil  = T_Names (return st116) where
   {-# NOINLINE st116 #-}
   st116 = let
      v115 :: T_Names_v115 
      v115 = \ (T_Names_vIn115 ) -> ( let
         _lhsOisIdentifier ::  [Bool] 
         _lhsOisIdentifier = rule217  ()
         _lhsOisOperator ::  [Bool] 
         _lhsOisOperator = rule218  ()
         _lhsOisSpecial ::  [Bool] 
         _lhsOisSpecial = rule219  ()
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule220  ()
         __result_ = T_Names_vOut115 _lhsOisIdentifier _lhsOisOperator _lhsOisSpecial _lhsOtext
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule217 #-}
   rule217 = \  (_ :: ()) ->
     []
   {-# INLINE rule218 #-}
   rule218 = \  (_ :: ()) ->
     []
   {-# INLINE rule219 #-}
   rule219 = \  (_ :: ()) ->
     []
   {-# INLINE rule220 #-}
   rule220 = \  (_ :: ()) ->
     []

-- Pattern -----------------------------------------------------
-- wrapper
data Inh_Pattern  = Inh_Pattern {  }
data Syn_Pattern  = Syn_Pattern { text_Syn_Pattern :: (Doc) }
{-# INLINABLE wrap_Pattern #-}
wrap_Pattern :: T_Pattern  -> Inh_Pattern  -> (Syn_Pattern )
wrap_Pattern (T_Pattern act) (Inh_Pattern ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg118 = T_Pattern_vIn118 
        (T_Pattern_vOut118 _lhsOtext) <- return (inv_Pattern_s119 sem arg118)
        return (Syn_Pattern _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Pattern #-}
sem_Pattern :: Pattern  -> T_Pattern 
sem_Pattern ( Pattern_Hole range_ id_ ) = sem_Pattern_Hole ( sem_Range range_ ) id_
sem_Pattern ( Pattern_Literal range_ literal_ ) = sem_Pattern_Literal ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_Variable range_ name_ ) = sem_Pattern_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Pattern ( Pattern_Constructor range_ name_ patterns_ ) = sem_Pattern_Constructor ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Parenthesized range_ pattern_ ) = sem_Pattern_Parenthesized ( sem_Range range_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_ ) = sem_Pattern_InfixConstructor ( sem_Range range_ ) ( sem_Pattern leftPattern_ ) ( sem_Name constructorOperator_ ) ( sem_Pattern rightPattern_ )
sem_Pattern ( Pattern_List range_ patterns_ ) = sem_Pattern_List ( sem_Range range_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Tuple range_ patterns_ ) = sem_Pattern_Tuple ( sem_Range range_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Record range_ name_ recordPatternBindings_ ) = sem_Pattern_Record ( sem_Range range_ ) ( sem_Name name_ ) ( sem_RecordPatternBindings recordPatternBindings_ )
sem_Pattern ( Pattern_Negate range_ literal_ ) = sem_Pattern_Negate ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_As range_ name_ pattern_ ) = sem_Pattern_As ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_Wildcard range_ ) = sem_Pattern_Wildcard ( sem_Range range_ )
sem_Pattern ( Pattern_Irrefutable range_ pattern_ ) = sem_Pattern_Irrefutable ( sem_Range range_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_Successor range_ name_ literal_ ) = sem_Pattern_Successor ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_NegateFloat range_ literal_ ) = sem_Pattern_NegateFloat ( sem_Range range_ ) ( sem_Literal literal_ )

-- semantic domain
newtype T_Pattern  = T_Pattern {
                               attach_T_Pattern :: Identity (T_Pattern_s119 )
                               }
newtype T_Pattern_s119  = C_Pattern_s119 {
                                         inv_Pattern_s119 :: (T_Pattern_v118 )
                                         }
data T_Pattern_s120  = C_Pattern_s120
type T_Pattern_v118  = (T_Pattern_vIn118 ) -> (T_Pattern_vOut118 )
data T_Pattern_vIn118  = T_Pattern_vIn118 
data T_Pattern_vOut118  = T_Pattern_vOut118 (Doc)
{-# NOINLINE sem_Pattern_Hole #-}
sem_Pattern_Hole :: T_Range  -> (Integer) -> T_Pattern 
sem_Pattern_Hole arg_range_ _ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule221  ()
         _lhsOtext :: Doc
         _lhsOtext = rule222 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule221 #-}
   rule221 = \  (_ :: ()) ->
                                         text hole
   {-# INLINE rule222 #-}
   rule222 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Literal #-}
sem_Pattern_Literal :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Literal arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalItext) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _text = rule223 _literalItext
         _lhsOtext :: Doc
         _lhsOtext = rule224 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule223 #-}
   rule223 = \ ((_literalItext) :: Doc) ->
                                         _literalItext
   {-# INLINE rule224 #-}
   rule224 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Variable #-}
sem_Pattern_Variable :: T_Range  -> T_Name  -> T_Pattern 
sem_Pattern_Variable arg_range_ arg_name_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule225 _nameIisOperator _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule226 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule225 #-}
   rule225 = \ ((_nameIisOperator) :: Bool) ((_nameItext) :: Doc) ->
                                         parensIf _nameIisOperator _nameItext
   {-# INLINE rule226 #-}
   rule226 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Constructor #-}
sem_Pattern_Constructor :: T_Range  -> T_Name  -> T_Patterns  -> T_Pattern 
sem_Pattern_Constructor arg_range_ arg_name_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _text = rule227 _nameIisOperator _nameItext _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule228 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule227 #-}
   rule227 = \ ((_nameIisOperator) :: Bool) ((_nameItext) :: Doc) ((_patternsItext) ::  [       Doc ] ) ->
                                         foldl (<+>) (parensIf _nameIisOperator _nameItext) _patternsItext
   {-# INLINE rule228 #-}
   rule228 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Parenthesized #-}
sem_Pattern_Parenthesized :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Parenthesized arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _text = rule229 _patternItext
         _lhsOtext :: Doc
         _lhsOtext = rule230 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule229 #-}
   rule229 = \ ((_patternItext) :: Doc) ->
                                         parens _patternItext
   {-# INLINE rule230 #-}
   rule230 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_InfixConstructor #-}
sem_Pattern_InfixConstructor :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_InfixConstructor arg_range_ arg_leftPattern_ arg_constructorOperator_ arg_rightPattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternItext) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 )
         (T_Name_vOut112 _constructorOperatorIisIdentifier _constructorOperatorIisOperator _constructorOperatorIisSpecial _constructorOperatorItext) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternItext) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 )
         _text = rule231 _constructorOperatorItext _leftPatternItext _rightPatternItext
         _lhsOtext :: Doc
         _lhsOtext = rule232 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule231 #-}
   rule231 = \ ((_constructorOperatorItext) :: Doc) ((_leftPatternItext) :: Doc) ((_rightPatternItext) :: Doc) ->
                                         _leftPatternItext <+> _constructorOperatorItext <+> _rightPatternItext
   {-# INLINE rule232 #-}
   rule232 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_List #-}
sem_Pattern_List :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_List arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _text = rule233 _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule234 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule233 #-}
   rule233 = \ ((_patternsItext) ::  [       Doc ] ) ->
                                         PPrint.list _patternsItext
   {-# INLINE rule234 #-}
   rule234 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Tuple #-}
sem_Pattern_Tuple :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_Tuple arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsItext) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _text = rule235 _patternsItext
         _lhsOtext :: Doc
         _lhsOtext = rule236 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule235 #-}
   rule235 = \ ((_patternsItext) ::  [       Doc ] ) ->
                                         tupled _patternsItext
   {-# INLINE rule236 #-}
   rule236 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Record #-}
sem_Pattern_Record :: T_Range  -> T_Name  -> T_RecordPatternBindings  -> T_Pattern 
sem_Pattern_Record arg_range_ arg_name_ arg_recordPatternBindings_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordPatternBindingsX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_recordPatternBindings_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordPatternBindings_vOut145 _recordPatternBindingsItext) = inv_RecordPatternBindings_s146 _recordPatternBindingsX146 (T_RecordPatternBindings_vIn145 )
         _text = rule237  ()
         _lhsOtext :: Doc
         _lhsOtext = rule238 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule237 #-}
   rule237 = \  (_ :: ()) ->
                                         text "{- !!! record pattern -}"
   {-# INLINE rule238 #-}
   rule238 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Negate #-}
sem_Pattern_Negate :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Negate arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalItext) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _text = rule239 _literalItext
         _lhsOtext :: Doc
         _lhsOtext = rule240 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule239 #-}
   rule239 = \ ((_literalItext) :: Doc) ->
                                         text "-" <> _literalItext
   {-# INLINE rule240 #-}
   rule240 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_As #-}
sem_Pattern_As :: T_Range  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_As arg_range_ arg_name_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _text = rule241 _nameItext _patternItext
         _lhsOtext :: Doc
         _lhsOtext = rule242 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule241 #-}
   rule241 = \ ((_nameItext) :: Doc) ((_patternItext) :: Doc) ->
                                         _nameItext <> text "@" <> _patternItext
   {-# INLINE rule242 #-}
   rule242 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Wildcard #-}
sem_Pattern_Wildcard :: T_Range  -> T_Pattern 
sem_Pattern_Wildcard arg_range_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule243  ()
         _lhsOtext :: Doc
         _lhsOtext = rule244 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule243 #-}
   rule243 = \  (_ :: ()) ->
                                         text "_"
   {-# INLINE rule244 #-}
   rule244 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Irrefutable #-}
sem_Pattern_Irrefutable :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Irrefutable arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _text = rule245 _patternItext
         _lhsOtext :: Doc
         _lhsOtext = rule246 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule245 #-}
   rule245 = \ ((_patternItext) :: Doc) ->
                                         text "~" <> _patternItext
   {-# INLINE rule246 #-}
   rule246 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_Successor #-}
sem_Pattern_Successor :: T_Range  -> T_Name  -> T_Literal  -> T_Pattern 
sem_Pattern_Successor arg_range_ arg_name_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Literal_vOut85 _literalItext) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _text = rule247 _literalItext _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule248 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule247 #-}
   rule247 = \ ((_literalItext) :: Doc) ((_nameItext) :: Doc) ->
                                         _nameItext <+> text "+" <+> _literalItext
   {-# INLINE rule248 #-}
   rule248 = \ _text ->
     _text
{-# NOINLINE sem_Pattern_NegateFloat #-}
sem_Pattern_NegateFloat :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_NegateFloat arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalItext) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _text = rule249 _literalItext
         _lhsOtext :: Doc
         _lhsOtext = rule250 _text
         __result_ = T_Pattern_vOut118 _lhsOtext
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule249 #-}
   rule249 = \ ((_literalItext) :: Doc) ->
                                         text "-." <> _literalItext
   {-# INLINE rule250 #-}
   rule250 = \ _text ->
     _text

-- Patterns ----------------------------------------------------
-- wrapper
data Inh_Patterns  = Inh_Patterns {  }
data Syn_Patterns  = Syn_Patterns { text_Syn_Patterns :: ( [       Doc ] ) }
{-# INLINABLE wrap_Patterns #-}
wrap_Patterns :: T_Patterns  -> Inh_Patterns  -> (Syn_Patterns )
wrap_Patterns (T_Patterns act) (Inh_Patterns ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg121 = T_Patterns_vIn121 
        (T_Patterns_vOut121 _lhsOtext) <- return (inv_Patterns_s122 sem arg121)
        return (Syn_Patterns _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Patterns #-}
sem_Patterns :: Patterns  -> T_Patterns 
sem_Patterns list = Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list)

-- semantic domain
newtype T_Patterns  = T_Patterns {
                                 attach_T_Patterns :: Identity (T_Patterns_s122 )
                                 }
newtype T_Patterns_s122  = C_Patterns_s122 {
                                           inv_Patterns_s122 :: (T_Patterns_v121 )
                                           }
data T_Patterns_s123  = C_Patterns_s123
type T_Patterns_v121  = (T_Patterns_vIn121 ) -> (T_Patterns_vOut121 )
data T_Patterns_vIn121  = T_Patterns_vIn121 
data T_Patterns_vOut121  = T_Patterns_vOut121 ( [       Doc ] )
{-# NOINLINE sem_Patterns_Cons #-}
sem_Patterns_Cons :: T_Pattern  -> T_Patterns  -> T_Patterns 
sem_Patterns_Cons arg_hd_ arg_tl_ = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 ) -> ( let
         _hdX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_hd_))
         _tlX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_tl_))
         (T_Pattern_vOut118 _hdItext) = inv_Pattern_s119 _hdX119 (T_Pattern_vIn118 )
         (T_Patterns_vOut121 _tlItext) = inv_Patterns_s122 _tlX122 (T_Patterns_vIn121 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule251 _hdItext _tlItext
         __result_ = T_Patterns_vOut121 _lhsOtext
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule251 #-}
   rule251 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Patterns_Nil #-}
sem_Patterns_Nil ::  T_Patterns 
sem_Patterns_Nil  = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule252  ()
         __result_ = T_Patterns_vOut121 _lhsOtext
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule252 #-}
   rule252 = \  (_ :: ()) ->
     []

-- Position ----------------------------------------------------
-- wrapper
data Inh_Position  = Inh_Position {  }
data Syn_Position  = Syn_Position { text_Syn_Position :: (Doc) }
{-# INLINABLE wrap_Position #-}
wrap_Position :: T_Position  -> Inh_Position  -> (Syn_Position )
wrap_Position (T_Position act) (Inh_Position ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg124 = T_Position_vIn124 
        (T_Position_vOut124 _lhsOtext) <- return (inv_Position_s125 sem arg124)
        return (Syn_Position _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Position #-}
sem_Position :: Position  -> T_Position 
sem_Position ( Position_Position filename_ line_ column_ ) = sem_Position_Position filename_ line_ column_
sem_Position ( Position_Unknown  ) = sem_Position_Unknown 

-- semantic domain
newtype T_Position  = T_Position {
                                 attach_T_Position :: Identity (T_Position_s125 )
                                 }
newtype T_Position_s125  = C_Position_s125 {
                                           inv_Position_s125 :: (T_Position_v124 )
                                           }
data T_Position_s126  = C_Position_s126
type T_Position_v124  = (T_Position_vIn124 ) -> (T_Position_vOut124 )
data T_Position_vIn124  = T_Position_vIn124 
data T_Position_vOut124  = T_Position_vOut124 (Doc)
{-# NOINLINE sem_Position_Position #-}
sem_Position_Position :: (String) -> (Int) -> (Int) -> T_Position 
sem_Position_Position arg_filename_ arg_line_ arg_column_ = T_Position (return st125) where
   {-# NOINLINE st125 #-}
   st125 = let
      v124 :: T_Position_v124 
      v124 = \ (T_Position_vIn124 ) -> ( let
         _text = rule253 arg_column_ arg_filename_ arg_line_
         _lhsOtext :: Doc
         _lhsOtext = rule254 _text
         __result_ = T_Position_vOut124 _lhsOtext
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule253 #-}
   rule253 = \ column_ filename_ line_ ->
                                        text filename_ <> tupled [int line_, int column_]
   {-# INLINE rule254 #-}
   rule254 = \ _text ->
     _text
{-# NOINLINE sem_Position_Unknown #-}
sem_Position_Unknown ::  T_Position 
sem_Position_Unknown  = T_Position (return st125) where
   {-# NOINLINE st125 #-}
   st125 = let
      v124 :: T_Position_v124 
      v124 = \ (T_Position_vIn124 ) -> ( let
         _text = rule255  ()
         _lhsOtext :: Doc
         _lhsOtext = rule256 _text
         __result_ = T_Position_vOut124 _lhsOtext
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule255 #-}
   rule255 = \  (_ :: ()) ->
                                        text "Unknown"
   {-# INLINE rule256 #-}
   rule256 = \ _text ->
     _text

-- Qualifier ---------------------------------------------------
-- wrapper
data Inh_Qualifier  = Inh_Qualifier {  }
data Syn_Qualifier  = Syn_Qualifier { text_Syn_Qualifier :: (Doc) }
{-# INLINABLE wrap_Qualifier #-}
wrap_Qualifier :: T_Qualifier  -> Inh_Qualifier  -> (Syn_Qualifier )
wrap_Qualifier (T_Qualifier act) (Inh_Qualifier ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg127 = T_Qualifier_vIn127 
        (T_Qualifier_vOut127 _lhsOtext) <- return (inv_Qualifier_s128 sem arg127)
        return (Syn_Qualifier _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Qualifier #-}
sem_Qualifier :: Qualifier  -> T_Qualifier 
sem_Qualifier ( Qualifier_Guard range_ guard_ ) = sem_Qualifier_Guard ( sem_Range range_ ) ( sem_Expression guard_ )
sem_Qualifier ( Qualifier_Let range_ declarations_ ) = sem_Qualifier_Let ( sem_Range range_ ) ( sem_Declarations declarations_ )
sem_Qualifier ( Qualifier_Generator range_ pattern_ expression_ ) = sem_Qualifier_Generator ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_Expression expression_ )
sem_Qualifier ( Qualifier_Empty range_ ) = sem_Qualifier_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Qualifier  = T_Qualifier {
                                   attach_T_Qualifier :: Identity (T_Qualifier_s128 )
                                   }
newtype T_Qualifier_s128  = C_Qualifier_s128 {
                                             inv_Qualifier_s128 :: (T_Qualifier_v127 )
                                             }
data T_Qualifier_s129  = C_Qualifier_s129
type T_Qualifier_v127  = (T_Qualifier_vIn127 ) -> (T_Qualifier_vOut127 )
data T_Qualifier_vIn127  = T_Qualifier_vIn127 
data T_Qualifier_vOut127  = T_Qualifier_vOut127 (Doc)
{-# NOINLINE sem_Qualifier_Guard #-}
sem_Qualifier_Guard :: T_Range  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Guard arg_range_ arg_guard_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardItext) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 )
         _text = rule257 _guardItext
         _lhsOtext :: Doc
         _lhsOtext = rule258 _text
         __result_ = T_Qualifier_vOut127 _lhsOtext
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule257 #-}
   rule257 = \ ((_guardItext) :: Doc) ->
                                       _guardItext
   {-# INLINE rule258 #-}
   rule258 = \ _text ->
     _text
{-# NOINLINE sem_Qualifier_Let #-}
sem_Qualifier_Let :: T_Range  -> T_Declarations  -> T_Qualifier 
sem_Qualifier_Let arg_range_ arg_declarations_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsItext) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 )
         _text = rule259 _declarationsItext
         _lhsOtext :: Doc
         _lhsOtext = rule260 _text
         __result_ = T_Qualifier_vOut127 _lhsOtext
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule259 #-}
   rule259 = \ ((_declarationsItext) ::  [       Doc ] ) ->
                                       text "let" <$> (indent 4 $ vcat _declarationsItext)
   {-# INLINE rule260 #-}
   rule260 = \ _text ->
     _text
{-# NOINLINE sem_Qualifier_Generator #-}
sem_Qualifier_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Generator arg_range_ arg_pattern_ arg_expression_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule261 _expressionItext _patternItext
         _lhsOtext :: Doc
         _lhsOtext = rule262 _text
         __result_ = T_Qualifier_vOut127 _lhsOtext
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule261 #-}
   rule261 = \ ((_expressionItext) :: Doc) ((_patternItext) :: Doc) ->
                                       _patternItext <+> text "<-" <+> _expressionItext
   {-# INLINE rule262 #-}
   rule262 = \ _text ->
     _text
{-# NOINLINE sem_Qualifier_Empty #-}
sem_Qualifier_Empty :: T_Range  -> T_Qualifier 
sem_Qualifier_Empty arg_range_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule263  ()
         _lhsOtext :: Doc
         _lhsOtext = rule264 _text
         __result_ = T_Qualifier_vOut127 _lhsOtext
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule263 #-}
   rule263 = \  (_ :: ()) ->
                                       empty
   {-# INLINE rule264 #-}
   rule264 = \ _text ->
     _text

-- Qualifiers --------------------------------------------------
-- wrapper
data Inh_Qualifiers  = Inh_Qualifiers {  }
data Syn_Qualifiers  = Syn_Qualifiers { text_Syn_Qualifiers :: ( [       Doc ] ) }
{-# INLINABLE wrap_Qualifiers #-}
wrap_Qualifiers :: T_Qualifiers  -> Inh_Qualifiers  -> (Syn_Qualifiers )
wrap_Qualifiers (T_Qualifiers act) (Inh_Qualifiers ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg130 = T_Qualifiers_vIn130 
        (T_Qualifiers_vOut130 _lhsOtext) <- return (inv_Qualifiers_s131 sem arg130)
        return (Syn_Qualifiers _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Qualifiers #-}
sem_Qualifiers :: Qualifiers  -> T_Qualifiers 
sem_Qualifiers list = Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list)

-- semantic domain
newtype T_Qualifiers  = T_Qualifiers {
                                     attach_T_Qualifiers :: Identity (T_Qualifiers_s131 )
                                     }
newtype T_Qualifiers_s131  = C_Qualifiers_s131 {
                                               inv_Qualifiers_s131 :: (T_Qualifiers_v130 )
                                               }
data T_Qualifiers_s132  = C_Qualifiers_s132
type T_Qualifiers_v130  = (T_Qualifiers_vIn130 ) -> (T_Qualifiers_vOut130 )
data T_Qualifiers_vIn130  = T_Qualifiers_vIn130 
data T_Qualifiers_vOut130  = T_Qualifiers_vOut130 ( [       Doc ] )
{-# NOINLINE sem_Qualifiers_Cons #-}
sem_Qualifiers_Cons :: T_Qualifier  -> T_Qualifiers  -> T_Qualifiers 
sem_Qualifiers_Cons arg_hd_ arg_tl_ = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 ) -> ( let
         _hdX128 = Control.Monad.Identity.runIdentity (attach_T_Qualifier (arg_hd_))
         _tlX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_tl_))
         (T_Qualifier_vOut127 _hdItext) = inv_Qualifier_s128 _hdX128 (T_Qualifier_vIn127 )
         (T_Qualifiers_vOut130 _tlItext) = inv_Qualifiers_s131 _tlX131 (T_Qualifiers_vIn130 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule265 _hdItext _tlItext
         __result_ = T_Qualifiers_vOut130 _lhsOtext
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule265 #-}
   rule265 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Qualifiers_Nil #-}
sem_Qualifiers_Nil ::  T_Qualifiers 
sem_Qualifiers_Nil  = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule266  ()
         __result_ = T_Qualifiers_vOut130 _lhsOtext
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule266 #-}
   rule266 = \  (_ :: ()) ->
     []

-- Range -------------------------------------------------------
-- wrapper
data Inh_Range  = Inh_Range {  }
data Syn_Range  = Syn_Range { text_Syn_Range :: (Doc) }
{-# INLINABLE wrap_Range #-}
wrap_Range :: T_Range  -> Inh_Range  -> (Syn_Range )
wrap_Range (T_Range act) (Inh_Range ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg133 = T_Range_vIn133 
        (T_Range_vOut133 _lhsOtext) <- return (inv_Range_s134 sem arg133)
        return (Syn_Range _lhsOtext)
   )

-- cata
{-# INLINE sem_Range #-}
sem_Range :: Range  -> T_Range 
sem_Range ( Range_Range start_ stop_ ) = sem_Range_Range ( sem_Position start_ ) ( sem_Position stop_ )

-- semantic domain
newtype T_Range  = T_Range {
                           attach_T_Range :: Identity (T_Range_s134 )
                           }
newtype T_Range_s134  = C_Range_s134 {
                                     inv_Range_s134 :: (T_Range_v133 )
                                     }
data T_Range_s135  = C_Range_s135
type T_Range_v133  = (T_Range_vIn133 ) -> (T_Range_vOut133 )
data T_Range_vIn133  = T_Range_vIn133 
data T_Range_vOut133  = T_Range_vOut133 (Doc)
{-# NOINLINE sem_Range_Range #-}
sem_Range_Range :: T_Position  -> T_Position  -> T_Range 
sem_Range_Range arg_start_ arg_stop_ = T_Range (return st134) where
   {-# NOINLINE st134 #-}
   st134 = let
      v133 :: T_Range_v133 
      v133 = \ (T_Range_vIn133 ) -> ( let
         _startX125 = Control.Monad.Identity.runIdentity (attach_T_Position (arg_start_))
         _stopX125 = Control.Monad.Identity.runIdentity (attach_T_Position (arg_stop_))
         (T_Position_vOut124 _startItext) = inv_Position_s125 _startX125 (T_Position_vIn124 )
         (T_Position_vOut124 _stopItext) = inv_Position_s125 _stopX125 (T_Position_vIn124 )
         _text = rule267 _startItext _stopItext
         _lhsOtext :: Doc
         _lhsOtext = rule268 _text
         __result_ = T_Range_vOut133 _lhsOtext
         in __result_ )
     in C_Range_s134 v133
   {-# INLINE rule267 #-}
   rule267 = \ ((_startItext) :: Doc) ((_stopItext) :: Doc) ->
                                           text "{-" <+> _startItext <+> text ", " <+> _stopItext <+> text "-}"
   {-# INLINE rule268 #-}
   rule268 = \ _text ->
     _text

-- RecordExpressionBinding -------------------------------------
-- wrapper
data Inh_RecordExpressionBinding  = Inh_RecordExpressionBinding {  }
data Syn_RecordExpressionBinding  = Syn_RecordExpressionBinding { text_Syn_RecordExpressionBinding :: (Doc) }
{-# INLINABLE wrap_RecordExpressionBinding #-}
wrap_RecordExpressionBinding :: T_RecordExpressionBinding  -> Inh_RecordExpressionBinding  -> (Syn_RecordExpressionBinding )
wrap_RecordExpressionBinding (T_RecordExpressionBinding act) (Inh_RecordExpressionBinding ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg136 = T_RecordExpressionBinding_vIn136 
        (T_RecordExpressionBinding_vOut136 _lhsOtext) <- return (inv_RecordExpressionBinding_s137 sem arg136)
        return (Syn_RecordExpressionBinding _lhsOtext)
   )

-- cata
{-# NOINLINE sem_RecordExpressionBinding #-}
sem_RecordExpressionBinding :: RecordExpressionBinding  -> T_RecordExpressionBinding 
sem_RecordExpressionBinding ( RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_ ) = sem_RecordExpressionBinding_RecordExpressionBinding ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_RecordExpressionBinding  = T_RecordExpressionBinding {
                                                               attach_T_RecordExpressionBinding :: Identity (T_RecordExpressionBinding_s137 )
                                                               }
newtype T_RecordExpressionBinding_s137  = C_RecordExpressionBinding_s137 {
                                                                         inv_RecordExpressionBinding_s137 :: (T_RecordExpressionBinding_v136 )
                                                                         }
data T_RecordExpressionBinding_s138  = C_RecordExpressionBinding_s138
type T_RecordExpressionBinding_v136  = (T_RecordExpressionBinding_vIn136 ) -> (T_RecordExpressionBinding_vOut136 )
data T_RecordExpressionBinding_vIn136  = T_RecordExpressionBinding_vIn136 
data T_RecordExpressionBinding_vOut136  = T_RecordExpressionBinding_vOut136 (Doc)
{-# NOINLINE sem_RecordExpressionBinding_RecordExpressionBinding #-}
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range  -> T_Name  -> T_Expression  -> T_RecordExpressionBinding 
sem_RecordExpressionBinding_RecordExpressionBinding arg_range_ arg_name_ arg_expression_ = T_RecordExpressionBinding (return st137) where
   {-# NOINLINE st137 #-}
   st137 = let
      v136 :: T_RecordExpressionBinding_v136 
      v136 = \ (T_RecordExpressionBinding_vIn136 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule269  ()
         _lhsOtext :: Doc
         _lhsOtext = rule270 _text
         __result_ = T_RecordExpressionBinding_vOut136 _lhsOtext
         in __result_ )
     in C_RecordExpressionBinding_s137 v136
   {-# INLINE rule269 #-}
   rule269 = \  (_ :: ()) ->
                                           text "{- !!! record expression binding -}"
   {-# INLINE rule270 #-}
   rule270 = \ _text ->
     _text

-- RecordExpressionBindings ------------------------------------
-- wrapper
data Inh_RecordExpressionBindings  = Inh_RecordExpressionBindings {  }
data Syn_RecordExpressionBindings  = Syn_RecordExpressionBindings { text_Syn_RecordExpressionBindings :: ( [       Doc ] ) }
{-# INLINABLE wrap_RecordExpressionBindings #-}
wrap_RecordExpressionBindings :: T_RecordExpressionBindings  -> Inh_RecordExpressionBindings  -> (Syn_RecordExpressionBindings )
wrap_RecordExpressionBindings (T_RecordExpressionBindings act) (Inh_RecordExpressionBindings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg139 = T_RecordExpressionBindings_vIn139 
        (T_RecordExpressionBindings_vOut139 _lhsOtext) <- return (inv_RecordExpressionBindings_s140 sem arg139)
        return (Syn_RecordExpressionBindings _lhsOtext)
   )

-- cata
{-# NOINLINE sem_RecordExpressionBindings #-}
sem_RecordExpressionBindings :: RecordExpressionBindings  -> T_RecordExpressionBindings 
sem_RecordExpressionBindings list = Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list)

-- semantic domain
newtype T_RecordExpressionBindings  = T_RecordExpressionBindings {
                                                                 attach_T_RecordExpressionBindings :: Identity (T_RecordExpressionBindings_s140 )
                                                                 }
newtype T_RecordExpressionBindings_s140  = C_RecordExpressionBindings_s140 {
                                                                           inv_RecordExpressionBindings_s140 :: (T_RecordExpressionBindings_v139 )
                                                                           }
data T_RecordExpressionBindings_s141  = C_RecordExpressionBindings_s141
type T_RecordExpressionBindings_v139  = (T_RecordExpressionBindings_vIn139 ) -> (T_RecordExpressionBindings_vOut139 )
data T_RecordExpressionBindings_vIn139  = T_RecordExpressionBindings_vIn139 
data T_RecordExpressionBindings_vOut139  = T_RecordExpressionBindings_vOut139 ( [       Doc ] )
{-# NOINLINE sem_RecordExpressionBindings_Cons #-}
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding  -> T_RecordExpressionBindings  -> T_RecordExpressionBindings 
sem_RecordExpressionBindings_Cons arg_hd_ arg_tl_ = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 ) -> ( let
         _hdX137 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBinding (arg_hd_))
         _tlX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_tl_))
         (T_RecordExpressionBinding_vOut136 _hdItext) = inv_RecordExpressionBinding_s137 _hdX137 (T_RecordExpressionBinding_vIn136 )
         (T_RecordExpressionBindings_vOut139 _tlItext) = inv_RecordExpressionBindings_s140 _tlX140 (T_RecordExpressionBindings_vIn139 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule271 _hdItext _tlItext
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOtext
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule271 #-}
   rule271 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_RecordExpressionBindings_Nil #-}
sem_RecordExpressionBindings_Nil ::  T_RecordExpressionBindings 
sem_RecordExpressionBindings_Nil  = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule272  ()
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOtext
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule272 #-}
   rule272 = \  (_ :: ()) ->
     []

-- RecordPatternBinding ----------------------------------------
-- wrapper
data Inh_RecordPatternBinding  = Inh_RecordPatternBinding {  }
data Syn_RecordPatternBinding  = Syn_RecordPatternBinding { text_Syn_RecordPatternBinding :: (Doc) }
{-# INLINABLE wrap_RecordPatternBinding #-}
wrap_RecordPatternBinding :: T_RecordPatternBinding  -> Inh_RecordPatternBinding  -> (Syn_RecordPatternBinding )
wrap_RecordPatternBinding (T_RecordPatternBinding act) (Inh_RecordPatternBinding ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg142 = T_RecordPatternBinding_vIn142 
        (T_RecordPatternBinding_vOut142 _lhsOtext) <- return (inv_RecordPatternBinding_s143 sem arg142)
        return (Syn_RecordPatternBinding _lhsOtext)
   )

-- cata
{-# NOINLINE sem_RecordPatternBinding #-}
sem_RecordPatternBinding :: RecordPatternBinding  -> T_RecordPatternBinding 
sem_RecordPatternBinding ( RecordPatternBinding_RecordPatternBinding range_ name_ pattern_ ) = sem_RecordPatternBinding_RecordPatternBinding ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Pattern pattern_ )

-- semantic domain
newtype T_RecordPatternBinding  = T_RecordPatternBinding {
                                                         attach_T_RecordPatternBinding :: Identity (T_RecordPatternBinding_s143 )
                                                         }
newtype T_RecordPatternBinding_s143  = C_RecordPatternBinding_s143 {
                                                                   inv_RecordPatternBinding_s143 :: (T_RecordPatternBinding_v142 )
                                                                   }
data T_RecordPatternBinding_s144  = C_RecordPatternBinding_s144
type T_RecordPatternBinding_v142  = (T_RecordPatternBinding_vIn142 ) -> (T_RecordPatternBinding_vOut142 )
data T_RecordPatternBinding_vIn142  = T_RecordPatternBinding_vIn142 
data T_RecordPatternBinding_vOut142  = T_RecordPatternBinding_vOut142 (Doc)
{-# NOINLINE sem_RecordPatternBinding_RecordPatternBinding #-}
sem_RecordPatternBinding_RecordPatternBinding :: T_Range  -> T_Name  -> T_Pattern  -> T_RecordPatternBinding 
sem_RecordPatternBinding_RecordPatternBinding arg_range_ arg_name_ arg_pattern_ = T_RecordPatternBinding (return st143) where
   {-# NOINLINE st143 #-}
   st143 = let
      v142 :: T_RecordPatternBinding_v142 
      v142 = \ (T_RecordPatternBinding_vIn142 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _text = rule273  ()
         _lhsOtext :: Doc
         _lhsOtext = rule274 _text
         __result_ = T_RecordPatternBinding_vOut142 _lhsOtext
         in __result_ )
     in C_RecordPatternBinding_s143 v142
   {-# INLINE rule273 #-}
   rule273 = \  (_ :: ()) ->
                                        text "{- !!! record pattern binding -}"
   {-# INLINE rule274 #-}
   rule274 = \ _text ->
     _text

-- RecordPatternBindings ---------------------------------------
-- wrapper
data Inh_RecordPatternBindings  = Inh_RecordPatternBindings {  }
data Syn_RecordPatternBindings  = Syn_RecordPatternBindings { text_Syn_RecordPatternBindings :: ( [       Doc ] ) }
{-# INLINABLE wrap_RecordPatternBindings #-}
wrap_RecordPatternBindings :: T_RecordPatternBindings  -> Inh_RecordPatternBindings  -> (Syn_RecordPatternBindings )
wrap_RecordPatternBindings (T_RecordPatternBindings act) (Inh_RecordPatternBindings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg145 = T_RecordPatternBindings_vIn145 
        (T_RecordPatternBindings_vOut145 _lhsOtext) <- return (inv_RecordPatternBindings_s146 sem arg145)
        return (Syn_RecordPatternBindings _lhsOtext)
   )

-- cata
{-# NOINLINE sem_RecordPatternBindings #-}
sem_RecordPatternBindings :: RecordPatternBindings  -> T_RecordPatternBindings 
sem_RecordPatternBindings list = Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list)

-- semantic domain
newtype T_RecordPatternBindings  = T_RecordPatternBindings {
                                                           attach_T_RecordPatternBindings :: Identity (T_RecordPatternBindings_s146 )
                                                           }
newtype T_RecordPatternBindings_s146  = C_RecordPatternBindings_s146 {
                                                                     inv_RecordPatternBindings_s146 :: (T_RecordPatternBindings_v145 )
                                                                     }
data T_RecordPatternBindings_s147  = C_RecordPatternBindings_s147
type T_RecordPatternBindings_v145  = (T_RecordPatternBindings_vIn145 ) -> (T_RecordPatternBindings_vOut145 )
data T_RecordPatternBindings_vIn145  = T_RecordPatternBindings_vIn145 
data T_RecordPatternBindings_vOut145  = T_RecordPatternBindings_vOut145 ( [       Doc ] )
{-# NOINLINE sem_RecordPatternBindings_Cons #-}
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding  -> T_RecordPatternBindings  -> T_RecordPatternBindings 
sem_RecordPatternBindings_Cons arg_hd_ arg_tl_ = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 ) -> ( let
         _hdX143 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBinding (arg_hd_))
         _tlX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_tl_))
         (T_RecordPatternBinding_vOut142 _hdItext) = inv_RecordPatternBinding_s143 _hdX143 (T_RecordPatternBinding_vIn142 )
         (T_RecordPatternBindings_vOut145 _tlItext) = inv_RecordPatternBindings_s146 _tlX146 (T_RecordPatternBindings_vIn145 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule275 _hdItext _tlItext
         __result_ = T_RecordPatternBindings_vOut145 _lhsOtext
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule275 #-}
   rule275 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_RecordPatternBindings_Nil #-}
sem_RecordPatternBindings_Nil ::  T_RecordPatternBindings 
sem_RecordPatternBindings_Nil  = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule276  ()
         __result_ = T_RecordPatternBindings_vOut145 _lhsOtext
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule276 #-}
   rule276 = \  (_ :: ()) ->
     []

-- RightHandSide -----------------------------------------------
-- wrapper
data Inh_RightHandSide  = Inh_RightHandSide {  }
data Syn_RightHandSide  = Syn_RightHandSide { text_Syn_RightHandSide :: ( Doc        -> Doc  ) }
{-# INLINABLE wrap_RightHandSide #-}
wrap_RightHandSide :: T_RightHandSide  -> Inh_RightHandSide  -> (Syn_RightHandSide )
wrap_RightHandSide (T_RightHandSide act) (Inh_RightHandSide ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg148 = T_RightHandSide_vIn148 
        (T_RightHandSide_vOut148 _lhsOtext) <- return (inv_RightHandSide_s149 sem arg148)
        return (Syn_RightHandSide _lhsOtext)
   )

-- cata
{-# NOINLINE sem_RightHandSide #-}
sem_RightHandSide :: RightHandSide  -> T_RightHandSide 
sem_RightHandSide ( RightHandSide_Expression range_ expression_ where_ ) = sem_RightHandSide_Expression ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_MaybeDeclarations where_ )
sem_RightHandSide ( RightHandSide_Guarded range_ guardedexpressions_ where_ ) = sem_RightHandSide_Guarded ( sem_Range range_ ) ( sem_GuardedExpressions guardedexpressions_ ) ( sem_MaybeDeclarations where_ )

-- semantic domain
newtype T_RightHandSide  = T_RightHandSide {
                                           attach_T_RightHandSide :: Identity (T_RightHandSide_s149 )
                                           }
newtype T_RightHandSide_s149  = C_RightHandSide_s149 {
                                                     inv_RightHandSide_s149 :: (T_RightHandSide_v148 )
                                                     }
data T_RightHandSide_s150  = C_RightHandSide_s150
type T_RightHandSide_v148  = (T_RightHandSide_vIn148 ) -> (T_RightHandSide_vOut148 )
data T_RightHandSide_vIn148  = T_RightHandSide_vIn148 
data T_RightHandSide_vOut148  = T_RightHandSide_vOut148 ( Doc        -> Doc  )
{-# NOINLINE sem_RightHandSide_Expression #-}
sem_RightHandSide_Expression :: T_Range  -> T_Expression  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Expression arg_range_ arg_expression_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         (T_MaybeDeclarations_vOut88 _whereItext) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 )
         _text = rule277 _justText
         _justText = rule278 _expressionItext _whereItext
         _lhsOtext ::  Doc        -> Doc  
         _lhsOtext = rule279 _text
         __result_ = T_RightHandSide_vOut148 _lhsOtext
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule277 #-}
   rule277 = \ _justText ->
                                    \assign       -> assign <$> _justText
   {-# INLINE rule278 #-}
   rule278 = \ ((_expressionItext) :: Doc) ((_whereItext) ::  Maybe [       Doc ] ) ->
                      indent 4
                          (  _expressionItext
                          <> maybe
                                 empty
                                 (\ds -> PPrint.empty <$> text "where" <$> indent 4 (vcat ds))
                                 _whereItext
                          )
   {-# INLINE rule279 #-}
   rule279 = \ _text ->
     _text
{-# NOINLINE sem_RightHandSide_Guarded #-}
sem_RightHandSide_Guarded :: T_Range  -> T_GuardedExpressions  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Guarded arg_range_ arg_guardedexpressions_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardedexpressionsX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_guardedexpressions_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_GuardedExpressions_vOut64 _guardedexpressionsItext) = inv_GuardedExpressions_s65 _guardedexpressionsX65 (T_GuardedExpressions_vIn64 )
         (T_MaybeDeclarations_vOut88 _whereItext) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 )
         _text = rule280 _guardedexpressionsItext _whereItext
         _lhsOtext ::  Doc        -> Doc  
         _lhsOtext = rule281 _text
         __result_ = T_RightHandSide_vOut148 _lhsOtext
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule280 #-}
   rule280 = \ ((_guardedexpressionsItext) ::  [        Doc -> Doc  ] ) ((_whereItext) ::  Maybe [       Doc ] ) ->
                  \assign ->
                      (   PPrint.empty
                      <$> vsep
                             (zipWith (\f x -> indent 4 (f x)) _guardedexpressionsItext (repeat assign))
                      <>  maybe
                             empty
                             (\ds -> PPrint.empty <$> indent 4 (text "where" <$> indent 4 (vcat ds)))
                             _whereItext
                      )
   {-# INLINE rule281 #-}
   rule281 = \ _text ->
     _text

-- SimpleType --------------------------------------------------
-- wrapper
data Inh_SimpleType  = Inh_SimpleType {  }
data Syn_SimpleType  = Syn_SimpleType { text_Syn_SimpleType :: (Doc) }
{-# INLINABLE wrap_SimpleType #-}
wrap_SimpleType :: T_SimpleType  -> Inh_SimpleType  -> (Syn_SimpleType )
wrap_SimpleType (T_SimpleType act) (Inh_SimpleType ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg151 = T_SimpleType_vIn151 
        (T_SimpleType_vOut151 _lhsOtext) <- return (inv_SimpleType_s152 sem arg151)
        return (Syn_SimpleType _lhsOtext)
   )

-- cata
{-# INLINE sem_SimpleType #-}
sem_SimpleType :: SimpleType  -> T_SimpleType 
sem_SimpleType ( SimpleType_SimpleType range_ name_ typevariables_ ) = sem_SimpleType_SimpleType ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Names typevariables_ )

-- semantic domain
newtype T_SimpleType  = T_SimpleType {
                                     attach_T_SimpleType :: Identity (T_SimpleType_s152 )
                                     }
newtype T_SimpleType_s152  = C_SimpleType_s152 {
                                               inv_SimpleType_s152 :: (T_SimpleType_v151 )
                                               }
data T_SimpleType_s153  = C_SimpleType_s153
type T_SimpleType_v151  = (T_SimpleType_vIn151 ) -> (T_SimpleType_vOut151 )
data T_SimpleType_vIn151  = T_SimpleType_vIn151 
data T_SimpleType_vOut151  = T_SimpleType_vOut151 (Doc)
{-# NOINLINE sem_SimpleType_SimpleType #-}
sem_SimpleType_SimpleType :: T_Range  -> T_Name  -> T_Names  -> T_SimpleType 
sem_SimpleType_SimpleType arg_range_ arg_name_ arg_typevariables_ = T_SimpleType (return st152) where
   {-# NOINLINE st152 #-}
   st152 = let
      v151 :: T_SimpleType_v151 
      v151 = \ (T_SimpleType_vIn151 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Names_vOut115 _typevariablesIisIdentifier _typevariablesIisOperator _typevariablesIisSpecial _typevariablesItext) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         _text = rule282 _nameItext _typevariablesItext
         _lhsOtext :: Doc
         _lhsOtext = rule283 _text
         __result_ = T_SimpleType_vOut151 _lhsOtext
         in __result_ )
     in C_SimpleType_s152 v151
   {-# INLINE rule282 #-}
   rule282 = \ ((_nameItext) :: Doc) ((_typevariablesItext) ::  [       Doc ] ) ->
                                      foldl (<+>) _nameItext _typevariablesItext
   {-# INLINE rule283 #-}
   rule283 = \ _text ->
     _text

-- Statement ---------------------------------------------------
-- wrapper
data Inh_Statement  = Inh_Statement {  }
data Syn_Statement  = Syn_Statement { text_Syn_Statement :: (Doc) }
{-# INLINABLE wrap_Statement #-}
wrap_Statement :: T_Statement  -> Inh_Statement  -> (Syn_Statement )
wrap_Statement (T_Statement act) (Inh_Statement ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg154 = T_Statement_vIn154 
        (T_Statement_vOut154 _lhsOtext) <- return (inv_Statement_s155 sem arg154)
        return (Syn_Statement _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Statement #-}
sem_Statement :: Statement  -> T_Statement 
sem_Statement ( Statement_Expression range_ expression_ ) = sem_Statement_Expression ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Statement ( Statement_Let range_ declarations_ ) = sem_Statement_Let ( sem_Range range_ ) ( sem_Declarations declarations_ )
sem_Statement ( Statement_Generator range_ pattern_ expression_ ) = sem_Statement_Generator ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_Expression expression_ )
sem_Statement ( Statement_Empty range_ ) = sem_Statement_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Statement  = T_Statement {
                                   attach_T_Statement :: Identity (T_Statement_s155 )
                                   }
newtype T_Statement_s155  = C_Statement_s155 {
                                             inv_Statement_s155 :: (T_Statement_v154 )
                                             }
data T_Statement_s156  = C_Statement_s156
type T_Statement_v154  = (T_Statement_vIn154 ) -> (T_Statement_vOut154 )
data T_Statement_vIn154  = T_Statement_vIn154 
data T_Statement_vOut154  = T_Statement_vOut154 (Doc)
{-# NOINLINE sem_Statement_Expression #-}
sem_Statement_Expression :: T_Range  -> T_Expression  -> T_Statement 
sem_Statement_Expression arg_range_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule284 _expressionItext
         _lhsOtext :: Doc
         _lhsOtext = rule285 _text
         __result_ = T_Statement_vOut154 _lhsOtext
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule284 #-}
   rule284 = \ ((_expressionItext) :: Doc) ->
                                       _expressionItext
   {-# INLINE rule285 #-}
   rule285 = \ _text ->
     _text
{-# NOINLINE sem_Statement_Let #-}
sem_Statement_Let :: T_Range  -> T_Declarations  -> T_Statement 
sem_Statement_Let arg_range_ arg_declarations_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsItext) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 )
         _text = rule286 _declarationsItext
         _lhsOtext :: Doc
         _lhsOtext = rule287 _text
         __result_ = T_Statement_vOut154 _lhsOtext
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule286 #-}
   rule286 = \ ((_declarationsItext) ::  [       Doc ] ) ->
                                       text "let" <$> (indent 4 $ vcat _declarationsItext)
   {-# INLINE rule287 #-}
   rule287 = \ _text ->
     _text
{-# NOINLINE sem_Statement_Generator #-}
sem_Statement_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Statement 
sem_Statement_Generator arg_range_ arg_pattern_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternItext) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_Expression_vOut40 _expressionItext) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 )
         _text = rule288 _expressionItext _patternItext
         _lhsOtext :: Doc
         _lhsOtext = rule289 _text
         __result_ = T_Statement_vOut154 _lhsOtext
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule288 #-}
   rule288 = \ ((_expressionItext) :: Doc) ((_patternItext) :: Doc) ->
                                       _patternItext <+> text "<-" <+> _expressionItext
   {-# INLINE rule289 #-}
   rule289 = \ _text ->
     _text
{-# NOINLINE sem_Statement_Empty #-}
sem_Statement_Empty :: T_Range  -> T_Statement 
sem_Statement_Empty arg_range_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _text = rule290  ()
         _lhsOtext :: Doc
         _lhsOtext = rule291 _text
         __result_ = T_Statement_vOut154 _lhsOtext
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule290 #-}
   rule290 = \  (_ :: ()) ->
                                       empty
   {-# INLINE rule291 #-}
   rule291 = \ _text ->
     _text

-- Statements --------------------------------------------------
-- wrapper
data Inh_Statements  = Inh_Statements {  }
data Syn_Statements  = Syn_Statements { text_Syn_Statements :: ( [       Doc ] ) }
{-# INLINABLE wrap_Statements #-}
wrap_Statements :: T_Statements  -> Inh_Statements  -> (Syn_Statements )
wrap_Statements (T_Statements act) (Inh_Statements ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg157 = T_Statements_vIn157 
        (T_Statements_vOut157 _lhsOtext) <- return (inv_Statements_s158 sem arg157)
        return (Syn_Statements _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Statements #-}
sem_Statements :: Statements  -> T_Statements 
sem_Statements list = Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list)

-- semantic domain
newtype T_Statements  = T_Statements {
                                     attach_T_Statements :: Identity (T_Statements_s158 )
                                     }
newtype T_Statements_s158  = C_Statements_s158 {
                                               inv_Statements_s158 :: (T_Statements_v157 )
                                               }
data T_Statements_s159  = C_Statements_s159
type T_Statements_v157  = (T_Statements_vIn157 ) -> (T_Statements_vOut157 )
data T_Statements_vIn157  = T_Statements_vIn157 
data T_Statements_vOut157  = T_Statements_vOut157 ( [       Doc ] )
{-# NOINLINE sem_Statements_Cons #-}
sem_Statements_Cons :: T_Statement  -> T_Statements  -> T_Statements 
sem_Statements_Cons arg_hd_ arg_tl_ = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 ) -> ( let
         _hdX155 = Control.Monad.Identity.runIdentity (attach_T_Statement (arg_hd_))
         _tlX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_tl_))
         (T_Statement_vOut154 _hdItext) = inv_Statement_s155 _hdX155 (T_Statement_vIn154 )
         (T_Statements_vOut157 _tlItext) = inv_Statements_s158 _tlX158 (T_Statements_vIn157 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule292 _hdItext _tlItext
         __result_ = T_Statements_vOut157 _lhsOtext
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule292 #-}
   rule292 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Statements_Nil #-}
sem_Statements_Nil ::  T_Statements 
sem_Statements_Nil  = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule293  ()
         __result_ = T_Statements_vOut157 _lhsOtext
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule293 #-}
   rule293 = \  (_ :: ()) ->
     []

-- Strings -----------------------------------------------------
-- wrapper
data Inh_Strings  = Inh_Strings {  }
data Syn_Strings  = Syn_Strings { text_Syn_Strings :: ( [       Doc ] ) }
{-# INLINABLE wrap_Strings #-}
wrap_Strings :: T_Strings  -> Inh_Strings  -> (Syn_Strings )
wrap_Strings (T_Strings act) (Inh_Strings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg160 = T_Strings_vIn160 
        (T_Strings_vOut160 _lhsOtext) <- return (inv_Strings_s161 sem arg160)
        return (Syn_Strings _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Strings #-}
sem_Strings :: Strings  -> T_Strings 
sem_Strings list = Prelude.foldr sem_Strings_Cons sem_Strings_Nil list

-- semantic domain
newtype T_Strings  = T_Strings {
                               attach_T_Strings :: Identity (T_Strings_s161 )
                               }
newtype T_Strings_s161  = C_Strings_s161 {
                                         inv_Strings_s161 :: (T_Strings_v160 )
                                         }
data T_Strings_s162  = C_Strings_s162
type T_Strings_v160  = (T_Strings_vIn160 ) -> (T_Strings_vOut160 )
data T_Strings_vIn160  = T_Strings_vIn160 
data T_Strings_vOut160  = T_Strings_vOut160 ( [       Doc ] )
{-# NOINLINE sem_Strings_Cons #-}
sem_Strings_Cons :: (String) -> T_Strings  -> T_Strings 
sem_Strings_Cons _ arg_tl_ = T_Strings (return st161) where
   {-# NOINLINE st161 #-}
   st161 = let
      v160 :: T_Strings_v160 
      v160 = \ (T_Strings_vIn160 ) -> ( let
         _tlX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_tl_))
         (T_Strings_vOut160 _tlItext) = inv_Strings_s161 _tlX161 (T_Strings_vIn160 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule294 _tlItext
         __result_ = T_Strings_vOut160 _lhsOtext
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule294 #-}
   rule294 = \ ((_tlItext) ::  [       Doc ] ) ->
     _tlItext
{-# NOINLINE sem_Strings_Nil #-}
sem_Strings_Nil ::  T_Strings 
sem_Strings_Nil  = T_Strings (return st161) where
   {-# NOINLINE st161 #-}
   st161 = let
      v160 :: T_Strings_v160 
      v160 = \ (T_Strings_vIn160 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule295  ()
         __result_ = T_Strings_vOut160 _lhsOtext
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule295 #-}
   rule295 = \  (_ :: ()) ->
     []

-- Type --------------------------------------------------------
-- wrapper
data Inh_Type  = Inh_Type {  }
data Syn_Type  = Syn_Type { text_Syn_Type :: (Doc) }
{-# INLINABLE wrap_Type #-}
wrap_Type :: T_Type  -> Inh_Type  -> (Syn_Type )
wrap_Type (T_Type act) (Inh_Type ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg163 = T_Type_vIn163 
        (T_Type_vOut163 _lhsOtext) <- return (inv_Type_s164 sem arg163)
        return (Syn_Type _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Type #-}
sem_Type :: Type  -> T_Type 
sem_Type ( Type_Application range_ prefix_ function_ arguments_ ) = sem_Type_Application ( sem_Range range_ ) prefix_ ( sem_Type function_ ) ( sem_Types arguments_ )
sem_Type ( Type_Variable range_ name_ ) = sem_Type_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Type ( Type_Constructor range_ name_ ) = sem_Type_Constructor ( sem_Range range_ ) ( sem_Name name_ )
sem_Type ( Type_Qualified range_ context_ type_ ) = sem_Type_Qualified ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_Type type_ )
sem_Type ( Type_Forall range_ typevariables_ type_ ) = sem_Type_Forall ( sem_Range range_ ) ( sem_Names typevariables_ ) ( sem_Type type_ )
sem_Type ( Type_Exists range_ typevariables_ type_ ) = sem_Type_Exists ( sem_Range range_ ) ( sem_Names typevariables_ ) ( sem_Type type_ )
sem_Type ( Type_Parenthesized range_ type_ ) = sem_Type_Parenthesized ( sem_Range range_ ) ( sem_Type type_ )

-- semantic domain
newtype T_Type  = T_Type {
                         attach_T_Type :: Identity (T_Type_s164 )
                         }
newtype T_Type_s164  = C_Type_s164 {
                                   inv_Type_s164 :: (T_Type_v163 )
                                   }
data T_Type_s165  = C_Type_s165
type T_Type_v163  = (T_Type_vIn163 ) -> (T_Type_vOut163 )
data T_Type_vIn163  = T_Type_vIn163 
data T_Type_vOut163  = T_Type_vOut163 (Doc)
{-# NOINLINE sem_Type_Application #-}
sem_Type_Application :: T_Range  -> (Bool) -> T_Type  -> T_Types  -> T_Type 
sem_Type_Application arg_range_ arg_prefix_ arg_function_ arg_arguments_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_function_))
         _argumentsX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_arguments_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _functionItext) = inv_Type_s164 _functionX164 (T_Type_vIn163 )
         (T_Types_vOut166 _argumentsItext) = inv_Types_s167 _argumentsX167 (T_Types_vIn166 )
         _text = rule296 _argumentsItext _functionItext arg_prefix_
         _lhsOtext :: Doc
         _lhsOtext = rule297 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule296 #-}
   rule296 = \ ((_argumentsItext) ::  [       Doc ] ) ((_functionItext) :: Doc) prefix_ ->
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
   {-# INLINE rule297 #-}
   rule297 = \ _text ->
     _text
{-# NOINLINE sem_Type_Variable #-}
sem_Type_Variable :: T_Range  -> T_Name  -> T_Type 
sem_Type_Variable arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule298 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule299 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule298 #-}
   rule298 = \ ((_nameItext) :: Doc) ->
                                            _nameItext
   {-# INLINE rule299 #-}
   rule299 = \ _text ->
     _text
{-# NOINLINE sem_Type_Constructor #-}
sem_Type_Constructor :: T_Range  -> T_Name  -> T_Type 
sem_Type_Constructor arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIisIdentifier _nameIisOperator _nameIisSpecial _nameItext) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _text = rule300 _nameItext
         _lhsOtext :: Doc
         _lhsOtext = rule301 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule300 #-}
   rule300 = \ ((_nameItext) :: Doc) ->
                                            _nameItext
   {-# INLINE rule301 #-}
   rule301 = \ _text ->
     _text
{-# NOINLINE sem_Type_Qualified #-}
sem_Type_Qualified :: T_Range  -> T_ContextItems  -> T_Type  -> T_Type 
sem_Type_Qualified arg_range_ arg_context_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextItext) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule302 _contextItext _typeItext
         _lhsOtext :: Doc
         _lhsOtext = rule303 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule302 #-}
   rule302 = \ ((_contextItext) ::  [       Doc ] ) ((_typeItext) :: Doc) ->
                                            case _contextItext of
                                              [ct] -> ct <+> text "=>" <+> _typeItext
                                              cts -> parens (commas cts) <+> text "=>" <+> _typeItext
   {-# INLINE rule303 #-}
   rule303 = \ _text ->
     _text
{-# NOINLINE sem_Type_Forall #-}
sem_Type_Forall :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Forall arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesIisIdentifier _typevariablesIisOperator _typevariablesIisSpecial _typevariablesItext) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule304 _typeItext _typevariablesItext
         _lhsOtext :: Doc
         _lhsOtext = rule305 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule304 #-}
   rule304 = \ ((_typeItext) :: Doc) ((_typevariablesItext) ::  [       Doc ] ) ->
                                            foldl (<+>) (text "forall") _typevariablesItext <> text "." <> _typeItext
   {-# INLINE rule305 #-}
   rule305 = \ _text ->
     _text
{-# NOINLINE sem_Type_Exists #-}
sem_Type_Exists :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Exists arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesIisIdentifier _typevariablesIisOperator _typevariablesIisSpecial _typevariablesItext) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule306 _typeItext _typevariablesItext
         _lhsOtext :: Doc
         _lhsOtext = rule307 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule306 #-}
   rule306 = \ ((_typeItext) :: Doc) ((_typevariablesItext) ::  [       Doc ] ) ->
                                            foldl (<+>) (text "exists") _typevariablesItext <> text "." <> _typeItext
   {-# INLINE rule307 #-}
   rule307 = \ _text ->
     _text
{-# NOINLINE sem_Type_Parenthesized #-}
sem_Type_Parenthesized :: T_Range  -> T_Type  -> T_Type 
sem_Type_Parenthesized arg_range_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeItext) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeItext) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _text = rule308 _typeItext
         _lhsOtext :: Doc
         _lhsOtext = rule309 _text
         __result_ = T_Type_vOut163 _lhsOtext
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule308 #-}
   rule308 = \ ((_typeItext) :: Doc) ->
                                            parens _typeItext
   {-# INLINE rule309 #-}
   rule309 = \ _text ->
     _text

-- Types -------------------------------------------------------
-- wrapper
data Inh_Types  = Inh_Types {  }
data Syn_Types  = Syn_Types { text_Syn_Types :: ( [       Doc ] ) }
{-# INLINABLE wrap_Types #-}
wrap_Types :: T_Types  -> Inh_Types  -> (Syn_Types )
wrap_Types (T_Types act) (Inh_Types ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg166 = T_Types_vIn166 
        (T_Types_vOut166 _lhsOtext) <- return (inv_Types_s167 sem arg166)
        return (Syn_Types _lhsOtext)
   )

-- cata
{-# NOINLINE sem_Types #-}
sem_Types :: Types  -> T_Types 
sem_Types list = Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list)

-- semantic domain
newtype T_Types  = T_Types {
                           attach_T_Types :: Identity (T_Types_s167 )
                           }
newtype T_Types_s167  = C_Types_s167 {
                                     inv_Types_s167 :: (T_Types_v166 )
                                     }
data T_Types_s168  = C_Types_s168
type T_Types_v166  = (T_Types_vIn166 ) -> (T_Types_vOut166 )
data T_Types_vIn166  = T_Types_vIn166 
data T_Types_vOut166  = T_Types_vOut166 ( [       Doc ] )
{-# NOINLINE sem_Types_Cons #-}
sem_Types_Cons :: T_Type  -> T_Types  -> T_Types 
sem_Types_Cons arg_hd_ arg_tl_ = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 ) -> ( let
         _hdX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_hd_))
         _tlX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_tl_))
         (T_Type_vOut163 _hdItext) = inv_Type_s164 _hdX164 (T_Type_vIn163 )
         (T_Types_vOut166 _tlItext) = inv_Types_s167 _tlX167 (T_Types_vIn166 )
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule310 _hdItext _tlItext
         __result_ = T_Types_vOut166 _lhsOtext
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule310 #-}
   rule310 = \ ((_hdItext) :: Doc) ((_tlItext) ::  [       Doc ] ) ->
     _hdItext  :  _tlItext
{-# NOINLINE sem_Types_Nil #-}
sem_Types_Nil ::  T_Types 
sem_Types_Nil  = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 ) -> ( let
         _lhsOtext ::  [       Doc ] 
         _lhsOtext = rule311  ()
         __result_ = T_Types_vOut166 _lhsOtext
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule311 #-}
   rule311 = \  (_ :: ()) ->
     []
