--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file
-- is distributed under the terms of the BSD3 License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Core.Module
   ( Module(..)
   , Decl(..)
   , Custom(..)
   , DeclKind(..)
   , Field(..)
   , TypeSynonymCoercions(..)
   , Arity
   , Tag
   , Access(..)
   , ExternName(..)
   , CallConv(..)
   , LinkConv(..)
   , globalNames
   , externNames
   , mapDecls
   , customDeclKind
   , customData
   , customTypeDecl
   , customClassDefinition
   , declKindFromDecl
   , shallowKindFromDecl
   , makeDeclKind
   , accessPublic
   , declaresValue
   , isDeclValue
   , isDeclAbstract
   , isDeclCon
   , isDeclExtern
   , isDeclGlobal
   , isDeclInfix
   , findInfixOrigin
   , typeSynonymTypeFromConstructorType
   )
where

import           Prelude                 hiding ( (<$>) )
import           Helium.Lvm.Common.Byte
import           Helium.Lvm.Common.Id
import           Helium.Lvm.Common.IdSet
import           Helium.Lvm.Core.PrettyId
import           Helium.Lvm.Core.Type
import           Helium.Lvm.Instr.Data
import           Data.List               ( intercalate )

import           Text.PrettyPrint.Leijen

{---------------------------------------------------------------
  A general LVM module structure parameterised by the
  type of values (Core expression, Asm expression or [Instr])
---------------------------------------------------------------}
data Module v
  = Module{ moduleName     :: Id
          , moduleMajorVer :: !Int
          , moduleMinorVer :: !Int
          , moduleImports  :: ![Id]
          , moduleDecls    :: ![Decl v]
          }


data Decl v
  = DeclValue     { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declType :: !Type, valueValue :: v, declCustoms :: ![Custom] }
  | DeclAbstract  { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declArity :: !Arity, declType :: !Type, declCustoms :: ![Custom] }
  | DeclCon       { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declType :: !Type, declFields :: ![Field], declCustoms :: [Custom] }
  | DeclExtern    { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declType :: !Type
                  , externType :: !String, externLink :: !LinkConv,   externCall  :: !CallConv
                  , externLib  :: !String, externName :: !ExternName, declCustoms :: ![Custom] }
  -- TODO: We should remove DeclCustom. I think it is only used for data types, so we should instead add
  -- a new constructor just for data types.
  | DeclCustom    { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declKind :: !DeclKind, declCustoms :: ![Custom] }
  | DeclTypeSynonym { declName :: Id, declAccess :: !Access, declModule :: !(Maybe Id), declSynonym :: !TypeSynonymCoercions, declType :: !Type, declCustoms :: ![Custom] }

newtype Field = Field { fieldName :: Id }

data TypeSynonymCoercions
  = TypeSynonymAlias   -- Implicit coercions in Haskell and Core
  | TypeSynonymNewtype -- Explicit coercions in Haskell, implicit in Core
-- Note that TypeSynonymNewtype can only be used for some newtypes. Recursive newtypes
-- can create infinite types when handling them as type synonyms. Hence we represent
-- those still as a data type. When compiling to LLVM we will still give them the same
-- representation. If possible we want to use a type synonym however, as that may
-- enable other optimizations. Hence we use this for all non-recursive newtypes.

data Custom
  = CustomInt   !Int
  | CustomBytes !Bytes
  | CustomName  Id
  | CustomLink  Id !DeclKind
  | CustomDecl  !DeclKind ![Custom]
  | CustomNothing

data DeclKind
  = DeclKindName
  | DeclKindKind
  | DeclKindBytes
  | DeclKindCode
  | DeclKindValue
  | DeclKindCon
  | DeclKindImport
  | DeclKindModule
  | DeclKindExtern
  | DeclKindExternType
  | DeclKindTypeSynonym
  | DeclKindCustom !Id
  deriving (Eq,Show)

data Access
  = Export !Id
  | Private
  deriving (Eq, Show)

accessPublic :: Access -> Bool
accessPublic (Export _) = True
accessPublic _ = False

-- externals
data ExternName = Plain    !String
                | Decorate !String
                | Ordinal  !Int
                deriving Show

data CallConv   = CallC | CallStd | CallInstr
                deriving (Show, Eq, Enum)

data LinkConv   = LinkStatic | LinkDynamic | LinkRuntime
                deriving (Show, Eq, Enum)

instance Ord DeclKind where
   compare k1 k2 = case (k1, k2) of
      (DeclKindCustom id1, DeclKindCustom id2) -> compare id1 id2
      (DeclKindCustom _, _) -> GT
      (_, DeclKindCustom _) -> LT
      _ -> compare (fromEnum k1) (fromEnum k2)

instance Enum DeclKind where
   toEnum i = case i of
      0  -> DeclKindName
      1  -> DeclKindKind
      2  -> DeclKindBytes
      3  -> DeclKindCode
      4  -> DeclKindValue
      5  -> DeclKindCon
      6  -> DeclKindImport
      7  -> DeclKindModule
      8  -> DeclKindExtern
      9  -> DeclKindExternType
      10 -> DeclKindTypeSynonym
      _  -> error ("Module.DeclKind.toEnum: unknown kind (" ++ show i ++ ")")

   fromEnum kind = case kind of
      DeclKindName        -> 0
      DeclKindKind        -> 1
      DeclKindBytes       -> 2
      DeclKindCode        -> 3
      DeclKindValue       -> 4
      DeclKindCon         -> 5
      DeclKindImport      -> 6
      DeclKindModule      -> 7
      DeclKindExtern      -> 8
      DeclKindExternType  -> 9
      DeclKindTypeSynonym -> 10
--      DeclKindCustom i  -> i
      _                   -> error "Module.DeclKind.fromEnum: unknown kind"

customDeclKind :: String -> DeclKind
customDeclKind = DeclKindCustom . idFromString

customData, customTypeDecl, customClassDefinition :: DeclKind
customData = customDeclKind "data"
customTypeDecl = customDeclKind "typedecl"
customClassDefinition = customDeclKind "ClassDefinition"

declKindFromDecl :: Decl a -> DeclKind
declKindFromDecl decl = case decl of
   DeclValue{}       -> DeclKindValue
   DeclAbstract{}    -> DeclKindValue
   DeclCon{}         -> DeclKindCon
   DeclExtern{}      -> DeclKindExtern
   DeclTypeSynonym{} -> DeclKindTypeSynonym
   DeclCustom{}      -> declKind decl
      -- _          -> error "Module.kindFromDecl: unknown declaration"

shallowKindFromDecl :: Decl a -> DeclKind
shallowKindFromDecl decl = case decl of
   DeclValue{}       -> DeclKindValue
   DeclAbstract{}    -> DeclKindValue
   DeclCon{}         -> DeclKindCon
   DeclExtern{}      -> DeclKindExtern
   DeclTypeSynonym{} -> DeclKindTypeSynonym
   DeclCustom{}      -> declKind decl

      -- _          -> error "Module.shallowKindFromDecl: unknown declaration"

----------------------------------------------------------------
-- Functors
----------------------------------------------------------------

instance Functor Module where
   fmap f m = m { moduleDecls = map (fmap f) (moduleDecls m) }

instance Functor Decl where
   fmap f decl = case decl of
      DeclValue    x ac md m  v  cs -> DeclValue x ac md m (f v) cs
      DeclAbstract x ac md ar tp cs -> DeclAbstract x ac md ar tp cs
      DeclCon x ac md t fs cs       -> DeclCon x ac md t fs cs
      DeclExtern x ac md ar et el ec elib en cs ->
         DeclExtern x ac md ar et el ec elib en cs
      DeclCustom x ac md k cs      -> DeclCustom x ac md k cs
      DeclTypeSynonym x ac md s t cs -> DeclTypeSynonym x ac md s t cs

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Pretty a => Pretty (Module a) where
   pretty (Module name _ _ imports decls) =
      text "module"
         <+> ppConId name
         <+> text "where"
         <$> text ("import(" ++ intercalate ", " (map show imports) ++ ")")
         <$> vcat (map (\decl -> pretty decl <> semi <> line) decls)
         <$> empty

instance Pretty a => Pretty (Decl a) where
   pretty decl = nest 2 $ case decl of
      DeclValue{} ->
         ppVarId (declName decl)
            <+> text "::"
            <+> pretty (declType decl)
            <+> ppAttrs decl
            <$> text "="
            <+> pretty (valueValue decl)
      DeclCon{} ->
         text "con"
            <+> ppConId (declName decl)
            <+> ppAttrs decl
            <$> text "::"
            <+> pretty (declType decl)
            <$> ppFields (declFields decl)
      DeclCustom{} ->
         text "custom"
            <+> pretty (declKind decl)
            <+> ppId (declName decl)
            <+> ppAttrs decl
      DeclExtern{} ->
         text "extern"
            <>  pretty (externLink decl)
            <>  pretty (externCall decl)
            <+> ppVarId (declName decl) -- <+> ppAttrs decl
            <+> ppExternName (externLib decl) (externName decl) -- <+> pretty (declArity decl)
            <+> ppExternType (externCall decl) (externType decl)
      DeclAbstract{} ->
         text "abstract"
            <+> ppVarId (declName decl)
            <+> ppAttrs decl
            <$> text " :: "
            <+> pretty (declType decl)
      DeclTypeSynonym name _ _ s tp cs ->
         let
            keyword = case s of
               TypeSynonymAlias -> text "type"
               TypeSynonymNewtype -> text "newtype"
         in
            keyword
               <+> ppVarId name
               <+> ppAttrs decl
               <+> text "="
               <+> pretty tp

instance Pretty LinkConv where
   pretty linkConv = case linkConv of
      LinkRuntime -> text " runtime"
      LinkDynamic -> text " dynamic"
      LinkStatic  -> empty

instance Pretty Field where
   pretty (Field name) = ppVarId name


instance Pretty CallConv where
   pretty callConv = case callConv of
      CallInstr -> text " instrcall"
      CallStd   -> text " stdcall"
      CallC     -> empty

ppExternName :: String -> ExternName -> Doc
ppExternName libName extName = case extName of
   Plain    name -> dquotes (ppQual name)
   Decorate name -> text "decorate" <+> ppQual name
   Ordinal  i    -> ppQual (show i)
 where
  ppQual name | null libName = ppVarId (idFromString name)
              | otherwise = ppQualId (idFromString libName) (idFromString name)

ppExternType :: CallConv -> String -> Doc
ppExternType callConv tp = text "::" <+> case callConv of
   CallInstr -> pretty tp
   _         -> ppString tp

ppNoImpAttrs :: Decl a -> Doc
ppNoImpAttrs = ppAttrsEx True

ppFields :: [Field] -> Doc
ppFields [] = empty
ppFields fs = encloseSep (text "<") (text ">") (text ", ") $ map pretty fs

ppAttrs :: Decl a -> Doc
ppAttrs = ppAttrsEx False

ppAttrsEx :: Bool -> Decl a -> Doc
ppAttrsEx hideImp decl =
   if null (declCustoms decl) && declModule decl == Nothing && not (accessPublic (declAccess decl))
      then empty
      else
         text ":"
         <+> ppAccess (declAccess decl)
         <+> ppModule (declModule decl)
         <+> pretty (declCustoms decl)

ppAccess :: Access -> Doc
ppAccess (Export name) = text "export" <+> ppId name
ppAccess Private = empty

ppModule :: Maybe Id -> Doc
ppModule Nothing = empty
ppModule (Just mod) = text "from" <+> ppId mod

instance Pretty Custom where
   pretty custom = case custom of
      CustomInt   i        -> pretty i
      CustomName  x        -> ppId x
      CustomBytes bs       -> dquotes (string (stringFromBytes bs))
      CustomLink x    kind -> text "custom" <+> pretty kind <+> ppId x
      CustomDecl kind cs   -> text "custom" <+> pretty kind <+> pretty cs
      CustomNothing        -> text "nothing"

   prettyList customs | null customs = empty
                      | otherwise    = list (map pretty customs)

instance Pretty DeclKind where
   pretty kind = case kind of
      DeclKindCustom x    -> ppId x
--         DeclKindName
--         DeclKindKind
--         DeclKindBytes
--         DeclKindCode
      DeclKindValue       -> ppId (idFromString "val")
      DeclKindCon         -> ppId (idFromString "con")
      DeclKindImport      -> ppId (idFromString "import")
      DeclKindModule      -> ppId (idFromString "module")
      DeclKindExtern      -> ppId (idFromString "extern")
      DeclKindTypeSynonym -> ppId (idFromString "type")
--         DeclKindExternType
      _                   -> pretty (fromEnum kind)

makeDeclKind :: Id -> DeclKind
makeDeclKind x = case stringFromId x of
   "val"    -> DeclKindValue
   "con"    -> DeclKindCon
   "import" -> DeclKindImport
   "module" -> DeclKindModule
   "extern" -> DeclKindExtern
   "type"   -> DeclKindTypeSynonym
   _        -> DeclKindCustom x

{---------------------------------------------------------------
  Utility functions
---------------------------------------------------------------}

declaresValue :: Decl a -> Bool
declaresValue decl = case decl of
   DeclValue{}       -> True
   DeclAbstract{}    -> True
   DeclCon{}         -> True
   DeclExtern{}      -> True
   DeclTypeSynonym{} -> False
   DeclCustom{}      -> isDeclInfix decl

isDeclInfix :: Decl a -> Bool
isDeclInfix decl@DeclCustom{} = case declKind decl of
   DeclKindCustom n -> n == idFromString "infix"
   _ -> False
isDeclInfix _ = False

findInfixOrigin :: [Decl a] -> Id -> Maybe Id
findInfixOrigin []     op = Nothing
findInfixOrigin (x:xs) op 
   | isDeclInfix x = if declAccess x == Export op
      then declModule x
      else findInfixOrigin xs op
   | otherwise = findInfixOrigin xs op

isDeclValue :: Decl a -> Bool
isDeclValue DeclValue{} = True
isDeclValue _           = False

isDeclAbstract :: Decl a -> Bool
isDeclAbstract DeclAbstract{} = True
isDeclAbstract _              = False

isDeclCon :: Decl a -> Bool
isDeclCon DeclCon{} = True
isDeclCon _         = False

isDeclExtern :: Decl a -> Bool
isDeclExtern DeclExtern{} = True
isDeclExtern _            = False

isDeclGlobal :: Decl a -> Bool
isDeclGlobal DeclValue{}    = True
isDeclGlobal DeclAbstract{} = True
isDeclGlobal DeclExtern{}   = True
isDeclGlobal _              = False

-- hasDeclKind kind decl           = (kind==declKindFromDecl decl)

{---------------------------------------------------------------
  More Utility functions
---------------------------------------------------------------}
globalNames :: Module v -> IdSet
globalNames m = setFromList
   [ declName d
   | d <- moduleDecls m
   , isDeclValue d || isDeclAbstract d || isDeclExtern d
   ]

externNames :: Module v -> IdSet
externNames m = setFromList [ declName d | d <- moduleDecls m, isDeclExtern d ]

mapDecls :: (Decl v -> Decl w) -> Module v -> Module w
mapDecls f m = m { moduleDecls = map f (moduleDecls m) }

-- Given the type of the constructor of a newtype,
-- returns the type of the field.
typeSynonymTypeFromConstructorType :: Type -> Type
typeSynonymTypeFromConstructorType (TForall q k tp) = TForall q k $ typeSynonymTypeFromConstructorType tp
typeSynonymTypeFromConstructorType (TAp (TAp (TCon TConFun) tArg) _) = typeNotStrict tArg
typeSynonymTypeFromConstructorType _ = error "typeSynonymTypeFromConstructorType: Expected a (possibly quantified) function type."
