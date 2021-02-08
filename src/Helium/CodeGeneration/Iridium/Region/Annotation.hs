module Helium.CodeGeneration.Iridium.Region.Annotation where

import Control.Applicative
import Data.Maybe
import Data.List

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Utils

newtype AnnotationVar = AnnotationVar { annotationVarIndex :: Int }
  deriving (Eq, Ord)

instance Show AnnotationVar where
  show (AnnotationVar idx) = 'ψ' : showSubscript idx

data Annotation
  -- f (fix g)
  -- We store a function to apply to the result of the fixpoint, to prevent the fixpoint being duplicated.
  = AFix !Annotation !Sort !Annotation

  | AFixEscape !Int !Sort !RegionSort !Annotation

  | AForall !Quantor !Annotation
  | ALam !Sort !RegionSort !LifetimeContext !Annotation

  | AInstantiate !Annotation !Type
  | AApp !Annotation !Annotation !RegionVars !LifetimeContext

  | ATuple ![Annotation]
  | AProject !Annotation !Int

  | AVar !AnnotationVar
  | ARelation !Relation
  | ATop !Sort
  | ABottom !Sort
  | AJoin !Annotation !Annotation
  deriving (Eq, Ord)

identity :: Sort -> Annotation
identity s = ALam s RegionSortUnit LifetimeContextAny $ AVar $ AnnotationVar 0

arelation :: Relation -> Annotation
arelation rel
  | relationIsEmpty rel = ABottom SortRelation
  | otherwise = ARelation rel

type Names = (QuantorNames, Env String, Env String) -- Type variable names, annotation variable names, region variable names

data Precedence = PrecLow | PrecApp | PrecHigh deriving (Eq, Ord)

showAnnotation :: Names -> Int -> Precedence -> Annotation -> ShowS
showAnnotation names indentation precedence annotation = case annotation of
  AFix f s g
    | isIdentity f -> parensMultiline PrecHigh $ \indentation' ->
      showString "fix {" . showSort' s . showString "}\r\n"
      . showIndentation indentation' . showAnnotation' indentation' PrecHigh g
    | otherwise ->
      showAnnotation' indentation PrecHigh (AApp f (AFix (identity s) s g) (RegionVarsTuple []) LifetimeContextAny)

  AFixEscape arity s rs f ->
    parensMultiline PrecHigh $ \indentation' ->
      showString "fix_escape {" . shows arity . showString "; " . showSort' s . showString "; " . showRegionSort quantorNames rs . showString "}\r\n"
      . showIndentation indentation' . showAnnotation' indentation' PrecHigh f

  AForall quantor a ->
    let
      quantorName = freshQuantorName quantorNames quantor
      names' = (quantorName : quantorNames, annotationNames, regionNames)
    in
      if isSimple a then
        parens PrecHigh $ showString "∀ " . showString quantorName . showString ". " . showAnnotation names' indentation PrecHigh a
      else
        parensMultiline PrecHigh $ \indentation' ->
          showString "∀ " . showString quantorName . showString "."
          . showString "\r\n" . showIndentation (indentation' + 1) . showAnnotation names' (indentation' + 1) PrecHigh a

  ALam s RegionSortUnit _ a ->
    let
      var = 'ψ' : showSubscript (envSize annotationNames)
      names' = (quantorNames, envPush var annotationNames, regionNames)
    in
      if isSimple a then
        parens PrecHigh $ showString "λ" . showString var . showString ": " . showSortLow' s . showString " -> " . showAnnotation names' indentation PrecHigh a
      else
        parensMultiline PrecHigh $ \indentation' ->
          showString "λ" . showString var . showString ": " . showSortLow' s . showString " ->\r\n"
          . showIndentation (indentation' + 1) . showAnnotation names' (indentation' + 1) PrecHigh a

  ALam s rs lc a ->
    let
      annotationVar = 'ψ' : showSubscript (envSize annotationNames)
      regionVars = map (\idx -> 'ρ' : showSubscript (envSize annotationNames) ++ "₋" ++ showSubscript idx) [0 .. regionSortSize rs - 1]
      names' = (quantorNames, envPush annotationVar annotationNames, foldl (flip envPush) regionNames regionVars)

      arguments = showString "λ[" . showString annotationVar . showString ": " . showSortLow' s . showString "; " . showRegionSortWithVariables quantorNames regionVars rs . showString "]" . shows lc
    in
      if isSimple a then
        parens PrecHigh $ arguments . showString " -> " . showAnnotation names' indentation PrecHigh a
      else
        parensMultiline PrecHigh $ \indentation' ->
          showString "λ" . arguments . showString " ->\r\n"
          . showIndentation (indentation' + 1) . showAnnotation names' (indentation' + 1) PrecHigh a

  AInstantiate a tp
    | isSimple annotation -> parens PrecApp $ showAnnotation' indentation PrecApp a . showString " { " . showType' tp . showString " }"
    | otherwise -> parensMultiline PrecApp $ \indentation' -> showAnnotation' indentation' PrecApp a . showString "\r\n" . showIndentation indentation' . showString "{ " . showType' tp . showString " }"

  AApp a1 a2 (RegionVarsTuple []) _
    | isSimple annotation -> parens PrecApp $ showAnnotation' indentation PrecApp a1 . showString " " . showAnnotation' indentation PrecLow a2
    | otherwise -> parensMultiline PrecApp $ \indentation' -> showAnnotation' indentation' PrecApp a1 . showString "\r\n" . showIndentation indentation' . showAnnotation' indentation PrecLow a2

  AApp a1 a2 vars lc
    | isSimple a1 && isSimple a2 -> parens PrecApp $ showAnnotation' indentation PrecApp a1 . showString " [" . showAnnotation' indentation PrecHigh a2 . showString "; " . showRegionVars vars . showString "]"
    | isSimple a2 -> parensMultiline PrecApp $ \indentation' ->
        showAnnotation' indentation' PrecApp a1
        . showString "\r\n" . showIndentation indentation'
        . showString "[" . showAnnotation' indentation' PrecHigh a2 . showString "; " . showRegionVars vars . showString "]" . shows lc
    | otherwise -> parensMultiline PrecApp $ \indentation' ->
        showAnnotation' indentation' PrecApp a1
        . showString "\r\n" . showIndentation indentation'
        . showString "[ " . showAnnotation' (indentation' + 1) PrecHigh a2
        . showString "\r\n" . showIndentation indentation'
        . showString "; " . showRegionVars vars
        . showString " ]" . shows lc

  ATuple as
    | isSimple annotation -> showString "(" . showsIntercalate (showAnnotation' indentation PrecHigh) ", " as . showString ")"
    | otherwise ->
      newline . showString "( "
      . showsIntercalate (showAnnotation' (indentation + 1) PrecHigh) (newline ", ") as . newline . showString ")"
  AProject a idx -> showAnnotation' indentation PrecLow a . showString "." . shows idx

  AVar var -> showAnnotationVar var
  ARelation relation -> showRelationWith showRegionVar relation
  ATop s -> parens PrecApp (showString "⊤ { " . showSort' s . showString " }")
  ABottom s -> parens PrecApp (showString "⊥ { " . showSort' s . showString " }")
  AJoin{}
    | isSimple annotation -> parens PrecHigh $ showsIntercalate (showAnnotation' indentation PrecApp) " ⊔ " $ gatherJoins annotation []
    | a:as <- gatherJoins annotation [] ->
      parensMultiline PrecHigh $ \indentation' ->
        showAnnotation' indentation' PrecApp a . newline . showString "⊔ "
        -- Note that we use indentation instead of indentation' here,
        -- to prevent double indentation if parentheses are needed.
        . showsIntercalate (showAnnotation' (indentation + 1) PrecApp) (newline "⊔ ") as
    | otherwise -> error "Impossible"

  where
    (quantorNames, annotationNames, regionNames) = names

    parens :: Precedence -> ShowS -> ShowS
    parens expected s
      | precedence >= expected = s
      | otherwise = showString "(" . s . showString ")"

    parensMultiline :: Precedence -> (Int -> ShowS) -> ShowS
    parensMultiline expected s
      | precedence >= expected = newline . s indentation
      | otherwise = 
        newline . showString "( "
        . s (indentation + 1)
        . newline . showString ")"

    newline = showString "\r\n" . showIndentation indentation

    showType' :: Type -> ShowS
    showType' = showString . showType quantorNames

    showSort' :: Sort -> ShowS
    showSort' = showSort quantorNames

    showSortLow' :: Sort -> ShowS
    showSortLow' = showSortLow quantorNames

    showAnnotation' = showAnnotation names

    showAnnotationVar :: AnnotationVar -> ShowS
    showAnnotationVar (AnnotationVar idx) = case envLookup idx annotationNames of
      Nothing -> showString $ 'ψ' : showSubscript (envSize annotationNames - idx - 1)
      Just s -> showString s

    showRegionVar :: RegionVar -> String
    showRegionVar RegionGlobal = show RegionGlobal
    showRegionVar RegionBottom = show RegionBottom
    showRegionVar (RegionLocal idx) = case envLookup idx regionNames of
      Nothing -> 'ρ' : showSubscript (envSize regionNames - idx - 1)
      Just s -> s

    showRegionVars :: RegionVars -> ShowS
    showRegionVars = showRegionVarsWith showRegionVar

    isSimple :: Annotation -> Bool
    isSimple = isSimple' 3

    isSimple' 0 _ = False
    isSimple' _ (AVar _) = True
    isSimple' k (ATuple as) = length as <= k && all (isSimple' $ k - 1) as
    isSimple' k (AApp a1 a2 _ _) = isSimple' k a1 && isSimple' (k - 1) a2
    isSimple' k (AProject a _) = isSimple' k a
    isSimple' k (AInstantiate a _) = isSimple' k a
    isSimple' _ (ARelation _) = True
    isSimple' _ _ = False

    gatherJoins :: Annotation -> [Annotation] -> [Annotation]
    gatherJoins (AJoin a1 a2) = gatherJoins a1 . gatherJoins a2
    gatherJoins a = (a :)

showIndentation :: Int -> ShowS
showIndentation 0 s = s
showIndentation i s = ' ' : ' ' : showIndentation (i - 1) s

isIdentity :: Annotation -> Bool
isIdentity (ALam _ RegionSortUnit _ (AVar (AnnotationVar 0))) = True
isIdentity _ = False
