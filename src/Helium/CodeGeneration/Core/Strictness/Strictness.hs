module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Annotate
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

type CoreGroup = BindingGroup Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: Bool -> NameSupply -> CoreModule -> CoreModule
coreStrictness False = monovariantStrictness
coreStrictness True  = polyvariantStrictness

monovariantStrictness :: NameSupply -> CoreModule -> CoreModule
monovariantStrictness supply mod = mod'' {moduleDecls = map resetDeclaration (moduleDecls mod)}
  where
    mod' = annotateModule supply mod
    cs = analyseModule mod'
    cs' = solveConstraints cs
    mod'' = transformModule cs' mod'

polyvariantStrictness :: NameSupply -> CoreModule -> CoreModule
polyvariantStrictness supply mod = mod {moduleDecls = map resetDeclaration (others' ++ values'')}
  where
    (values, others) = partition isValue (moduleDecls mod)
    (supply1, supply2) = splitNameSupply supply
    values' = mapWithSupply annotateDeclaration supply1 values
    others' = mapWithSupply annotateDeclaration supply2 others
    env = typeEnvForModule mod{moduleDecls = others'}
    groups = coreBindingGroups values'
    (values'', _) = foldl groupStrictness ([], env) groups
    
groupStrictness :: ([CoreDecl], TypeEnvironment) -> CoreGroup -> ([CoreDecl], TypeEnvironment)
-- Single declaration
groupStrictness (b, env) (BindingNonRecursive d) = (b ++ [d'], env')
  where
    -- Analyse declaration
    cs = analyseDeclaration env d
    -- Solve constraints
    cs' = solveConstraints cs
    -- Apply transformations to declaration
    d' = transformDeclaration cs' d
    -- Add to type environment for next declarations
    env' = typeEnvAddGlobalValue (declName d') (declType d') env
-- Group of recursive declarations
groupStrictness (bs, env) (BindingRecursive ds) = (bs ++ ds'', env'')
  where
    -- Add all to type environment in annotated form
    env' = typeEnvAddGlobalValues (map (\d -> (declName d, declType d)) ds) env
    -- Analyse all declarations
    cs = map (analyseDeclaration env') ds
    -- Solve constraints
    cs' = solveConstraints (S.unions cs)
    -- Apply transformations to declarations
    ds'' = map (transformDeclaration cs') ds
    -- Add to type environment again but now with solved types
    env'' = typeEnvAddGlobalValues (map (\d -> (declName d, declType d)) ds'') env

-- Switch back original and annotated type, or remove annotations
resetDeclaration :: CoreDecl -> CoreDecl
resetDeclaration decl = resetDeclaration' decl
  where
      t = typeRemoveAnnotations $ declType decl
      c = if hasCustomAnn (declCustoms decl) then declCustoms decl else a : declCustoms decl
      a = CustomDecl (DeclKindCustom (idFromString "strictness")) [CustomType (declType decl)]
      resetDeclaration' :: CoreDecl -> CoreDecl
      resetDeclaration' DeclValue{}       = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclAbstract{}    = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclCon{}         = decl{declType = t}
      resetDeclaration' DeclTypeSynonym{} = decl{declType = t}
      resetDeclaration' _                 = decl

isValue :: CoreDecl -> Bool
isValue DeclValue{} = True
isValue _           = False
