module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Annotate
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.Instantiate
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module

type CoreGroup = BindingGroup Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: Bool -> NameSupply -> CoreModule -> CoreModule
coreStrictness False = monovariantStrictness
coreStrictness True  = polyvariantStrictness

monovariantStrictness :: NameSupply -> CoreModule -> CoreModule
monovariantStrictness supply mod = mod {moduleDecls = map resetDeclaration (moduleDecls mod'')}
  where
    -- Annotate module
    mod' = annotateModule supply mod
    -- Analyse module
    cs = analyseModule mod'
    -- Solve constraints
    cs' = solveConstraints cs
    -- Apply transformations
    mod'' = transformModule cs' False mod'

polyvariantStrictness :: NameSupply -> CoreModule -> CoreModule
polyvariantStrictness supply mod = mod {moduleDecls = map resetDeclaration (others' ++ values')}
  where
    (supply1, supply2) = splitNameSupply supply
    -- Annotate module
    mod' = annotateModule supply1 mod
    -- Split module in functions and others
    (values, others) = partition isDeclValue (moduleDecls mod')
    -- Instantiate others
    env1 = typeEnvForModule mod{moduleDecls = others}
    others' = mapWithSupply (instantiateDeclaration env1) supply2 others
    env2 = typeEnvForModule mod{moduleDecls = others'}
    -- Binding group analysis for functions
    groups = coreBindingGroups values
    (values', _) = foldl (groupStrictness supply2) ([], env2) groups
    
groupStrictness :: NameSupply -> ([CoreDecl], TypeEnvironment) -> CoreGroup -> ([CoreDecl], TypeEnvironment)
-- Single declaration
groupStrictness supply (b, env) (BindingNonRecursive d) = (b ++ [td], env')
  where
    -- Instantiate declaration
    id = instantiateDeclaration env supply d
    -- Analyse declaration
    cs = analyseDeclaration env id
    -- Solve constraints
    sc = solveConstraints cs
    -- Apply transformations
    td = transformDeclaration env sc True d
    -- Add to type environment for next declarations
    env' = typeEnvAddGlobalValue (declName td) (declType td) env
-- Group of recursive declarations
groupStrictness supply (bs, env) (BindingRecursive ds) = (bs ++ tds, env'')
  where
    -- Instantiate declarations
    ids = instantiateDeclarations env supply ds
    env' = typeEnvAddGlobalValues (map (\d -> (declName d, declType d)) ids) env
    -- Analyse declarations
    cs = map (analyseDeclaration env') ids
    -- Solve constraints
    sc = solveConstraints (S.unions cs)
    -- Apply transformations
    tds = map (transformDeclaration env' sc True) ds
    -- Add to type environment for next declarations
    env'' = typeEnvAddGlobalValues (map (\d -> (declName d, declType d)) tds) env

-- Switch back original and annotated type, or remove annotations
resetDeclaration :: CoreDecl -> CoreDecl
resetDeclaration decl = resetDeclaration' decl
  where
      t = typeRemoveAnnotations $ declType decl
      c = if not (any isCustomAnn (declCustoms decl)) then a : declCustoms decl else declCustoms decl
      a = CustomDecl (DeclKindCustom (idFromString "strictness")) [CustomType (declType decl)]
      resetDeclaration' :: CoreDecl -> CoreDecl
      resetDeclaration' DeclValue{}       = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclAbstract{}    = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclCon{}         = decl{declType = t}
      resetDeclaration' DeclTypeSynonym{} = decl{declType = t}
      resetDeclaration' _                 = decl
