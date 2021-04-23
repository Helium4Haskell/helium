module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Data.List
import Data.Maybe
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Annotate
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

type CoreGroup = BindingGroup Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: NameSupply -> CoreModule -> CoreModule
coreStrictness supply mod = mod {moduleDecls = map resetDeclaration (others ++ values')}
  where
    mod' = annotateModule supply mod
    (values, others) = partition isValue (moduleDecls mod')
    env = typeEnvForModule mod{moduleDecls = others}
    groups = coreBindingGroups values
    (values', _) = foldl groupStrictness ([], env) groups
    
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
resetDeclaration decl@DeclValue{}       = decl{declType = fromJust $ declAnn decl, declAnn = Just $ declType decl}
resetDeclaration decl@DeclAbstract{}    = decl{declType = fromJust $ declAnn decl, declAnn = Just $ declType decl}
resetDeclaration decl@DeclCon{}         = decl{declType = typeRemoveAnnotations $ declType decl}
resetDeclaration decl@DeclTypeSynonym{} = decl{declType = typeRemoveAnnotations $ declType decl}
resetDeclaration decl                   = decl

isValue :: CoreDecl -> Bool
isValue DeclValue{} = True
isValue _           = False
