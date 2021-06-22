module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Annotate
import Helium.CodeGeneration.Core.Strictness.Data
import qualified Helium.CodeGeneration.Core.Strictness.Polyvariant as P
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

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
polyvariantStrictness supply mod = mod {moduleDecls = decls1 ++ map resetDeclaration others' ++ values'}
  where
    (supply1, supply2) = splitNameSupply supply
    -- Ignore declarations which have already been analysed
    (decls1, decls2) = partition (any isCustomAnn . declCustoms) $ moduleDecls mod
    -- Split module in functions and others (constructors, abstract, synonyms)
    (values, others) = partition isDeclValue decls2
    -- For declarations which have been annotated, set strictness type to declType
    decls1' = map setStrictnessType decls1
    -- Annotate others
    (others', is) = unzip $ mapWithSupply (P.annotateDeclaration (typeEnvForModule mod)) supply1 others
    -- Create starting environment
    env' = typeEnvForModule mod{moduleDecls = others' ++ decls1'}
    -- Binding group analysis for functions
    groups = coreBindingGroups values
    (values', _, _) = foldl (groupStrictness (unionSets is)) ([], env', supply2) groups
    
groupStrictness :: IdSet -> ([CoreDecl], TypeEnvironment, NameSupply) -> CoreGroup -> ([CoreDecl], TypeEnvironment, NameSupply)
-- Single declaration
groupStrictness is (b, env, supply) (BindingNonRecursive d) = (b ++ [d{valueValue = e', declCustoms = c}], env', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Analyse function
    Analysis e cs ae sc1 = P.analyseDeclaration env is supply1 d
    -- Solve constraints
    cs' = S.union cs $ annEnvToConstraints ae
    sc2 = solveConstraints cs'
    sc3 = mapMap (replaceVar sc2) sc1
    sc = unionMap sc2 sc3
    -- Transform expression using solved constraints
    e' = transformExpression sc e
    -- Get type, apply transformations and forallify
    t' = forallify True $ transformType sc True False $ typeOfCoreExpression env e
    -- Add strictness type to custom
    c = strictnessToCustom t' (declCustoms d)
    -- Add function to environment for next function
    env' = typeEnvAddGlobalValue (declName d) t' env
-- Group of recursive declarations
groupStrictness is (bs, env, supply) (BindingRecursive ds) = (bs ++ ds', env'', supply3)
  where
    (supply1, supply') = splitNameSupply supply
    (supply2, supply3) = splitNameSupply supply'
    -- Annotate type signatures and add them to the envorinment
    (ts, is2) = unzip $ mapWithSupply (\s d -> spread (declName d) (P.annotateType env s $ declType d)) supply1 ds
    env' = typeEnvAddGlobalValues ts env
    is3 = unionSet is $ unionSets is2
    -- Run analysis on all bodies, merge information with meet
    Analysis es cs ae sc1 = mergeAnalysis meet $ mapWithSupply (P.analyseDeclaration env' is3) supply2 ds
    -- Solve constraints
    cs' = S.union cs $ annEnvToConstraints ae
    sc2 = solveConstraints cs'
    sc3 = mapMap (replaceVar sc2) sc1
    sc = unionMap sc2 sc3
    -- Transform all expressions using solved constraints
    es' = map (transformExpression sc) es
    -- Get types from body, apply solved constraints and forallify
    ts' = map (forallify True . transformType sc True False . typeOfCoreExpression env') es
    -- Create new declarations with new values and strictness types
    ds' = map (\(d, v, t) -> d{valueValue = v, declCustoms = strictnessToCustom t (declCustoms d)}) (zip3 ds es' ts')
    -- Add types to environment for next functions
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds' ts')) env

-- Switch back original and annotated type, or remove annotations
resetDeclaration :: CoreDecl -> CoreDecl
resetDeclaration decl = resetDeclaration' decl
  where
      t = typeRemoveAnnotations $ declType decl
      c = strictnessToCustom (declType decl) (declCustoms decl)
      resetDeclaration' :: CoreDecl -> CoreDecl
      resetDeclaration' DeclValue{}       = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclAbstract{}    = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclCon{}         = decl{declType = t}
      resetDeclaration' DeclTypeSynonym{} = decl{declType = t}
      resetDeclaration' _                 = decl

setStrictnessType :: CoreDecl -> CoreDecl
setStrictnessType decl = decl{declType = t}
  where
    t = typeFromCustom $ declCustoms decl

strictnessToCustom :: Type -> [Custom] -> [Custom]
strictnessToCustom t c = CustomDecl (DeclKindCustom (idFromString "strictness")) [CustomType t] : c

spread :: a -> (b, c) -> ((a, b), c)
spread a (b, c) = ((a, b), c)
