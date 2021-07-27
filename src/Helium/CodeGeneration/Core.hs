{-| Module      :  Core
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core (desugarCore) where

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Helium.CodeGeneration.Core.TypeCheck
import Control.Monad (when)
import Text.PrettyPrint.Leijen (pretty)
import Helium.CodeGeneration.Iridium.FileCache

import Helium.CodeGeneration.Core.LetInline(coreLetInline)
import Helium.CodeGeneration.Core.LetSort(coreLetSort)
import Helium.CodeGeneration.Core.Normalize(coreNormalize)
import Helium.CodeGeneration.Core.Lift(coreLift)
import Helium.CodeGeneration.Core.ReduceThunks(coreReduceThunks)
import Helium.CodeGeneration.Core.Rename(coreRename)
import Helium.CodeGeneration.Core.RemoveAliases(coreRemoveAliases)
import Helium.CodeGeneration.Core.RemovePatterns(coreRemovePatterns)
import Helium.CodeGeneration.Core.Saturate(coreSaturate)
import Helium.CodeGeneration.Core.Strictness.Strictness(coreStrictness)

pipeline :: Int -> [(String, NameSupply -> CoreModule -> CoreModule)]
pipeline s =
  [ ("Rename", coreRename)
  , ("Saturate", coreSaturate)
  , ("LetSort", const coreLetSort)
  , ("LetInline 1", const coreLetInline)
  , ("RemovePatterns", const coreRemovePatterns)
  , ("LetInline 2", const coreLetInline)
  , ("Normalize", coreNormalize)
  , ("Strictness 1", coreStrictness s)
  , ("Strictness 2", strictnessExtraPass s)
  , ("RemoveAliases", const coreRemoveAliases)
  , ("ReduceThunks", const coreReduceThunks)
  , ("Lift", coreLift)
  , ("Strictness 3", coreStrictness s)
  ]

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: Int -> NameSupply -> CoreModule -> IO CoreModule
desugarCore s supply mod = do
  putStrLn $ showStrictness s ++ " strictness analysis selected..."
  desugar supply (pipeline s) mod

desugar :: NameSupply -> [(String, NameSupply -> CoreModule -> CoreModule)] -> CoreModule -> IO CoreModule
desugar supply ((passName, passFn) : passes) mod = do
  -- writeFile (stringFromId (moduleName mod) ++ "_" ++ passName ++ "_before.core") $ show $ pretty mod
  let (supply1, supply2) = splitNameSupply supply
  let mod' = passFn supply1 mod
  -- writeFile (stringFromId (moduleName mod) ++ "_" ++ passName ++ "_after.core") $ show $ pretty mod'
  checkModuleIO passName mod'
  desugar supply2 passes mod'
desugar _ [] mod = return mod

showStrictness :: Int -> String
showStrictness 5 = "Simple polyvariant"
showStrictness 4 = "Simple monovariant"
showStrictness 3 = "Advanced polyvariant"
showStrictness 2 = "Advanced monovariant"
showStrictness 1 = "Old"
showStrictness _ = "Monotype"

strictnessExtraPass :: Int -> (NameSupply -> CoreModule -> CoreModule)
strictnessExtraPass 1 = coreStrictness 1
strictnessExtraPass _ = \_ x -> x -- Type/effect system doesn't need second pass
