-- | Module      :  Core
--    License     :  GPL
--
--    Maintainer  :  helium@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable
module Helium.CodeGeneration.Core
  ( desugarCore,
  )
where

import Control.Monad
import Helium.CodeGeneration.Core.LetInline (coreLetInline)
import Helium.CodeGeneration.Core.LetSort (coreLetSort)
import Helium.CodeGeneration.Core.Lift (coreLift)
import Helium.CodeGeneration.Core.Normalize (coreNormalize)
import Helium.CodeGeneration.Core.ReduceThunks (coreReduceThunks)
import Helium.CodeGeneration.Core.RemoveAliases (coreRemoveAliases)
import Helium.CodeGeneration.Core.Rename (coreRename)
import Helium.CodeGeneration.Core.Saturate (coreSaturate)
import Helium.CodeGeneration.Core.Strictness (coreStrictness)
import Helium.CodeGeneration.Core.TypeCheck
import Helium.Main.Args
import Lvm.Common.Id
import Lvm.Core.Expr
import Text.PrettyPrint.Leijen (pretty)

pipeline :: [(String, NameSupply -> CoreModule -> CoreModule)]
pipeline =
  [ ("01 Rename", coreRename),
    ("02 Saturate", coreSaturate),
    ("03 LetSort", const coreLetSort),
    ("04 LetInline 1", const coreLetInline),
    ("05 LetInline 2", const coreLetInline),
    ("06 Normalize", coreNormalize),
    ("07 Strictness 1", coreStrictness),
    ("08 Strictness 2", coreStrictness),
    ("09 RemoveAliases", const coreRemoveAliases),
    ("010 ReduceThunks", const coreReduceThunks),
    ("011 Lift", coreLift)
  ]

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: (Foldable m) => String -> NameSupply -> m Option -> CoreModule -> IO CoreModule
desugarCore fileName supply options cmod =
  if containsDOption Core `any` options
    then do
      desugar (printCore fileName) supply pipeline cmod
    else do
      desugar (noCore "") supply pipeline cmod

noCore :: String -> String -> CoreModule -> IO ()
noCore _ _ _ = return ()

printCore :: String -> String -> CoreModule -> IO ()
printCore fileName passName mod' = writeFile (fileName ++ "-" ++ passName ++ ".core") $ show $ pretty mod'

desugar :: (String -> CoreModule -> IO ()) -> NameSupply -> [(String, NameSupply -> CoreModule -> CoreModule)] -> CoreModule -> IO CoreModule
desugar dcore supply ((passName, passFn) : passes) cmod = do
  let (supply1, supply2) = splitNameSupply supply
  let mod' = passFn supply1 cmod
  checkModuleIO passName mod'
  dcore passName mod'
  desugar dcore supply2 passes mod'
desugar _ _ [] cmod = return cmod
