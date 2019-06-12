{-| Module      :  PhaseNormalize
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseNormalize(phaseNormalize) where

import Lvm.Core.Expr(CoreModule)
import Helium.Main.CompileUtils

import Lvm.Common.Id              (NameSupply, newNameSupply, splitNameSupplies)
import Lvm.Core.NoShadow          (coreRename)    -- rename local variables
import Lvm.Core.Saturate          (coreSaturate)  -- saturate constructors, instructions and externs
import Lvm.Core.Normalize         (coreNormalize) -- normalize core, ie. atomic arguments and lambda's at let bindings
import Lvm.Core.LetSort           (coreLetSort)   -- find smallest recursive let binding groups
import Lvm.Core.Lift              (coreLift)      -- lambda-lift, ie. make free variables arguments

import Helium.Normalization.Simplify(coreSimplify)

import Text.PrettyPrint.Leijen

phaseNormalize :: String -> CoreModule -> [Option] -> IO CoreModule
phaseNormalize fullName coreModule options = do
    enterNewPhase "Code normalization" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName
    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.beforenormalize") $ show . pretty $ coreModule

    nameSupply <- newNameSupply

    let (coreModule', dbgs) = if (DisableSimplify `elem` options)
                               then (normalizeWithoutSimplify nameSupply coreModule)
                               else (normalizeAndSimplify nameSupply coreModule)

    when (DumpCoreToFile `elem` options) $ do
        when (DisableSimplify `notElem` options) $ do
            writeFile (fullNameNoExt ++ ".core.duringnormalize") (unwords dbgs)
        writeFile (fullNameNoExt ++ ".core.afternormalize") $ show . pretty $ coreModule'

    return coreModule'

type DBGS a = (a, [String])

normalizeAndSimplify :: NameSupply -> CoreModule -> DBGS CoreModule
normalizeAndSimplify supply = coreSimplify . normalize supply

normalizeWithoutSimplify :: NameSupply -> CoreModule -> DBGS CoreModule
normalizeWithoutSimplify supply = (\cm -> (cm,[])) . normalize supply

normalize :: NameSupply -> CoreModule -> CoreModule
normalize supply =
    coreLift
  . coreLetSort
  . coreNormalize supply2
  . coreSaturate supply1
  . coreRename supply0
  where
    (supply0:supply1:supply2:_) = splitNameSupplies supply
