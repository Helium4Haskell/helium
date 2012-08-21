{-| Module      :  CoreToLvm
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module CoreToLvm ( coreToLvm ) where

import Lvm.Common.Id         ( newNameSupply )
import Lvm.Core.CoreToAsm  ( coreToAsm )         -- enriched lambda expressions (Core) to Asm
import Lvm.Asm.AsmToLvm   ( asmToLvm )          -- translate Asm to instructions
import Lvm.Asm.AsmOptimize( asmOptimize )       -- optimize Asm (ie. inlining)
import Lvm.LvmWrite   ( lvmWriteFile )

coreToLvm source coremod = do
    nameSupply  <- newNameSupply

    -- coreRemoveDead gebeurt al in Compile.hs
    let asmmod  = coreToAsm nameSupply coremod
        asmopt  = asmOptimize asmmod
        lvmmod  = asmToLvm  asmopt
        target  = source ++ ".lvm"
   
    -- putDoc (lvmPretty lvmmod)
    lvmWriteFile target lvmmod
