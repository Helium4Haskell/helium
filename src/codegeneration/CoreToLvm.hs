module CoreToLvm ( coreToLvm ) where

import Id         ( newNameSupply )
import CoreToAsm  ( coreToAsm )         -- enriched lambda expressions (Core) to Asm
import AsmToLvm   ( asmToLvm )          -- translate Asm to instructions
import AsmOptimize( asmOptimize )       -- optimize Asm (ie. inlining)
import LvmWrite   ( lvmWriteFile )

coreToLvm source coremod = do
    nameSupply  <- newNameSupply

    -- coreRemoveDead gebeurt al in Compile.hs
    let asmmod  = coreToAsm nameSupply coremod
        asmopt  = asmOptimize asmmod
        lvmmod  = asmToLvm  asmopt
        target  = source ++ ".lvm"

    lvmWriteFile target lvmmod
