module CoreToLvm ( coreToLvm ) where

import Standard   ( getLvmPath, searchPath )
import Id         ( newNameSupply, stringFromId )

import CoreRemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import CoreToAsm  ( coreToAsm )         -- enriched lambda expressions (Core) to Asm

import AsmToLvm   ( asmToLvm )          -- translate Asm to instructions
import AsmOptimize( asmOptimize )       -- optimize Asm (ie. inlining)

import LvmWrite   ( lvmWriteFile )
import LvmImport  ( lvmImport )

----------------------------------------------------------------
--
----------------------------------------------------------------
findModule paths id
  = searchPath paths ".lvm" (stringFromId id)

coreToLvm source mod =
    do
        path        <- getLvmPath
        let coreModule  = mod -- lvmImport (findModule path) mod
        nameSupply  <- newNameSupply
        
        let coremod = {- coreRemoveDead -} coreModule -- gebeurt al in Compile.hs
            asmmod  = coreToAsm nameSupply coremod
            asmopt  = asmOptimize asmmod
            lvmmod  = asmToLvm  asmopt
            
            target = source ++ ".lvm"
            
            showFile fname =
                map (\c -> if (c == '\\') then '/' else c) fname
                
        lvmWriteFile target lvmmod
