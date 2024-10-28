--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Data
   ( module Helium.Lvm.Core.Module, LvmModule, LvmDecl
     -- constants
   , recHeader,recFooter           
   ) where

import Helium.Lvm.Core.Module
import Helium.Lvm.Instr.Data   ( Instr )

{--------------------------------------------------------------
  An LVM module
---------------------------------------------------------------}
type LvmModule  = Module [Instr]
type LvmDecl    = Decl [Instr]

{---------------------------------------------------------------
  Constants
---------------------------------------------------------------}
recHeader,recFooter :: Int
recHeader     = 0x1F4C564D
recFooter     = 0x1E4C564D
