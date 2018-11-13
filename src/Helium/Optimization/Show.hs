{-# LANGUAGE StandaloneDeriving #-}
module Helium.Optimization.Show where

import Lvm.Core.Module
import Lvm.Core.Expr

{-Module-}
deriving instance Show Access
deriving instance Show Custom

{-Expr-}
deriving instance Show Expr
deriving instance Show a => Show (Con a)
deriving instance Show Binds
deriving instance Show Bind
deriving instance Show Alt
deriving instance Show Pat
deriving instance Show Literal