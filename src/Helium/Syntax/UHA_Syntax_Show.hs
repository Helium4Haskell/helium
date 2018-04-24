{-# LANGUAGE StandaloneDeriving #-}
module Helium.Syntax.UHA_Syntax_Show where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Range ()
import Helium.Syntax.UHA_Utils ()

deriving instance Show Module
deriving instance Show MaybeExports
deriving instance Show Export
deriving instance Show Body
deriving instance Show ImportDeclaration
deriving instance Show MaybeImportSpecification
deriving instance Show ImportSpecification
deriving instance Show Import
deriving instance Show MaybeDeclarations
deriving instance Show Declaration
deriving instance Show Fixity
deriving instance Show Type
deriving instance Show SimpleType
deriving instance Show ContextItem
deriving instance Show Constructor
deriving instance Show FieldDeclaration
deriving instance Show AnnotatedType
deriving instance Show MaybeExpression
deriving instance Show Expression
deriving instance Show Statement
deriving instance Show Qualifier
deriving instance Show Alternative
deriving instance Show GuardedExpression
deriving instance Show RecordExpressionBinding
deriving instance Show RecordPatternBinding
deriving instance Show FunctionBinding
deriving instance Show LeftHandSide
deriving instance Show RightHandSide
deriving instance Show Pattern
deriving instance Show Literal
deriving instance Show MaybeNames
deriving instance Show MaybeName
deriving instance Show MaybeInt
deriving instance Show Position
