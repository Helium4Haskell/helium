--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Instr.Data 
   ( Instr(..), Var(..), Con(..), Global(..), Alt(..), Pat(..)
   , Offset, Depth, Index, Tag, Arity
   , opcodeFromInstr, instrFromOpcode, instrFromName, nameFromInstr
   , isCATCH, strictResult
   ) where

import Prelude hiding ((<$>))
import Data.Char
import Data.Maybe
import Helium.Lvm.Common.Byte
import Helium.Lvm.Common.Id
import Text.PrettyPrint.Leijen

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

type Offset   = Int
type Depth    = Int
type Index    = Int
type Tag      = Int
type Arity    = Int

data Global = Global 
   { idFromGlobal :: !Id
   , indexFromGlobal :: Index
   , arityFromGlobal :: !Arity 
   }
 deriving Show

data Con = Con
   { idFromCon    :: !Id 
   , indexFromCon :: Index 
   , arityFromCon :: !Arity 
   , tagFromCon   :: !Tag
   }
 deriving Show

data Var = Var
   { idFromVar     :: !Id 
   , offsetFromVar :: !Offset 
   , depthFromVar  :: !Depth
   } 
 deriving Show

----------------------------------------------------------------
-- The instructions
----------------------------------------------------------------
data Pat      = PatCon !Con
              | PatInt !Int
              | PatTag !Tag !Arity
              | PatDefault
              deriving Show

data Alt      = Alt !Pat ![Instr]
              deriving Show

data Instr    =
              -- pseudo instructions
                VAR         !Id
              | PARAM       !Id
              | USE         !Id
              | NOP
              | ATOM        ![Instr]
              | INIT        ![Instr]


              -- structured instructions
              | CATCH       ![Instr]               -- for generating PUSHCATCH
              | EVAL        !Depth ![Instr]        -- for generating PUSHCONT
              | RESULT      ![Instr]               -- for generating SLIDE

              | MATCH       ![Alt]
              | MATCHCON    ![Alt]
              | SWITCHCON   ![Alt]
              | MATCHINT    ![Alt]

              -- push instructions
              | PUSHVAR     !Var
              | PUSHINT     !Int
              | PUSHBYTES   !Bytes !Index
              | PUSHFLOAT   !Double
              | PUSHCODE    !Global
              | PUSHCONT    !Offset
              | PUSHCATCH

              -- stack instructions
              | ARGCHK      !Arity
              | SLIDE       !Int !Int !Depth
              | STUB        !Var

              -- control
              | ENTER
              | RAISE
              | CALL        !Global

              | ENTERCODE   !Global
              | EVALVAR     !Var

              | RETURN
              | RETURNCON   !Con
              | RETURNINT   !Int

              -- applications
              | ALLOCAP     !Arity
              | PACKAP      !Var !Arity
              | PACKNAP     !Var !Arity
              | NEWAP       !Arity
              | NEWNAP      !Arity

              -- constructors
              | ALLOCCON    !Con
              | PACKCON     !Con !Var
              | NEWCON      !Con

              | ALLOC
              | NEW         !Arity
              | PACK        !Arity  !Var
              | UNPACK      !Arity
              | GETFIELD
              | SETFIELD
              | GETTAG
              | GETSIZE
              | UPDFIELD

              -- INT operations
              | ADDINT
              | SUBINT
              | MULINT
              | DIVINT
              | MODINT
              | QUOTINT
              | REMINT
              | ANDINT
              | XORINT
              | ORINT
              | SHRINT
              | SHLINT
              | SHRNAT
              | NEGINT

              | EQINT
              | NEINT
              | LTINT
              | GTINT
              | LEINT
              | GEINT
             
              -- FLOAT operations
              | ADDFLOAT
              | SUBFLOAT
              | MULFLOAT
              | DIVFLOAT
              | NEGFLOAT

              | EQFLOAT
              | NEFLOAT
              | LTFLOAT
              | GTFLOAT
              | LEFLOAT
              | GEFLOAT

              -- optimized VAR
              | PUSHVAR0
              | PUSHVAR1
              | PUSHVAR2
              | PUSHVAR3
              | PUSHVAR4

              | PUSHVARS2 !Var !Var

              -- optimized AP
              | NEWAP2
              | NEWAP3
              | NEWAP4

              | NEWNAP2
              | NEWNAP3
              | NEWNAP4

              -- optimized NEWCON
              | NEWCON0 !Con
              | NEWCON1 !Con
              | NEWCON2 !Con
              | NEWCON3 !Con

              | RETURNCON0 !Con
              deriving Show

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Pretty Instr where
   prettyList = align . vcat . map pretty
   pretty instr = 
      case instr of
      -- pseudo instructions
      VAR         x           -> text name <+> pretty x
      PARAM       x           -> text name <+> pretty x
      USE         x           -> text name <+> pretty x
      NOP                     -> text name
      
      ATOM        is          -> nest 2 (text name <$> pretty is)
      INIT        is          -> nest 2 (text name <$> pretty is)

    -- structured instructions
      CATCH instrs            -> nest 2 (text name <$> pretty instrs)
      EVAL d instrs           -> nest 2 (text name <+> pretty d <$> pretty instrs)
      RESULT instrs           -> nest 2 (text name <$> pretty instrs)

      SWITCHCON alts          -> nest 2 (text name <$> pretty alts)
      MATCHCON alts           -> nest 2 (text name <$> pretty alts)
      MATCHINT alts           -> nest 2 (text name <$> pretty alts)
      MATCH alts              -> nest 2 (text name <$> pretty alts)


    -- push instructions
      PUSHVAR     var         -> text name <+> pretty var
      PUSHINT     n           -> text name <+> pretty n
      PUSHBYTES   bs _        -> text name <+> ppBytes bs
      PUSHFLOAT   d           -> text name <+> pretty d
      PUSHCODE    global      -> text name <+> pretty global
      PUSHCONT    ofs         -> text name <+> pretty ofs

    -- stack instructions
      ARGCHK      n           -> text name  <+> pretty n
      SLIDE       n m depth   -> text name  <+> pretty n <+> pretty m <+> pretty depth
      STUB        var         -> text name  <+> pretty var

    -- control
      ENTER                   -> text name
      RAISE                   -> text name
      CALL        global      -> text name <+> pretty global

      ENTERCODE   global      -> text name <+> pretty global
      EVALVAR     var         -> text name <+> pretty var

      RETURN                  -> text name
      RETURNCON   con         -> text name <+> pretty con
      RETURNINT   n           -> text name <+> pretty n

    -- applications
      ALLOCAP     arity       -> text name <+> pretty arity
      PACKAP      var arity   -> text name  <+> pretty var <+> pretty arity
      PACKNAP     var arity   -> text name <+> pretty var <+> pretty arity
      NEWAP       arity       -> text name   <+> pretty arity
      NEWNAP      arity       -> text name  <+> pretty arity

    -- constructors
      ALLOCCON    con         -> text name <+> pretty con
      PACKCON     con var     -> text name  <+> pretty var <+> pretty con
      NEWCON      con         -> text name   <+> pretty con
      
      NEW arity               -> text name <+> pretty arity
      PACK arity var          -> text name <+> pretty arity <+> pretty var
      UNPACK arity            -> text name <+> pretty arity

    -- optimized instructions
      PUSHVARS2  v w          -> text name <+> pretty v <+> pretty w

      NEWCON0 con             -> text name <+> pretty con
      NEWCON1 con             -> text name <+> pretty con
      NEWCON2 con             -> text name <+> pretty con
      NEWCON3 con             -> text name <+> pretty con

      RETURNCON0 con          -> text name <+> pretty con

    -- others
      _                       -> text name
    where 
      name = nameFromInstr instr
    
instance Pretty Alt where 
   pretty (Alt pat is) = nest 2 (pretty pat <> text ":" <$> pretty is)
   prettyList = vcat . map pretty

instance Pretty Pat where
   pretty pat =
      case pat of
         PatCon con  -> pretty con
         PatInt i    -> pretty i
         PatTag t a  -> text "(@" <> pretty t <> char ',' <> pretty a <> text ")"
         PatDefault  -> text "<default>"

instance Pretty Con where
   pretty (Con x _ arity _) =
      pretty x <+> pretty arity

instance Pretty Global where
   pretty (Global x _ arity) =
      pretty x <+> pretty arity

instance Pretty Var where
   pretty (Var x ofs depth) =
      pretty x <+> parens( pretty ofs <> comma <+> pretty depth )

ppBytes :: Bytes -> Doc
ppBytes = dquotes . string . stringFromBytes

----------------------------------------------------------------
-- Instruction instances
----------------------------------------------------------------
instance Enum Instr where
  fromEnum = enumFromInstr
  toEnum _ = error "Code.toEnum: undefined for instructions"

instance Eq Instr where
  instr1 == instr2    = fromEnum instr1 == fromEnum instr2

instance Ord Instr where
  compare instr1 instr2  = compare (fromEnum instr1) (fromEnum instr2)

----------------------------------------------------------------
-- Instruction names
----------------------------------------------------------------
instrFromName :: String -> Instr
instrFromName name
  = fromMaybe (error msg) (lookup (map toUpper name) instrNames)
  where
    msg = "Code.instrFromName: unknown instruction name: " ++ name
    instrNames
      = [ ("CATCH", CATCH [])
        , ("RAISE", RAISE)

        , ("ADDINT", ADDINT)
        , ("SUBINT", SUBINT)
        , ("MULINT", MULINT)
        , ("DIVINT", DIVINT)
        , ("MODINT", MODINT)
        , ("QUOTINT",QUOTINT)
        , ("REMINT", REMINT)
        , ("ANDINT", ANDINT)
        , ("XORINT", XORINT)
        , ("ORINT",  ORINT)
        , ("SHRINT", SHRINT)
        , ("SHLINT", SHLINT)
        , ("SHRNAT", SHRNAT)
        , ("NEGINT", NEGINT)

        , ("EQINT", EQINT)
        , ("NEINT", NEINT)
        , ("LTINT", LTINT)
        , ("GTINT", GTINT)
        , ("LEINT", LEINT)
        , ("GEINT", GEINT)

        , ("ADDFLOAT", ADDFLOAT)
        , ("SUBFLOAT", SUBFLOAT)
        , ("MULFLOAT", MULFLOAT)
        , ("DIVFLOAT", DIVFLOAT)
        , ("NEGFLOAT", NEGFLOAT)

        , ("EQFLOAT", EQFLOAT)
        , ("NEFLOAT", NEFLOAT)
        , ("LTFLOAT", LTFLOAT)
        , ("GTFLOAT", GTFLOAT)
        , ("LEFLOAT", LEFLOAT)
        , ("GEFLOAT", GEFLOAT)

        , ("ALLOC",   ALLOC)
        , ("GETFIELD",GETFIELD)
        , ("SETFIELD",SETFIELD)
        , ("GETTAG",  GETTAG)
        , ("GETSIZE", GETSIZE)
        , ("UPDFIELD",UPDFIELD)
        ]


{---------------------------------------------------------------
  instrHasStrictResult: returns [True] if an instruction returns
    a strict result, ie. a value that can be [match]ed or [RETURN]'ed.
---------------------------------------------------------------}

strictResult :: Instr -> Bool
strictResult (NEW _) = True
strictResult instr   = instr `elem` strictList
 where
   strictList = 
      [ ALLOC, ADDINT, SUBINT, MULINT, DIVINT, MODINT, QUOTINT
      , REMINT, ANDINT, XORINT, ORINT, SHRINT, SHLINT, SHRNAT 
      , NEGINT, EQINT, NEINT, LTINT, GTINT, LEINT, GEINT  
      , ADDFLOAT, SUBFLOAT, MULFLOAT, DIVFLOAT, NEGFLOAT
      , EQFLOAT, NEFLOAT, LTFLOAT, GTFLOAT, LEFLOAT, GEFLOAT 
      ]

----------------------------------------------------------------
-- Instruction opcodes
----------------------------------------------------------------
instrFromOpcode :: Int -> Instr
instrFromOpcode i
  | i >= length instrTable  = error "Instr.instrFromOpcode: illegal opcode"
  | otherwise               = instrTable !! i

opcodeFromInstr :: Instr -> Int
opcodeFromInstr instr
  = walk 0 instrTable
  where
    walk _   []     = error "Instr.opcodeFromInstr: no opcode defined for this instruction"
    walk opc (i:is) | instr == i  = opc
                    | otherwise   = (walk $! (opc+1)) is

instrTable :: [Instr]
instrTable =
    [ ARGCHK 0, PUSHCODE global, PUSHCONT 0, PUSHVAR var
    , PUSHINT 0, PUSHFLOAT 0, PUSHBYTES mempty 0, SLIDE 0 0 0, STUB var
    , ALLOCAP 0, PACKAP var 0, PACKNAP var 0, NEWAP 0, NEWNAP 0
    , ENTER, RETURN, PUSHCATCH, RAISE, CALL global
    , ALLOCCON con, PACKCON con var, NEWCON con
    --, UNPACKCON 0 , TESTCON id [], TESTINT 0 []
    , NOP, NOP, NOP
    , ADDINT, SUBINT, MULINT, DIVINT, MODINT, QUOTINT, REMINT
    , ANDINT, XORINT, ORINT, SHRINT, SHLINT, SHRNAT, NEGINT
    , EQINT, NEINT, LTINT, GTINT, LEINT, GEINT
    , ALLOC, NEW 0, GETFIELD, SETFIELD, GETTAG, GETSIZE, PACK 0 var, UNPACK 0
    , PUSHVAR0, PUSHVAR1, PUSHVAR2, PUSHVAR3, PUSHVAR4
    -- , PUSHVARS2 id 0 id 0, PUSHVARS3 id 0 id 0 id 0, PUSHVARS4 id 0 id 0 id 0 id 0
    , PUSHVARS2 var var, NOP, NOP
    , NOP, NEWAP2, NEWAP3, NEWAP4
    , NOP, NEWNAP2, NEWNAP3, NEWNAP4
    , NEWCON0 con, NEWCON1 con, NEWCON2 con, NEWCON3 con
    , ENTERCODE global, EVALVAR var, RETURNCON con, RETURNINT 0, RETURNCON0 con 
    , MATCHCON [], SWITCHCON [], MATCHINT [], NOP {- MATCHFLOAT -}, MATCH []
    , NOP {- ENTERFLOAT -}, ADDFLOAT, SUBFLOAT, MULFLOAT, DIVFLOAT, NEGFLOAT
    , EQFLOAT, NEFLOAT, LTFLOAT, GTFLOAT, LEFLOAT, GEFLOAT
    -- Additional experimental instructions (AD, 20040108)
    , UPDFIELD    
    ]
  where
    dum    = dummyId
    var    = Var dum 0 0
    global = Global dum 0 0
    con    = Con dum 0 0 0


----------------------------------------------------------------
-- Instruction enumeration
----------------------------------------------------------------

isCATCH :: Instr -> Bool
isCATCH (CATCH _) = True
isCATCH _         = False
             
enumFromInstr :: Instr -> Int
enumFromInstr instr
  = case instr of
      -- pseudo instructions
      VAR {}                  -> -1
      PARAM {}                -> -2
      USE {}                  -> -3
      NOP                     -> -4
      ATOM {}                 -> -5
      INIT {}                 -> -6


    -- structured instructions
      CATCH {}                -> 0
      EVAL {}                 -> 1
      RESULT {}               -> 2

      MATCHCON {}             -> 3
      SWITCHCON {}            -> 4
      MATCHINT {}             -> 5
      MATCH {}                -> 6

    -- push instructions
      PUSHVAR {}              -> 10
      PUSHINT {}              -> 11
      PUSHBYTES {}            -> 12
      PUSHFLOAT {}            -> 13
      PUSHCODE {}             -> 14
      PUSHCONT {}             -> 15
      PUSHCATCH               -> 16

    -- stack instructions
      ARGCHK {}               -> 20
      SLIDE {}                -> 21
      STUB {}                 -> 22

    -- control
      ENTER                   -> 30
      RAISE                   -> 31
      CALL {}                 -> 32

      ENTERCODE {}            -> 33
      EVALVAR {}              -> 34

      RETURN                  -> 35
      RETURNCON {}            -> 36
      RETURNINT {}            -> 37

    -- applications
      ALLOCAP {}              -> 40
      PACKAP {}               -> 41
      PACKNAP {}              -> 42
      NEWAP {}                -> 43
      NEWNAP {}               -> 44

    -- constructors
      ALLOCCON {}             -> 47
      PACKCON {}              -> 48
      NEWCON {}               -> 49

      ALLOC                   -> 50
      NEW {}                  -> 51
      PACK {}                 -> 52
      UNPACK {}               -> 53
      GETFIELD                -> 54 
      SETFIELD                -> 55
      GETTAG                  -> 56
      GETSIZE                 -> 57
      UPDFIELD                -> 58

    -- INT operations
      ADDINT                  -> 60
      SUBINT                  -> 61
      MULINT                  -> 62
      DIVINT                  -> 63
      MODINT                  -> 64
      QUOTINT                 -> 65
      REMINT                  -> 66
      ANDINT                  -> 67
      XORINT                  -> 68
      ORINT                   -> 69
      SHRINT                  -> 70
      SHLINT                  -> 71
      SHRNAT                  -> 72
      NEGINT                  -> 73

      -- relative INT ops
      EQINT                   -> 80
      NEINT                   -> 81
      LTINT                   -> 82
      GTINT                   -> 83
      LEINT                   -> 84
      GEINT                   -> 85

      -- optimized instructions
      PUSHVAR0                -> 100
      PUSHVAR1                -> 101
      PUSHVAR2                -> 102
      PUSHVAR3                -> 103
      PUSHVAR4                -> 104
      PUSHVARS2 {}            -> 105

      -- optimizes AP
      NEWAP2                  -> 111
      NEWAP3                  -> 112
      NEWAP4                  -> 113

      NEWNAP2                 -> 114
      NEWNAP3                 -> 115
      NEWNAP4                 -> 116

      -- optimized NEWCON
      NEWCON0 {}              -> 120
      NEWCON1 {}              -> 121
      NEWCON2 {}              -> 122
      NEWCON3 {}              -> 123

      RETURNCON0 {}           -> 124

      -- FLOAT operations
      ADDFLOAT                  -> 160
      SUBFLOAT                  -> 161
      MULFLOAT                  -> 162
      DIVFLOAT                  -> 163
      NEGFLOAT                  -> 164

      -- relative FLOAT ops
      EQFLOAT                   -> 180
      NEFLOAT                   -> 181
      LTFLOAT                   -> 182
      GTFLOAT                   -> 183
      LEFLOAT                   -> 184
      GEFLOAT                   -> 185


----------------------------------------------------------------
-- Instruction names
----------------------------------------------------------------

nameFromInstr :: Instr -> String
nameFromInstr instr
  = case instr of
      -- pseudo instructions
      VAR {}                  -> "VAR"
      PARAM {}                -> "PARAM"
      USE {}                  -> "USE"
      NOP                     -> "NOP"
      ATOM {}                 -> "ATOM"
      INIT {}                 -> "INIT"


    -- structured instructions
      CATCH {}                -> "CATCH"
      EVAL {}                 -> "EVAL"
      RESULT {}               -> "RESULT"

      MATCHCON {}             -> "MATCHCON"
      SWITCHCON {}            -> "SWITCHCON"
      MATCHINT {}             -> "MATCHINT"
      MATCH {}                -> "MATCH"

    -- push instructions
      PUSHVAR {}              -> "PUSHVAR"
      PUSHINT {}              -> "PUSHINT"
      PUSHBYTES {}            -> "PUSHBYTES"
      PUSHFLOAT {}            -> "PUSHFLOAT"
      PUSHCODE {}             -> "PUSHCODE"
      PUSHCONT {}             -> "PUSHCONT"
      PUSHCATCH               -> "PUSHCATCH"

    -- stack instructions
      ARGCHK {}               -> "ARGCHK"
      SLIDE {}                -> "SLIDE"
      STUB {}                 -> "STUB"

    -- control
      ENTER                   -> "ENTER"
      RAISE                   -> "RAISE"
      CALL {}                 -> "CALL"

      ENTERCODE {}            -> "ENTERCODE"
      EVALVAR {}              -> "EVALVAR"

      RETURN                  -> "RETURN"
      RETURNCON {}            -> "RETURNCON"
      RETURNINT {}            -> "RETURNINT"

    -- applications
      ALLOCAP {}              -> "ALLOCAP"
      PACKAP {}               -> "PACKAP"
      PACKNAP {}              -> "PACKNAP"
      NEWAP {}                -> "NEWAP"
      NEWNAP {}               -> "NEWNAP"

    -- constructors
      ALLOCCON {}             -> "ALLOCCON"
      PACKCON {}              -> "PACKCON"
      NEWCON {}               -> "NEWCON"

      ALLOC                   -> "ALLOC"
      NEW {}                  -> "NEW"
      PACK {}                 -> "PACK"
      UNPACK {}               -> "UNPACK"
      GETFIELD                -> "GETFIELD" 
      SETFIELD                -> "SETFIELD"
      GETTAG                  -> "GETTAG"
      GETSIZE                 -> "GETSIZE"
      UPDFIELD                -> "UPDFIELD"

    -- INT operations
      ADDINT                  -> "ADDINT"
      SUBINT                  -> "SUBINT"
      MULINT                  -> "MULINT"
      DIVINT                  -> "DIVINT"
      MODINT                  -> "MODINT"
      QUOTINT                 -> "QUOTINT"
      REMINT                  -> "REMINT"
      ANDINT                  -> "ANDINT"
      XORINT                  -> "XORINT"
      ORINT                   -> "ORINT"
      SHRINT                  -> "SHRINT"
      SHLINT                  -> "SHLINT"
      SHRNAT                  -> "SHRNAT"
      NEGINT                  -> "NEGINT"

      -- relative INT ops
      EQINT                   -> "EQINT"
      NEINT                   -> "NEINT"
      LTINT                   -> "LTINT"
      GTINT                   -> "GTINT"
      LEINT                   -> "LEINT"
      GEINT                   -> "GEINT"

      -- optimized instructions
      PUSHVAR0                -> "PUSHVAR0"
      PUSHVAR1                -> "PUSHVAR1"
      PUSHVAR2                -> "PUSHVAR2"
      PUSHVAR3                -> "PUSHVAR3"
      PUSHVAR4                -> "PUSHVAR4"

      PUSHVARS2 {}            -> "PUSHVARS2"


      -- optimizes AP
      NEWAP2                  -> "NEWAP2"
      NEWAP3                  -> "NEWAP3"
      NEWAP4                  -> "NEWAP4"

      NEWNAP2                 -> "NEWNAP2"
      NEWNAP3                 -> "NEWNAP3"
      NEWNAP4                 -> "NEWNAP4"

      -- optimized NEWCON
      NEWCON0 {}              -> "NEWCON0"
      NEWCON1 {}              -> "NEWCON1"
      NEWCON2 {}              -> "NEWCON2"
      NEWCON3 {}              -> "NEWCON3"

      RETURNCON0 {}           -> "RETURNCON0"

    -- FLOAT operations
      ADDFLOAT                  -> "ADDFLOAT"
      SUBFLOAT                  -> "SUBFLOAT"
      MULFLOAT                  -> "MULFLOAT"
      DIVFLOAT                  -> "DIVFLOAT"
      NEGFLOAT                  -> "NEGFLOAT"

    -- relative FLOAT ops
      EQFLOAT                   -> "EQFLOAT"
      NEFLOAT                   -> "NEFLOAT"
      LTFLOAT                   -> "LTFLOAT"
      GTFLOAT                   -> "GTFLOAT"
      LEFLOAT                   -> "LEFLOAT"
      GEFLOAT                   -> "GEFLOAT"
