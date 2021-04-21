{-| Module      :  PhaseParser
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseParser(phaseParser) where

import Helium.Main.CompileUtils
import Helium.Parser.LexerToken(Token)
import Helium.Parser.Parser (module_)
import Helium.Parser.ParseLibrary(runHParser)
import qualified Helium.Parser.CheckDim as CD
import Text.ParserCombinators.Parsec.Error (ParseError, Message(..), newErrorMessage)
import Text.ParserCombinators.Parsec.Pos(newPos)
import Helium.Syntax.UHA_Syntax(Name(..), MaybeName(..))
import Helium.Syntax.UHA_Range(noRange)
import Helium.Utils.Utils (firstUpper)

phaseParser :: 
   String -> [Token] -> [Option] -> 
   Phase ParseError Module
phaseParser fullName tokens options = do
    enterNewPhase "Parsing" options
    let (_, baseName, _) = splitFilePath fullName

    case runHParser module_ fullName tokens True of
        Left parseError ->
            return (Left [parseError])
        Right m ->
            (do let fixedm = fixModuleName m $ firstUpper baseName
                let res = CD.wrap_Module (CD.sem_Module fixedm) CD.Inh_Module {}
                if not (DimensionTypes `elem` options) then
                    case CD.dimconstruct_Syn_Module res of
                        Nothing -> return (Right fixedm)
                        Just (line,column)  -> return $ Left [newErrorMessage (Message "dimension construct \n you should use --dim-types option") (newPos "Dimension" line column)]
                else return (Right fixedm))

-- | Make sure the module has a name. If there is no name (module without
--   header) insert the base name of the file name as name.
fixModuleName :: Module -> String -> Module
fixModuleName original@(Module_Module r name es b) baseName =
    case name of
        MaybeName_Nothing ->
            Module_Module r (MaybeName_Just (Name_Identifier noRange [] [] baseName)) es b -- !!!Name
        _ -> original
