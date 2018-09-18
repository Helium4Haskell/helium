module Helium.CodeGeneration.InstanceDictionary where

import Lvm.Core.Expr 
import Lvm.Core.Module

import Lvm.Common.Id 

import Helium.CodeGeneration.CoreUtils
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Text.PrettyPrint.Leijen
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

constructFunctionMap :: ImportEnvironment -> Name -> [(String, Int)]
constructFunctionMap env name = 
    let 
        err = error "Invalid class name" 
        f :: (Name, a, b) -> String
        f (name, _, _) = getNameName name 
        mapF = map f . snd
    in zip (maybe err mapF  $ M.lookup name (classMemberEnvironment env)) [0..]

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: [(String, Int)] -> [CoreDecl]
classFunctions combinedNames = map classFunction combinedNames
        where
            classFunction :: (String, Int) -> CoreDecl
            classFunction (name, label) = 
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString name
                        , declAccess  = public
                        , valueEnc    = Nothing
                        , valueValue  = Lam dictParam (Ap (Var dictParam) (Lit (LitInt label)))
                        , declCustoms = [] 
                        }
                in val
         
combineDeclIndex :: [(String, Int)] -> [(String, CoreDecl)] -> [(Int, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(_, l) -> (l, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = 
        let
            err = error "Invalid mapping" 
        in map (\(name, label) -> (label, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: [(String, Int)] -> [(String, CoreDecl)] -> String -> CoreDecl
constructDictionary combinedNames whereDecls dictionaryName = let 
            val = DeclValue 
                { declName    = idFromString ("$dict" ++ dictionaryName)
                , declAccess  = public
                , valueEnc    = Nothing
                , valueValue  = getFunc
                , declCustoms = [ custom "type" ("Dict" ++ dictionaryName) ] 
                }
            in val
        where 
            functions = combineDeclIndex combinedNames whereDecls
            idP = idFromString "index"
            getFunc = Lam idP (Match idP (makeAlts functions))
            makeAlts :: [(Int, Maybe CoreDecl)] -> Alts
            makeAlts = map (uncurry makeAlt)
            makeAlt :: Int -> Maybe CoreDecl -> Alt
            makeAlt label decl= let
                            undefinedFunc = Var $ idFromString "undefined"
                            func = maybe undefinedFunc getCoreValue decl
                            pat = PatLit (LitInt label)
                            in Alt pat func


getCoreName :: CoreDecl -> String 
getCoreName cd = stringFromId $ declName cd

getCoreValue :: CoreDecl -> Expr 
getCoreValue = valueValue