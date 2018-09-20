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

constructFunctionMap :: ImportEnvironment -> Name -> [(Name, Int)]
constructFunctionMap env name = 
    let 
        err = error "Invalid class name" 
        f :: (Name, a, b) -> Name
        f (name, _, _) = name 
        mapF = map f . snd
    in zip (maybe err mapF  $ M.lookup name (classMemberEnvironment env)) [0..]

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: ImportEnvironment -> [(Name, Int)] -> [CoreDecl]
classFunctions importEnv combinedNames = map classFunction combinedNames
        where
            classFunction :: (Name, Int) -> CoreDecl
            classFunction (name, label) = 
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ getNameName name
                        , declAccess  = public
                        , valueEnc    = Nothing
                        , valueValue  = Lam dictParam (Ap (Var dictParam) (Lit (LitInt label)))
                        , declCustoms = toplevelType name importEnv True
                        }
                in val
         
combineDeclIndex :: [(Name, Int)] -> [(Name, CoreDecl)] -> [(Int, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(_, l) -> (l, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = 
        let
            err = error "Invalid mapping" 
        in map (\(name, label) -> (label, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: [(Name, Int)] -> [(Name, CoreDecl)] -> Name -> String -> CoreDecl
constructDictionary combinedNames whereDecls className insName  = let 
            val = DeclValue 
                { declName    = idFromString ("$dict" ++ getNameName className ++ "$" ++ insName)
                , declAccess  = public
                , valueEnc    = Nothing
                , valueValue  = getFunc
                , declCustoms = [ custom "type" ("Dict" ++ getNameName className ++ "$" ++ insName) ] 
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
