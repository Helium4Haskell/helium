module Helium.CodeGeneration.InstanceDictionary where

import Lvm.Core.Expr 
import Lvm.Core.Module

import Lvm.Common.Id 
import Lvm.Common.Byte

import Helium.CodeGeneration.CoreUtils
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils

import Top.Types
import Text.PrettyPrint.Leijen
import qualified Data.Map as M
import Data.Maybe

constructFunctionMap :: ImportEnvironment -> Name -> [(Name, Int)]
constructFunctionMap env name = 
    let 
        err = error "Invalid class name" 
        f :: (Name, a, b, c) -> Name
        f (name, _, _, _) = name 
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
                        , valueValue  = Lam dictParam (Ap (Ap (Var dictParam) (Lit (LitInt label))) (Var dictParam))
                        , declCustoms = toplevelType name importEnv True
                        }
                in val
         
combineDeclIndex :: [(Name, Int)] -> [(Name, CoreDecl)] -> [(Int, Name, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(n, l) -> (l, n, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = 
        let
            err = error "Invalid mapping" 
        in map (\(name, label) -> (label, name, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: [(Name, Int)] -> [(Name, CoreDecl)] -> Name -> String  -> CoreDecl
constructDictionary combinedNames whereDecls className insName = let 
            
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
            makeAlts :: [(Int, Name, Maybe CoreDecl)] -> Alts
            makeAlts = map (\(l, n, mc) -> makeAlt l n mc)
            makeAlt :: Int -> Name -> Maybe CoreDecl -> Alt
            makeAlt label name decl = let 
                            undefinedFunc = (Var $ idFromString ("default$" ++ getNameName className ++ "$" ++ getNameName name))
                            func = maybe undefinedFunc getCoreValue decl
                            pat = PatLit (LitInt label)
                            in Alt pat func


getCoreName :: CoreDecl -> String 
getCoreName cd = stringFromId $ declName cd

getCoreValue :: CoreDecl -> Expr 
getCoreValue = valueValue

constructClassMemberCustomDecl :: Maybe (Names, [(Name, TpScheme, Bool, HasDefault)]) -> [Custom]
constructClassMemberCustomDecl Nothing =  internalError "InstanceDictionary" "constructClassMemberCustomDecl" "Unknown class" 
constructClassMemberCustomDecl (Just (typevars, members)) = typeVarsDecl : map functionToCustom members
                        where
                            typeVarsDecl :: Custom
                            typeVarsDecl = CustomDecl 
                                (DeclKindCustom $ idFromString "ClassTypeVariables")
                                (map (CustomName . idFromString . getNameName) typevars)
                            functionToCustom :: (Name, TpScheme, Bool, HasDefault) -> Custom
                            functionToCustom (name, tps, _, _) = CustomDecl 
                                (DeclKindCustom $ idFromString "Function") 
                                [
                                    CustomName $ idFromString $ getNameName name, 
                                    CustomBytes $ bytesFromString $ show tps
                                ]

convertDictionaries :: ImportEnvironment -> Name -> [Name] -> [(Name, CoreDecl)] -> [CoreDecl]
convertDictionaries importEnv className functions defaults = map makeFunction functions
            where
                constructName :: Name -> String
                constructName fname = "default$" ++ getNameName className ++ "$" ++ getNameName fname
                makeFunction :: Name -> CoreDecl
                makeFunction fname = 
                    let 
                        updateName :: CoreDecl -> CoreDecl
                        updateName decl = decl{
                            declName = idFromString $ constructName fname
                        }
                        fDefault :: CoreDecl
                        fDefault = DeclValue
                            { declName    = idFromString $ constructName fname
                            , declAccess  = public 
                            , valueEnc    = Nothing
                            , valueValue  = (Var $ idFromString "undefined")
                            , declCustoms = toplevelType fname importEnv True
                            }
                    in maybe fDefault updateName (lookup fname defaults)
                

                            