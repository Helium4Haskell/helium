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

import qualified Data.Map as M

type DictLabel = String

constructFunctionMap :: ImportEnvironment -> Int -> Name -> [(Name, Int, DictLabel)]
constructFunctionMap env nrOfSuperclasses name = 
    let 
        err = error $ "Invalid class name " ++ show name 
        f :: Int -> (Name, a, b, c) -> (Name, Int, DictLabel)
        f i (n, _, _, _) = (n, i, "func$" ++ getNameName n) 
        
    in maybe err (zipWith f [nrOfSuperclasses..] . snd) $ M.lookup name (classMemberEnvironment env)

constructSuperClassMap :: ImportEnvironment -> String -> [(String, Int, DictLabel)]
constructSuperClassMap env name =
    let 
        err = error $ "Invalid class name" ++ show name ++ " in " ++ show (classEnvironment env)
        f :: Class -> [(String, Int, DictLabel)]
        f (ns, _) = zipWith (\n i -> (n, i, "superC$" ++ n)) ns [0..]
    in maybe err f (M.lookup name $ classEnvironment env)

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: ImportEnvironment -> String -> [(Name, Int, DictLabel)] -> [CoreDecl]
classFunctions importEnv className combinedNames = [DeclCon
                                                    { declName = idFromString ("Dict" ++ className)
                                                    , declAccess  = public
                                                    , declArity   = length superclasses + length combinedNames
                                                    , conTag      = 0
                                                    , declCustoms = [ custom "type" ("Dict" ++ className) ]       
                                                    }]
                                                    ++ map superDict superclasses ++ map classFunction combinedNames
        where
            labels = map (\(_, _, l)->l) superclasses ++ map (\(_, _, l)->l) combinedNames
            superclasses = constructSuperClassMap importEnv className
            superDict :: (String, Int, DictLabel) -> CoreDecl
            superDict (superName, tag, label) =
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ "$get" ++ superName ++ "$" ++ className
                        , declAccess  = public
                        , valueEnc    = Nothing
                        , valueValue  = Lam dictParam 
                                        (Match dictParam 
                                            [
                                                Alt (PatCon (ConId $ idFromString ("Dict" ++ className)) (map idFromString labels)) 
                                                    (Var $ idFromString label)
                                                
                                            ]
                                        )
                        , declCustoms = [custom "type" ("Dict$" ++ className ++" -> Dict$" ++ superName)]
                        }
                in val
            classFunction :: (Name, Int, DictLabel) -> CoreDecl
            classFunction (name, tag, label) = 
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ getNameName name
                        , declAccess  = public
                        , valueEnc    = Nothing
                        , valueValue  = Lam dictParam $ 
                                Let (Strict $ Bind dictParam (Var dictParam))
                                (Match dictParam 
                                    [
                                        Alt (PatCon (ConId $ idFromString ("Dict" ++ className)) (map idFromString labels)) 
                                            (Ap (Var $ idFromString label) (Var dictParam))
                                        --, Alt (PatCon (ConId $ idFromString ("Dict" ++ className)) $ map idFromString ["x", "y", "z"]) (Var $ idFromString "x")
                                        --, Alt PatDefault (Lam (idFromString "d") $ Lam (idFromString "x") (Var $ idFromString "x"))
                                    ]
                                )
                        , declCustoms = toplevelType name importEnv True
                        }
                in val
         
combineDeclIndex :: [(Name, Int, DictLabel)] -> [(Name, CoreDecl)] -> [(DictLabel, Name, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(n, _, l) -> (l, n, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = map (\(name, _, label) -> (label, name, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: ImportEnvironment -> [(String, Name)] -> [(Name, Int, DictLabel)] -> [(Name, CoreDecl)] -> Name -> String -> [Name] -> CoreDecl
constructDictionary importEnv instanceSuperClass combinedNames whereDecls className insName typeVariables = 
        let 
            
            val = DeclValue 
                { declName    = idFromString ("$dict" ++ getNameName className ++ "$" ++ insName)
                , declAccess  = public
                , valueEnc    = Nothing
                , valueValue  = dict
                , declCustoms = custom "type" ("Dict" ++ getNameName className ++ "$" ++ insName)
                            :    map (custom "typeVariable" . getNameName) typeVariables 
                            ++   map (\(superName, superVar) -> custom "superInstance" $ superName ++ "-" ++ getNameName superVar) instanceSuperClass
                }
            in val
        where 
            functions = combineDeclIndex combinedNames whereDecls
            idP = idFromString "index"
            superClasses = constructSuperClassMap importEnv $ getNameName className
            dict = foldr Lam (Let (Rec binds) (Var $ idFromString "dict")) instanceSuperClassLabels
            binds = map makeBindSuper superClasses ++ map makeBindFunc functions ++ [dictCon]
            labels = map (\(_, _, l)->l) superClasses ++ map (\(l, _, _)->l) functions
            instanceSuperClassLabels = map (\(className, tvar) -> idFromString $ "$instanceDict" ++ className ++ "$" ++ getNameName tvar) instanceSuperClass
            makeBindSuper :: (String, Int, DictLabel) -> Bind
            makeBindSuper (cName, tag, label) = Bind (idFromString label) (Var (idFromString ("$dict" ++ cName ++ "$" ++ insName)))
            makeBindFunc :: (DictLabel, Name, Maybe CoreDecl) -> Bind
            makeBindFunc (label, name, fdecl) = let 
                undefinedFunc = (Var $ idFromString ("default$" ++ getNameName className ++ "$" ++ getNameName name))
                func = maybe undefinedFunc getCoreValue fdecl
                in Bind (idFromString label) func
            dictCon = Bind (idFromString "dict") (
                    foldl Ap (Con $ ConId $ idFromString ("Dict" ++ getNameName className)) $ map (Var . idFromString) labels
                )

getCoreName :: CoreDecl -> String 
getCoreName cd = stringFromId $ declName cd

getCoreValue :: CoreDecl -> Expr 
getCoreValue = valueValue

constructClassMemberCustomDecl :: ImportEnvironment -> Name -> Maybe (Names, [(Name, TpScheme, Bool, HasDefault)]) -> [Custom]
constructClassMemberCustomDecl _ _ Nothing =  internalError "InstanceDictionary" "constructClassMemberCustomDecl" "Unknown class" 
constructClassMemberCustomDecl env name (Just (typevars, members)) = typeVarsDecl : superClassesDecl ++ map functionToCustom members
                        where
                            superClassesDecl :: [Custom]
                            superClassesDecl = 
                                let
                                    Just classDef = M.lookup (getNameName name) (classEnvironment env)
                                    conv :: String -> Custom
                                    conv super = CustomDecl (DeclKindCustom $ idFromString "SuperClass") [CustomName $ idFromString super]
                                in map conv $ fst classDef
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
                        updateName fdecl = fdecl{
                            declName = idFromString $ constructName fname
                        }
                        fDefault :: CoreDecl
                        fDefault = DeclValue
                            { declName    = idFromString $ constructName fname
                            , declAccess  = public 
                            , valueEnc    = Nothing
                            , valueValue  = Var $ idFromString "undefined"
                            , declCustoms = toplevelType fname importEnv True
                            }
                    in maybe fDefault updateName (lookup fname defaults)
                

                            