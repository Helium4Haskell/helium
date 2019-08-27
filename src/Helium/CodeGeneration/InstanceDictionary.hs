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
import Control.Arrow

import qualified Data.Map as M

import Data.Maybe
import Data.List

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
        err = error $ "Invalid class name " ++ show name ++ " in " ++ show (classEnvironment env)
        f :: Class -> [(String, Int, DictLabel)]
        f (ns, _) = zipWith (\n i -> (n, i, "superC$" ++ n)) ns [0..]
    in maybe err f (M.lookup name $ classEnvironment env)

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: ImportEnvironment -> String -> [Custom] -> [(Name, Int, DictLabel)] -> [CoreDecl]
classFunctions importEnv className origin combinedNames = [DeclCon
                                                    { declName = idFromString ("Dict" ++ className)
                                                    , declAccess  = public
                                                    , declArity   = length locSuperclasses + length combinedNames
                                                    , conTag      = 0
                                                    , declCustoms = [ custom "type" ("Dict$" ++ className) ]  
                                                    }]
                                                    ++ map superDict locSuperclasses ++ concatMap classFunction combinedNames
        where
            -- What was this doinhg here: custom' = CustomLink (idFromString "dict") (DeclKindCustom (idFromString "data"))
            labels = map (\(_, _, l)->l) locSuperclasses ++ map (\(_, _, l)->l) combinedNames
            locSuperclasses = constructSuperClassMap importEnv className
            superDict :: (String, Int, DictLabel) -> CoreDecl
            superDict (superName, _, label) =
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ "$get" ++ superName ++ "$" ++ className
                        , declAccess  = public
                        , valueEnc    = Nothing
                        , valueValue  = Lam dictParam $ Let (Strict $ Bind dictParam (Var dictParam))
                                        (Match dictParam 
                                            [
                                                Alt (PatCon (ConId $ idFromString ("Dict" ++ className)) (map idFromString labels)) 
                                                    (Var $ idFromString label)
                                                
                                            ]
                                        )
                        , declCustoms = [custom "type" ("Dict$" ++ className ++" -> Dict$" ++ superName)]
                        }
                in val
            classFunction :: (Name, Int, DictLabel) -> [CoreDecl]
            classFunction (name, _, label) = 
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
                                    ]
                                )
                        , declCustoms = toplevelType name importEnv True ++ origin
                        }
                in  if getNameName name == "negate" && className == "Prelude.Num" then 
                        [val, val{
                            declName = idFromString "$negate"
                        }]
                    else
                    [val]
         
combineDeclIndex :: [(Name, Int, DictLabel)] -> [(Name, CoreDecl)] -> [(DictLabel, Name, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(n, _, l) -> (l, n, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = map (\(name, _, label) -> (label, name, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: ImportEnvironment -> [(String, Name)] -> [(Name, Int, DictLabel)] -> [(Name, CoreDecl)] -> Name -> String -> [Name] -> [Custom] -> CoreDecl
constructDictionary importEnv instanceSuperClass combinedNames whereDecls className insName typeVariables origin =
        let 
            
            val = DeclValue 
                { declName    = idFromString ("$dict" ++ getNameName className ++ "$" ++ insName)
                , declAccess  = public
                , valueEnc    = Nothing
                , valueValue  = dict
                , declCustoms = custom "type" ("Dict" ++ getNameName className ++ "$" ++ insName)
                            :    map (custom "typeVariable" . getNameName) typeVariables 
                            ++   map (\(superName, superVar) -> custom "superInstance" $ superName ++ "-" ++ getNameName superVar) instanceSuperClass
                            ++ origin
                }
            in val
        where 
            functions = combineDeclIndex combinedNames whereDecls
            -- idP = idFromString "index"
            superClasses = constructSuperClassMap importEnv $ getNameName className
            dict = foldr Lam (Let (Rec binds) (Var $ idFromString "dict")) instanceSuperClassLabels
            binds = map makeBindSuper superClasses ++ map makeBindFunc functions ++ [dictCon]
            labels = map (\(_, _, l)->l) superClasses ++ map (\(l, _, _)->l) functions
            instanceSuperClassLabels = map (\(locClassName, tvar) -> idFromString $ "$instanceDict" ++ locClassName ++ "$" ++ getNameName tvar) instanceSuperClass
            makeBindSuper :: (String, Int, DictLabel) -> Bind
            makeBindSuper (cName, _, label) = let
                    parentMapping :: [(String, String)]
                    parentMapping = map (getNameName *** getNameName) $ getTVMapping importEnv (getNameName className) insName cName
                    resolveSuperInstance :: (String, String) -> Expr
                    resolveSuperInstance (n, theVar)
                            -- check if the required class is already an existing parameter
                            | (n, fst $ fromJust (find (\x -> snd x == theVar) parentMapping)) `elem` map (second getNameName) instanceSuperClass && n == cName= let 
                                        Just tvar = find (\(_, cn) -> cn == theVar) parentMapping
                                    in
                                            Var (idFromString $ "$instanceDict" ++ cName ++ "$" ++ fst tvar)
                            | otherwise = let
                                    -- get all the available super classes
                                    repInstanceSuperClass = filter (\(_, v) -> getNameName v == rVar) instanceSuperClass
                                    rVar = fst $ fromJust $find (\(_, cn) -> cn == theVar) parentMapping
                                    shortestPath :: [[a]] -> [a]
                                    shortestPath [x] = x
                                    shortestPath (x:xs) = 
                                        let 
                                          sp = shortestPath xs
                                        in if length sp < length x then sp else x
                                    shortestPath _ = error "Path should not be empty in shortestPath in InstanceDictionary.hs"     
                                    -- construct the path from a sub class to it's super class, e.g. ["Num", "Ord", "Eq"]
                                    constructPath :: String -> String -> [[String]]
                                    constructPath from to 
                                        | from == to = [[to]] 
                                        | otherwise = let
                                                locSuperClasses = getClassSuperClasses importEnv from
                                                paths :: [[[String]]]
                                                paths = map (`constructPath` to) locSuperClasses
                                                sPaths :: [[String]]
                                                sPaths = map (shortestPath. filter (\x -> last x == to)) paths
                                            in map (from:) sPaths
                                    sPath = shortestPath (constructPath n cName)
                                    combinePath :: String -> [String] -> [(String, String)]
                                    combinePath _ [] = []
                                    combinePath theFirst (x:xs) = (theFirst, x) : combinePath x xs
                                    combinedPath = shortestPath $ map (\source -> filter (uncurry (/=)) $ combinePath (fst source) sPath) repInstanceSuperClass
                                in
                                    foldl 
                                        (\expr (sub, super) -> Ap (Var $ idFromString $ "$get" ++ super ++ "$" ++ sub) expr)
                                        (Var (idFromString $ "$instanceDict" ++ fst (head combinedPath) ++ "$" ++ rVar))
                                        combinedPath
                                
                    instanceSuperClasses = getInstanceSuperClasses importEnv cName insName

                    baseInstance = foldl Ap (Var (idFromString ("$dict" ++ cName ++ "$" ++ insName))) $ map resolveSuperInstance instanceSuperClasses
                    
                in Bind (idFromString label) baseInstance 
            
            makeBindFunc :: (DictLabel, Name, Maybe CoreDecl) -> Bind
            makeBindFunc (label, name, fdecl) = let 
                undefinedFunc = (Var $ idFromString ("default$" ++ getNameName className ++ "$" ++ getNameName name))
                func = maybe undefinedFunc getCoreValue fdecl
                in Bind (idFromString label) func
            dictCon = Bind (idFromString "dict") (
                    foldl Ap (Con $ ConId $ idFromString ("Dict" ++ getNameName className)) $ map (Var . idFromString) labels
                )

getInstanceSuperClassesNames :: ImportEnvironment -> String -> String -> [String]
getInstanceSuperClassesNames env cName iName = map fst $ getInstanceSuperClasses env cName iName

getTVMapping :: ImportEnvironment -> String -> String -> String -> [(Name, Name)]
getTVMapping env className insName superClassName = let
        isInsTp :: Tp -> Bool
        isInsTp (TApp f _) = isInsTp f
        isInsTp (TCon c) = c == insName
        isInsTp _ = error "Uncovered case in isInsTp in getTVMapping in InstanceDictionary.hs"
        cTV = fst $ snd $ fromMaybe (error "Nothing") $ find (\((n, tp), _) -> getNameName n == className && isInsTp tp) $ M.toList $ instanceEnvironment env
        iTV = fst $ snd $ fromMaybe (error "Nothing") $ find (\((n, tp), _) -> getNameName n == superClassName && isInsTp tp) $ M.toList $ instanceEnvironment env
    in zip cTV iTV

getClassSuperClasses :: ImportEnvironment -> String -> [String]
getClassSuperClasses env className = fst $ fromMaybe (error "Nothing") $ M.lookup className (classEnvironment env)

getInstanceSuperClasses :: ImportEnvironment -> String -> String -> [(String, String)]
getInstanceSuperClasses env className insName = snd $ snd $ fromMaybe (error "Nothing") $ find(
        \((n, tp),_) -> getNameName n == className && isInsTp tp
    ) $ M.toList $ instanceEnvironment env
    where
        isInsTp :: Tp -> Bool
        isInsTp (TApp f _) = isInsTp f
        isInsTp (TCon c) = c == insName 
        isInsTp _ = error "Uncovered case in isInsTp in getInstanceSuperClasses in InstanceDictionary.hs"

getCoreName :: CoreDecl -> String 
getCoreName cd = stringFromId $ declName cd

getCoreValue :: CoreDecl -> Expr 
getCoreValue = valueValue

constructClassMemberCustomDecl :: ImportEnvironment -> Name -> Maybe (Names, [(Name, TpScheme, Bool, HasDefault)]) -> [Custom] -> [Custom]
constructClassMemberCustomDecl _ _ Nothing _ =  internalError "InstanceDictionary" "constructClassMemberCustomDecl" "Unknown class" 
constructClassMemberCustomDecl env name (Just (typevars, members)) _ = typeVarsDecl : superClassesDecl ++ map functionToCustom members
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
                            functionToCustom (locName, tps, _, fDefault) = CustomDecl 
                                (DeclKindCustom $ idFromString "Function") 
                                [
                                    CustomName $ idFromString $ getNameName locName, 
                                    CustomBytes $ bytesFromString $ show tps,
                                    if fDefault then CustomInt 1 else CustomInt 0
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
                

                            