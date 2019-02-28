module Helium.CodeGeneration.InstanceDictionary where

import Lvm.Core.Expr
import qualified Lvm.Core.Type as Core
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

constructFunctionMap :: ImportEnvironment -> Int -> Name -> [(Name, Int, DictLabel, Core.Type)]
constructFunctionMap env nrOfSuperclasses name = 
    let 
        err = error $ "Invalid class name " ++ show name 
        f i (n, t, _, _) = (n, i, "func$" ++ getNameName n, toCoreType t) 
        
    in maybe err (zipWith f [nrOfSuperclasses..] . snd) $ M.lookup name (classMemberEnvironment env)

typeClassType :: Id -> Core.Type
typeClassType n = Core.TCon $ Core.TConTypeClassDictionary n

constructSuperClassMap :: ImportEnvironment -> String -> [(String, Int, DictLabel, Core.Type)]
constructSuperClassMap env name =
    let 
        err = error $ "Invalid class name " ++ show name ++ " in " ++ show (classEnvironment env)
        f :: Class -> [(String, Int, DictLabel, Core.Type)]
        f (ns, _) = zipWith (\n i -> (n, i, "superC$" ++ n, typeClassType $ idFromString n)) ns [0..]
    in maybe err f (M.lookup name $ classEnvironment env)

constructorType :: Id -> [Core.Type] -> Core.Type -> Core.Type
constructorType typeVar fields classType =
    Core.TForall typeVar $ Core.typeFunction fields' classType
    where
        fields' = map instantiateClassVar fields
        instantiateClassVar :: Core.Type -> Core.Type
        instantiateClassVar (Core.TForall x t)
            | x == typeVar = t
            | otherwise = Core.TForall x $ instantiateClassVar t
        instantiateClassVar t = t

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: ImportEnvironment -> String -> String -> [(Name, Int, DictLabel, Core.Type)] -> [CoreDecl]
classFunctions importEnv className typeVar combinedNames = [DeclCon -- Declare the constructor for the dictionary
                                                    { declName = dictName
                                                    , declAccess  = public
                                                    , declType    = constructorType typeArgId (map (\(_, _, _, t) -> t) superclasses ++ map (\(_, _, _, t) -> t) combinedNames) classType
                                                    , declCustoms = 
                                                        -- Types of constructors are not enforced
                                                        [ custom "type" ("whatever")
                                                        , CustomLink dictName (DeclKindCustom $ idFromString "data") ]
                                                    }
                                                   ,DeclCustom -- Declare the data type for the dictionary
                                                    { declName = dictName
                                                    , declAccess = public
                                                    , declKind = DeclKindCustom (idFromString "data")
                                                    , declCustoms = [ CustomInt 1 ]} -- 1 type argument
                                                   ]
                                                    ++ map superDict superclasses ++ concatMap classFunction combinedNames
        where
            typeArgId = idFromString typeVar
            typeArg = Core.TVar typeArgId
            classType = Core.TAp (typeClassType $ idFromString className) typeArg
            dictName = idFromString ("Dict$" ++ className)
            labels = map (\(_, _, l, _)->l) superclasses ++ map (\(_, _, l, _)->l) combinedNames
            superclasses = constructSuperClassMap importEnv className
            superDict :: (String, Int, DictLabel, Core.Type) -> CoreDecl
            superDict (superName, tag, label, t) =
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ "$get" ++ superName ++ "$" ++ className
                        , declAccess  = public
                        , declType    = Core.TForall typeArgId $ Core.typeFunction [classType] $ Core.TAp t typeArg
                        , valueValue  = Lam (Variable dictParam classType) $ Let (Strict $ Bind (Variable dictParam $ Core.typeToStrict classType) (Var dictParam))
                                        (Match dictParam 
                                            [
                                                Alt (PatCon (ConId $ idFromString ("Dict$" ++ className)) (map idFromString labels)) 
                                                    (Var $ idFromString label)
                                                
                                            ]
                                        )
                        , declCustoms = [custom "type" ("Dict$" ++ className ++" a -> Dict$" ++ superName ++ " a")]
                        }
                in val
            classFunction :: (Name, Int, DictLabel, Core.Type) -> [CoreDecl]
            classFunction (name, tag, label, _) = 
                let dictParam = idFromString "dict"
                    val = DeclValue 
                        { declName    = idFromString $ getNameName name
                        , declAccess  = public
                        , declType    = declarationType name importEnv True
                        , valueValue  = Lam (Variable dictParam classType) $ 
                                Let (Strict $ Bind (Variable dictParam $ Core.typeToStrict classType) (Var dictParam))
                                (Match dictParam 
                                    [
                                        Alt (PatCon (ConId $ idFromString ("Dict$" ++ className)) (map idFromString labels)) 
                                            (Ap (Var $ idFromString label) (Var dictParam))
                                    ]
                                )
                        , declCustoms = toplevelType name importEnv True
                        }
                in  if getNameName name == "negate" && className == "Num" then 
                        [val, val{
                            declName = idFromString "$negate"
                        }]
                    else
                    [val]

combineDeclIndex :: [(Name, Int, DictLabel, Core.Type)] -> [(Name, CoreDecl)] -> [(DictLabel, Name, Core.Type, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(n, _, l, t) -> (l, n, t, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = map (\(name, _, label, t) -> (label, name, t, lookup name decls)) names

--returns a dictionary with specific implementations for every instance
constructDictionary :: ImportEnvironment -> [(String, Name, Core.Type)] -> [(Name, Int, DictLabel, Core.Type)] -> [(Name, CoreDecl)] -> Name -> String -> [Name] -> Core.Type -> CoreDecl
constructDictionary importEnv instanceSuperClass combinedNames whereDecls className insName typeVariables insType = 
        let 
            
            val = DeclValue 
                { declName    = idFromString ("$dict" ++ getNameName className ++ "$" ++ insName)
                , declAccess  = public
                , declType    = Core.TAp (typeClassType $ idFromName className) insType
                , valueValue  = dict
                , declCustoms = custom "type" ("Dict$" ++ getNameName className ++ " " ++ insName)
                            :    map (custom "typeVariable" . getNameName) typeVariables 
                            ++   map (\(superName, superVar, _) -> custom "superInstance" $ superName ++ "-" ++ getNameName superVar) instanceSuperClass
                }
            in val
        where 
            functions = combineDeclIndex combinedNames whereDecls
            idP = idFromString "index"
            superClasses = constructSuperClassMap importEnv $ getNameName className
            dict = foldr Lam (Let (Rec binds) (Var $ idFromString "dict")) instanceSuperClassVariables
            binds = map makeBindSuper superClasses ++ map makeBindFunc functions ++ [dictCon]
            labels = map (\(_, _, l, _)->l) superClasses ++ map (\(l, _, _, _)->l) functions
            instanceSuperClassVariables = map (\(className, tvar, superType) -> Variable (idFromString $ "$instanceDict" ++ className ++ "$" ++ getNameName tvar) superType) instanceSuperClass
            makeBindSuper :: (String, Int, DictLabel, Core.Type) -> Bind
            makeBindSuper (cName, tag, label, t) = let
                    parentMapping :: [(String, String)]
                    parentMapping = map (getNameName *** getNameName) $ getTVMapping importEnv (getNameName className) insName cName
                    resolveSuperInstance :: (String, String) -> Expr
                    resolveSuperInstance (n, var)
                            -- check if the required class is already an existing parameter
                            | (n, fst $ fromJust (find (\x -> snd x == var) parentMapping)) `elem` map (\(a, b, _) -> (a, getNameName b)) instanceSuperClass && n == cName= let 
                                        Just tvar = find (\(_, cn) -> cn == var) parentMapping
                                    in
                                            Var (idFromString $ "$instanceDict" ++ cName ++ "$" ++ fst tvar)
                            | otherwise = let
                                    -- get all the available super classes
                                    repInstanceSuperClass = filter (\(_, v, _) -> getNameName v == rVar) instanceSuperClass
                                    rVar = fst $ fromJust $find (\(_, cn) -> cn == var) parentMapping
                                    shortestPath :: [[a]] -> [a]
                                    shortestPath [x] = x
                                    shortestPath (x:xs) = let 
                                        sp = shortestPath xs
                                        in if length sp < length x then sp else x
                                    -- construct the path from a sub class to it's super class, e.g. ["Num", "Ord", "Eq"]
                                    constructPath :: String -> String -> [[String]]
                                    constructPath from to 
                                        | from == to = [[to]] 
                                        | otherwise = let
                                                superClasses = getClassSuperClasses importEnv from
                                                paths :: [[[String]]]
                                                paths = map (`constructPath` to) superClasses
                                                sPaths :: [[String]]
                                                sPaths = map (shortestPath. filter (\x -> last x == to)) paths
                                            in map (from:) sPaths
                                    sPath = shortestPath (constructPath n cName)
                                    combinePath :: String -> [String] -> [(String, String)]
                                    combinePath first [] = []
                                    combinePath first (x:xs) = (first, x) : combinePath x xs
                                    combinedPath = shortestPath $ map (\(source, _, _) -> filter (uncurry (/=)) $ combinePath source sPath) repInstanceSuperClass
                                in
                                    foldl 
                                        (\expr (sub, super) -> Ap (Var $ idFromString $ "$get" ++ super ++ "$" ++ sub) expr)
                                        (Var (idFromString $ "$instanceDict" ++ fst (head combinedPath) ++ "$" ++ rVar))
                                        combinedPath
                                
                    instanceSuperClasses = getInstanceSuperClasses importEnv cName insName

                    baseInstance = foldl Ap (Var (idFromString ("$dict" ++ cName ++ "$" ++ insName))) $ map resolveSuperInstance instanceSuperClasses
                    
                in Bind (Variable (idFromString label) t) baseInstance 
            
            makeBindFunc :: (DictLabel, Name, Core.Type, Maybe CoreDecl) -> Bind
            makeBindFunc (label, name, t, fdecl) = let 
                undefinedFunc = (Var $ idFromString ("default$" ++ getNameName className ++ "$" ++ getNameName name))
                func = maybe undefinedFunc getCoreValue fdecl
                in Bind (Variable (idFromString label) t) func
            dictCon = Bind (Variable (idFromString "dict") Core.TAny) (
                    foldl Ap (Con $ ConId $ idFromString ("Dict$" ++ getNameName className)) $ map (Var . idFromString) labels
                )

getInstanceSuperClassesNames :: ImportEnvironment -> String -> String -> [String]
getInstanceSuperClassesNames env cName iName = map fst $ getInstanceSuperClasses env cName iName

getTVMapping :: ImportEnvironment -> String -> String -> String -> [(Name, Name)]
getTVMapping env className insName superClassName = let
        isInsTp :: Tp -> Bool
        isInsTp (TApp f _) = isInsTp f
        isInsTp (TCon c) = c == insName
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
                            functionToCustom (name, tps, _, fDefault) = CustomDecl 
                                (DeclKindCustom $ idFromString "Function") 
                                [
                                    CustomName $ idFromString $ getNameName name, 
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
                        tp = declarationType fname importEnv True
                        fDefault :: CoreDecl
                        fDefault = DeclValue
                            { declName    = idFromString $ constructName fname
                            , declAccess  = public 
                            , declType    = tp
                            , valueValue  = Var $ idFromString "undefined"
                            , declCustoms = toplevelType fname importEnv True
                            }
                    in maybe fDefault updateName (lookup fname defaults)
                

                            