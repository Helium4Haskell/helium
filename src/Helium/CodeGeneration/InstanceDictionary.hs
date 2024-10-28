module Helium.CodeGeneration.InstanceDictionary where

import Helium.Lvm.Core.Expr
import qualified Helium.Lvm.Core.Type as Core
import Helium.Lvm.Core.Module
import Helium.Lvm.Core.Utils (createFunction)

import Helium.Lvm.Common.Id
import Helium.Lvm.Common.Byte

import Helium.CodeGeneration.CoreUtils
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils
import Helium.Top.Top.Types
import Control.Arrow

import qualified Data.Map as M

import Data.Maybe
import Data.List

import Text.PrettyPrint.Leijen (pretty)

type DictLabel = String

constructFunctionMap :: ImportEnvironment -> Int -> Name -> [(Name, Int, DictLabel, Core.Type)]
constructFunctionMap env nrOfSuperclasses name =
    let
        err = error $ "Invalid class name " ++ show name
        f i (n, t, _, _) = (n, i, "func$" ++ getNameName n, toCoreType emptyQuantors t)

    in maybe err (zipWith f [nrOfSuperclasses..] . snd) $ M.lookup name (classMemberEnvironment env)

typeClassType :: Id -> Core.Type
typeClassType n = Core.TCon $ Core.TConTypeClassDictionary n

constructSuperClassMap :: ImportEnvironment -> String -> Core.Type -> [(String, Int, DictLabel, Core.Type)]
constructSuperClassMap env name tp =
    let
        err = error $ "Invalid class name " ++ show name ++ " in " ++ show (classEnvironment env)
        f :: Class -> [(String, Int, DictLabel, Core.Type)]
        f (ns, _) = zipWith (\n i -> (n, i, "superC$" ++ n, Core.TAp (typeClassType $ idFromString n) tp)) ns [0..]
    in maybe err f (M.lookup name $ classEnvironment env)

constructorType :: String -> [Core.Type] -> [Core.Type] -> Core.Type -> Core.Type
constructorType typeVar fieldsSuper fieldsMembers classType =
    Core.TForall (Core.Quantor $ Just typeVar) Core.KStar $ Core.typeFunction fields' classType
    where
        fields' = fieldsSuper ++ map (addDictArgument 0 . instantiateClassVar) fieldsMembers

        -- Adds the dictionary argument to the types of the fields of the type class
        addDictArgument :: Int -> Core.Type -> Core.Type
        addDictArgument idx (Core.TForall quantor kind tp) = Core.TForall quantor kind $ addDictArgument (idx + 1) tp
        addDictArgument idx tp = Core.TAp (Core.TAp (Core.TCon Core.TConFun) $ Core.typeWeaken idx classType) tp

        -- We use 0 for the type variable for the argument of the type class.
        -- The types for the fields may need to be updated for this.
        -- We increment all other type variables with 1 (such that 0 is not used)
        -- and replace the type variable for the type class with 0.
        instantiateClassVar :: Core.Type -> Core.Type
        instantiateClassVar = go 0 . Core.typeWeaken 1
          where
            go idx t1@(Core.TForall (Core.Quantor name) k t2)
              | name == Just typeVar = Core.typeApply t1 (Core.TVar idx)
              | otherwise = Core.TForall (Core.Quantor name) k $ go (idx + 1) t2
            go _ _ = internalError "InstanceDictionary" "constructorType" "Type argument for type class not found in signature of field."

-- data DictEq a = DictEq (Eq a => a -> a -> Bool) (forall b . Eq a => b -> a -> Bool)

--returns for every function in a class the function that retrieves that class from a dictionary
classFunctions :: [String] -> TypeInferenceOutput -> String -> String -> [(Name, Int, DictLabel, Core.Type)] -> [CoreDecl]
classFunctions mod typeOutput className typeVar combinedNames = [DeclCon -- Declare the constructor for the dictionary
                                                    { declName = dictName
                                                    , declAccess  = Export dictName
                                                    , declModule  = Nothing
                                                    , declType    = constructorType typeVar (map (\(_, _, _, t) -> t) superclasses) (map (\(_, _, _, t) -> t) combinedNames) classType
                                                    , declCustoms =
                                                        [ CustomLink dictName (DeclKindCustom $ idFromString "data") ]
                                                    , declFields = []
                                                    }
                                                   ,DeclCustom -- Declare the data type for the dictionary
                                                    { declName = dictName
                                                    , declAccess = Export dictName
                                                    , declModule = Nothing
                                                    , declKind = DeclKindCustom (idFromString "data")
                                                    , declCustoms = [ CustomInt 1 ]} -- 1 type argument
                                                   ]
                                                    ++ map superDict superclasses ++ concatMap classFunction combinedNames
        where
            typeArg = Core.TVar 0
            classType = Core.TAp (typeClassType $ idFromString className) typeArg
            dictName = idFromString ("Dict$" ++ className)
            labels = map thd4 superclasses ++ map thd4 combinedNames
            superclasses = constructSuperClassMap (importEnv typeOutput) className typeArg
            superDict :: (String, Int, DictLabel, Core.Type) -> CoreDecl
            superDict (superName, _, label, t) =
                let dictParam = idFromString "dict"
                    (declValue, declType) = createFunction [Core.Quantor $ Just typeVar] [Variable dictParam classType] body t
                    body = Let (Strict $ Bind (Variable dictParam classType) (Var dictParam))
                        $ Match dictParam
                            [
                                Alt (PatCon (ConId $ idFromString ("Dict$" ++ className)) [typeArg] (map idFromString labels))
                                    (Var $ idFromString label)

                            ]
                    valName = idFromString $ "$get" ++ superName ++ "$" ++ className
                    val = DeclValue
                        { declName    = valName
                        , declAccess  = Export valName
                        , declModule  = Nothing
                        , declType    = declType
                        , valueValue  = declValue
                        , declCustoms = []
                        }
                in val
            classFunction :: (Name, Int, DictLabel, Core.Type) -> [CoreDecl]
            classFunction (name, _, label, _) =
                let dictParam = idFromString "dict"
                    quantors =
                        drop 1
                        $ unfoldr
                            (\tp -> case tp of
                                Core.TForall quantor _ t -> Just (quantor, t)
                                _ -> Nothing
                            )
                            declType
                    declType = snd $ declarationType typeOutput TCCNone emptyQuantors name
                    tvars = reverse [0..length quantors - 1]
                    typeArg' = Core.TVar $ length quantors
                    val = DeclValue
                        { declName    = idFromName $ addQualified mod name
                        , declAccess  = Export $ idFromString $ getNameName name
                        , declModule  = Nothing
                        , declType    = declType
                        , valueValue  = Forall (Core.Quantor $ Just typeVar) Core.KStar
                            $ flip (foldr (\q e -> Forall q Core.KStar e)) quantors
                            $ Lam True (Variable dictParam $ Core.typeWeaken (length quantors) classType)
                            $ Match dictParam
                                [
                                    Alt (PatCon (ConId $ idFromString ("Dict$" ++ className)) [typeArg'] (map idFromString labels))
                                        (Ap (foldl (\e idx -> ApType e (Core.TVar idx)) (Var $ idFromString label) tvars) $ Var dictParam)
                                ]
                        , declCustoms = []
                        }
                in  [val]

combineDeclIndex :: [(Name, Int, DictLabel, Core.Type)] -> [(Name, CoreDecl)] -> [(DictLabel, Name, Core.Type, Maybe CoreDecl)]
combineDeclIndex ls [] = map (\(n, _, l, t) -> (l, n, t, Nothing)) ls
combineDeclIndex [] _ = error "Inconsistent mapping"
combineDeclIndex names decls = map (\(name, _, label, t) -> (label, name, t, lookup name decls)) names


--returns a dictionary with specific implementations for every instance
constructDictionary :: TypeInferenceOutput -> [(String, Name)] -> [(Name, Int, DictLabel, Core.Type)] -> [(Name, CoreDecl)] -> Name -> String -> [(Name, Int)] -> Core.Type -> [Custom] -> CoreDecl
constructDictionary typeOutput instanceSuperClass combinedNames whereDecls className insName typeVariables' insType origin =
    DeclValue
    { declName    = name
    , declAccess  = Export name
    , declModule  = Nothing
    , declType    = declType
    , valueValue  = declValue
    , declCustoms =  map (custom "typeVariable" . getNameName . fst) typeVariables
                ++ map (\(superName, superVar) -> custom "superInstance" $ superName ++ "-" ++ getNameName superVar) instanceSuperClass
                ++ origin
    }
    where
        name = idFromString ("$dict" ++ getNameName className ++ "$" ++ insName)
        typeVariables = map (\(name, idx) -> let TVar beta = lookupBeta idx typeOutput in (name, beta)) typeVariables'
        (declValue, declType) = createFunction quantors instanceSuperClassVariables dict dictType
        quantors = map (\(name, idx) -> (Core.Quantor $ Just $ getNameName name)) typeVariables
        functions = combineDeclIndex combinedNames whereDecls
        idP = idFromString "index"
        superClasses = constructSuperClassMap (importEnv typeOutput) (getNameName className) insType
        dict = Let (Rec binds) $ Var $ idFromString "dict"
        binds = map makeBindSuper superClasses ++ map makeBindFunc functions ++ [dictCon]
        labels = map (\(_, _, l, _)->l) superClasses ++ map (\(l, _, _, _)->l) functions
        findTVar :: Name -> Int
        findTVar name = maybe (error "constructDictionary: Type variable not found in a type class instance declaration") (\i -> length typeVariables' - 1 - i) $ elemIndex name $ map fst typeVariables'
        instanceSuperClassVariables = map (\(className, tvar) -> Variable (idFromString $ "$instanceDict" ++ className ++ "$" ++ getNameName tvar) $ Core.TAp (typeClassType $ idFromString className) $ Core.TVar $ findTVar tvar) instanceSuperClass
        makeBindSuper :: (String, Int, DictLabel, Core.Type) -> Bind
        makeBindSuper (cName, _, label, t) = let
                parentMapping :: [(String, String)]
                parentMapping = map (getNameName *** getNameName) $ getTVMapping (importEnv typeOutput) (getNameName className) insName cName
                resolveSuperInstance :: (String, String) -> Expr
                resolveSuperInstance (n, var)
                        -- check if the required class is already an existing parameter
                        | (n, fst $ fromJust (find (\x -> snd x == var) parentMapping)) `elem` map (\(a, b) -> (a, getNameName b)) instanceSuperClass && n == cName= let
                                    Just tvar = find (\(_, cn) -> cn == var) parentMapping
                                in
                                    Var (idFromString $ "$instanceDict" ++ cName ++ "$" ++ fst tvar)
                        | otherwise = let
                                -- get all the available super classes
                                repInstanceSuperClass = filter (\(_, v) -> getNameName v == rVar) instanceSuperClass
                                rVar = fst $ fromJust $find (\(_, cn) -> cn == var) parentMapping
                                shortestPath :: [[a]] -> [a]
                                shortestPath [x] = x
                                shortestPath (x:xs) = let
                                    sp = shortestPath xs
                                    in if length sp < length x then sp else x
                                shortestPath _ = error "Path should not be empty in shortestPath in InstanceDictionary.hs"
                                -- construct the path from a sub class to it's super class, e.g. ["Num", "Ord", "Eq"]
                                constructPath :: String -> String -> [[String]]
                                constructPath from to
                                    | from == to = [[to]]
                                    | otherwise = let
                                            superClasses = getClassSuperClasses (importEnv typeOutput) from
                                            paths :: [[[String]]]
                                            paths = map (`constructPath` to) superClasses
                                            sPaths :: [[String]]
                                            sPaths = map (shortestPath. filter (\x -> last x == to)) paths
                                        in map (from:) sPaths
                                sPath = shortestPath (constructPath n cName)
                                combinePath :: String -> [String] -> [(String, String)]
                                combinePath _ [] = []
                                combinePath first (x:xs) = (first, x) : combinePath x xs
                                combinedPath = shortestPath $ map (\(source, _) -> filter (uncurry (/=)) $ combinePath source sPath) repInstanceSuperClass
                            in
                                foldl
                                    (\expr (sub, super) -> Ap (ApType (Var $ idFromString $ "$get" ++ super ++ "$" ++ sub) $ Core.TVar $ findTVar $ nameFromString var) expr)
                                    (Var (idFromString $ "$instanceDict" ++ fst (head combinedPath) ++ "$" ++ rVar))
                                    combinedPath

                instanceSuperClasses = getInstanceSuperClasses (importEnv typeOutput) cName insName

                baseInstanceFn =
                    foldl
                        (\expr idx -> ApType expr (Core.TVar idx))
                        (Var (idFromString ("$dict" ++ cName ++ "$" ++ insName)))
                        $ reverse $ zipWith const [0..] typeVariables
                baseInstance = foldl Ap baseInstanceFn $ map resolveSuperInstance instanceSuperClasses

            in Bind (Variable (idFromString label) t) baseInstance

        makeBindFunc :: (DictLabel, Name, Core.Type, Maybe CoreDecl) -> Bind
        makeBindFunc (label, name, t, fdecl) = let
            (_, tp) = declarationType typeOutput (TCCInstance (idFromString insName) insType) emptyQuantors name
                -- declarationType :: M.Map NameWithRange Top.TpScheme -> ImportEnvironment -> TypeClassContext -> Name -> (Top.TpScheme, Core.Type)
            undefinedFunc = ApType (Var $ idFromString ("default$" ++ getNameName className ++ "$" ++ getNameName name)) insType
            func = maybe undefinedFunc getCoreValue fdecl
            in Bind (Variable (idFromString label) tp) func
        dictCon = Bind (Variable (idFromString "dict") dictType) (
                foldl Ap (Con (ConId $ idFromString ("Dict$" ++ getNameName className)) `ApType` insType) $ map (Var . idFromString) labels
            )
        dictType = Core.TAp (typeClassType $ idFromName className) insType

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

convertDictionaries :: TypeInferenceOutput -> Name -> [Name] -> [(Name, CoreDecl)] -> [CoreDecl]
convertDictionaries typeOutput className functions defaults = map makeFunction functions
            where
                constructName :: Name -> String
                constructName fname = "default$" ++ getNameName className ++ "$" ++ getNameName fname
                makeFunction :: Name -> CoreDecl
                makeFunction fname =
                    let
                        fid = idFromString $ constructName fname
                        updateName :: CoreDecl -> CoreDecl
                        updateName fdecl = fdecl{
                            declName = fid
                        }
                        tp = snd $ declarationType typeOutput TCCNone emptyQuantors fname
                        fDefault :: CoreDecl
                        fDefault = DeclValue
                            { declName    = fid
                            , declAccess  = Export fid
                            , declModule  = Nothing
                            , declType    = tp
                            , valueValue  = ApType (Var (idFromString "undefined")) tp
                            , declCustoms = []
                            }
                    in maybe fDefault updateName (lookup fname defaults)
