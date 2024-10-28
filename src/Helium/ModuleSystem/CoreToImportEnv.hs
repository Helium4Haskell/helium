{-| Module      :  CoreToImportEnv
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.ModuleSystem.CoreToImportEnv
    ( getImportEnvironment
    , parseFromString
    ) where

import Helium.Lvm.Core.Expr
import qualified Helium.Lvm.Core.Type as Core
import qualified Helium.CodeGeneration.Core.TypeEnvironment as Core
import Helium.Lvm.Core.Utils
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Common.Byte(stringFromBytes)

import Helium.Utils.Utils
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.Parser.ParseLibrary
import Helium.Parser.Lexer(lexer)
import Helium.Parser.Parser(type_, contextAndType)
import Helium.Parser.OperatorTable
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range(makeImportRange, setNameRange)
import Helium.Syntax.UHA_Syntax

import Helium.Top.Top.Types

import Control.Arrow
import Control.Applicative
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Text.PrettyPrint.Leijen (pretty)


nameFromCustoms :: String -> Id -> String -> [Custom] -> Name
nameFromCustoms _ _ conName [] =
    internalError "CoreToImportEnv" "nameFromCustoms"
        ("constructor import without name: " ++ conName)
nameFromCustoms importedInModule importedFromModId conName ( CustomLink parentid (DeclKindCustom ident) : cs) 
    | stringFromId ident == "data" = makeImportName importedInModule importedFromModId parentid
    | otherwise =
        nameFromCustoms importedInModule importedFromModId conName cs
nameFromCustoms importedInModule importedFromModId conName (_ : cs) = nameFromCustoms importedInModule importedFromModId conName cs

parseFromString :: HParser a -> String -> a
parseFromString p string = 
    case lexer [] "CoreToImportEnv" string of 
        Left _ -> internalError "CoreToImportEnv" "parseFromString" ("lex error in " ++ string)
        Right (tokens, _) ->
            case runHParser p "CoreToImportEnv" tokens True {- wait for EOF -} of
                Left e  -> internalError "CoreToImportEnv" "parseFromString" ("parse error in " ++ string ++ ": " ++ show e)
                Right x -> x

typeSchemeFromCore :: Core.Type -> TpScheme
typeSchemeFromCore quantifiedType =
  Quantification (quantors, qmap, Qualification (predicates, fromCore tp))
  where
    -- Convert Debruijn indices (as used in Core) to unique named indices (in Top).
    -- Quantification can only occur at the top level of the type, which makes the
    -- conversion easier. Since foralls cannot occur nested within the type, a type
    -- variable will always have the same index in the Core type. We need to
    -- explicitly find the indices for those variables at the toplevel, when building
    -- the list of quantors. We use 'forallCount' to find the number of foralls. The
    -- first type variable has index `forallCount quantifiedType - 1`.
    splitForalls :: Int -> Core.Type -> ([Int], QuantorMap, Core.Type)
    splitForalls nextTypeVar (Core.TForall (Core.Quantor name) _ t) = (nextTypeVar : idxs, qmap', t')
      where
        (idxs, qmap, t') = splitForalls (nextTypeVar - 1) t
        qmap' = case name of
          Nothing -> qmap
          Just n -> (nextTypeVar, n) : qmap
    splitForalls nextTypeVar (Core.TStrict t) = splitForalls nextTypeVar t -- I think this can be removed. We should test that.
    splitForalls _ t = ([], [], t)

    forallCount :: Core.Type -> Int
    forallCount (Core.TForall _ _ t) = 1 + forallCount t
    forallCount _ = 0

    splitPredicates :: Core.Type -> ([Predicate], Core.Type)
    splitPredicates (Core.TAp (Core.TAp (Core.TCon Core.TConFun) (Core.TAp (Core.TCon (Core.TConTypeClassDictionary className)) instanceType)) t)
      = ( Predicate (stringFromId className) (fromCore instanceType) : predicates, t' )
      where
        (predicates, t') = splitPredicates t
    splitPredicates (Core.TAp (Core.TAp (Core.TCon Core.TConFun) (Core.TStrict (Core.TAp (Core.TCon (Core.TConTypeClassDictionary className)) instanceType))) t)
      = ( Predicate (stringFromId className) (fromCore instanceType) : predicates, t' )
      where
        (predicates, t') = splitPredicates t
    splitPredicates t = ([], t)

    (quantors, qmap, qtype) = splitForalls (forallCount quantifiedType - 1) quantifiedType
    (predicates, tp) = splitPredicates qtype

    fromCore :: Core.Type -> Tp
    fromCore (Core.TCon c) = TCon $ show c
    fromCore (Core.TAp t1 t2) = TApp (fromCore t1) (fromCore t2)
    fromCore (Core.TVar x) = TVar x
    fromCore (Core.TStrict t) = fromCore t
    fromCore (Core.TForall _ _ _) = internalError "CoreToImportEnv" "typeSchemeFromCore" ("Unexpected 'forall' in type scheme. Forall quantifiers may only occur on the top level of a type scheme. Type: " ++ Core.showType [] quantifiedType)

typeSynFromCore :: Core.Type -> (Int, Tps -> Tp)
typeSynFromCore quantifiedType = (typeArgs, \args -> fromCore args tp)
  where
    (typeArgs, tp) = splitForalls quantifiedType
    splitForalls :: Core.Type -> (Int, Core.Type)
    splitForalls (Core.TForall _ _ t) = (count + 1, t)
      where
        (count, t') = splitForalls t
    splitForalls t = (0, t)

    fromCore :: [Tp] -> Core.Type -> Tp
    fromCore args (Core.TCon c) = TCon $ show c
    fromCore args (Core.TAp t1 t2) = TApp (fromCore args t1) (fromCore args t2)
    fromCore args (Core.TVar x) = case args `safeIndex` (typeArgs - 1 - x) of
      Just t -> t
      Nothing -> internalError "CoreToImportEnv" "typeSynFromCore" ("Type variable not found: v$" ++ show x)
    fromCore args (Core.TForall _ _ _) = internalError "CoreToImportEnv" "typeSynFromCore" ("Unexpected 'forall' in type synonym")

-- in compiled Core files types have a kind (e.g. * -> *), 
-- in Helium the have a number indicating the arity
arityFromCustoms :: String -> [Custom] -> Int
arityFromCustoms n [] =
    internalError "CoreToImportEnv" "arityFromCustoms"
        ("type constructor import without kind: " ++ n)
arityFromCustoms _ ( CustomInt arity : _ ) = arity
arityFromCustoms _ ( CustomDecl (DeclKindCustom ident) [CustomBytes bytes] : _ ) 
    | stringFromId ident == "kind" = 
        (length . filter ('*'==) . stringFromBytes) bytes - 1
        -- the number of stars minus 1 is the arity
arityFromCustoms n (_:cs) = arityFromCustoms n cs

makeOperatorTable :: Name -> [Custom] -> [(Name, (Int, Assoc))]
makeOperatorTable oper (CustomInt i : CustomBytes bs : _) =
    let
        associativity =
            case stringFromBytes bs of
                "left"   -> AssocLeft
                "right"  -> AssocRight
                "none"   -> AssocNone
                assocStr -> intErr ("unknown associativity: " ++ assocStr)
        
        intErr = internalError "CoreToImportEnv" "makeOperatorTable"
    in
        if getNameName oper == "-" then
            -- special rule: unary minus has the associativity
            -- and the priority of the infix operator -
            [ (oper, (i, associativity))
            , (intUnaryMinusName, (i, associativity))
            , (floatUnaryMinusName, (i, associativity))
            ]
        else
            [(oper, (i, associativity))]
makeOperatorTable oper _ = 
    internalError "CoreToImportEnv" "makeOperatorTable"
        ("infix decl missing priority or associativity: " ++ show oper)

makeImportName :: String -> Id -> Id -> Name
makeImportName importedInMod importedFromMod n =
    makeImportNameName importedInMod importedFromMod (nameFromId n)

makeImportNameName :: String -> Id -> Name -> Name
makeImportNameName importedInMod importedFromMod n = {-setNameOrigin (stringFromId importedFromMod) $-}
    setNameRange 
        n
        (makeImportRange (idFromString importedInMod) importedFromMod)

makeFullQualifiedImportName:: String -> Name -> Name
makeFullQualifiedImportName origin = 
    let (modu, _) = break (==':') origin 
    in addQualified (getQualifiedFromString modu)

-- Why is the first argument never used?    
insertDictionaries :: String -> CoreDecl -> ImportEnvironment -> ImportEnvironment
insertDictionaries _
        DeclAbstract{ declName    = n
                    , declModule  = Just _
                    , declCustoms = cs
                    } env 
                        | "$dict" `isPrefixOf` stringFromId n =
                            let
                                dictPrefix = "$dict"
                                splitDictName dict = (getClassName dict, getTypeName dict) 
                                getClassName :: String -> String
                                getClassName = takeWhile (/='$')
                                getTypeName :: String -> String
                                getTypeName = drop 1 . dropWhile (/='$')
                                (className, typeName) = splitDictName (drop (length dictPrefix) (stringFromId n))
                                tpVars = zip (selectCustomsString "typeVariable" cs) (map TVar [0..])
                                instancePred = Predicate className (foldl TApp (TCon typeName) (map snd tpVars))
                                superPreds :: Predicates
                                superPreds = map (\x -> Predicate (takeWhile (/='-') x) (fromMaybe (error "Nothing") $ lookup (drop 1 $ dropWhile (/= '-') x) tpVars)) $ selectCustomsString "superInstance" cs
                                addInstance :: Instances -> Instances
                                addInstance = ((instancePred, superPreds):)
                                nClass = M.update (Just . second addInstance) className (classEnvironment env)
                                instanceEnv = instanceEnvironment env
                                nInstanceEnv = M.insert (nameFromString className, foldl TApp (TCon typeName) (map snd tpVars)) 
                                                (map (nameFromString.fst) tpVars, map (\x -> (takeWhile (/= '-') x, drop 1 $ dropWhile (/= '-') x)) (selectCustomsString "superInstance" cs)) instanceEnv

                            in setInstanceEnvironment nInstanceEnv $ setClassEnvironment nClass env

insertDictionaries _ 
                    DeclCustom  { declName    = n
                                , declKind    = DeclKindCustom ident
                                , declCustoms = cs
                                } env
                                | stringFromId ident == "ClassDefinition" = let
                                    tpVar = map (\(CustomDecl _ [CustomName n']) -> nameFromId n') $ selectCustoms "ClassTypeVariables" cs 
                                    functions = map getFunction $ selectCustoms "Function" cs
                                    getFunction :: Custom -> (Name, TpScheme, Bool, HasDefault)
                                    getFunction (CustomDecl _ [
                                            CustomName fname,
                                            CustomBytes tps,
                                            CustomInt n'
                                        ]) = (nameFromString $ stringFromId fname, makeTpSchemeFromType $ parseFromString type_ $ stringFromBytes tps, n' == 1, n' == 1)
                                    getFunction _ = internalError "CoreToImportEnv" "insertDictionaries" 
                                                      ("local function getFunction only defined for CustomDecls")    
                                    className = nameFromId n
                                    classMembers = (tpVar, functions) 
                                in setClassMemberEnvironment (M.insert className classMembers (classMemberEnvironment env)) env
insertDictionaries _ _ env = env

selectCustomsString ::  String -> [Custom] -> [String]
selectCustomsString n cs = map (\(CustomDecl _ [CustomBytes values]) -> stringFromBytes values) $ filter (\(CustomDecl (DeclKindCustom n') _) -> n == stringFromId n') cs

selectCustoms :: String -> [Custom] -> [Custom]
selectCustoms n = filter (\(CustomDecl (DeclKindCustom n') _) -> n == stringFromId n')


getImportEnvironment :: String -> [CoreDecl] -> ImportEnvironment
getImportEnvironment importedInModule decls = foldr (insertDictionaries importedInModule) env1 decls
   where
      transparentNewtypes = setFromList [ name | DeclTypeSynonym{ declName = name, declAccess = Export _, declSynonym = TypeSynonymNewtype } <- decls ]

      -- dataTypeToConstructor is both filled and consumed in locInsert. That works because of laziness.
      (env1, dataTypeToConstructor) = foldr locInsert (emptyEnvironment, []) decls
      dataTypeToConstructorMap = M.fromListWith (++) $ map (\(x,y) -> (x, [y])) dataTypeToConstructor

      locInsert :: CoreDecl -> (ImportEnvironment, [(Name, Name)]) -> (ImportEnvironment, [(Name, Name)])
      locInsert decl (env, dataTypeMapping) =
         case decl of 
         
           -- functions
           DeclAbstract { declAccess  = Export n
                        , declModule  = Just importedFromModId
                        , declType    = tp
                        , declCustoms = cs
                        } ->
                if "$dict" `isPrefixOf` (stringFromId n) then (env, dataTypeMapping) else
                    ( addType
                        (makeImportName importedInModule importedFromModId n)
                        (typeSchemeFromCore tp)
                        env
                    , dataTypeMapping
                    )

           -- functions from non-core/non-lvm libraries and lvm-instructions
           DeclExtern { declAccess  = Export n
                      , declModule  = Just importedFromModId
                      , declCustoms = cs
                      , declType    = tp
                      } ->
              ( addType
                 (makeImportName importedInModule importedFromModId n)
                 (typeSchemeFromCore tp)
                 env
              , dataTypeMapping
              )

           -- constructors
           DeclCon { declAccess  = Export n
                   , declModule  = Just importedFromModId
                   , declCustoms = cs
                   , declFields  = fs
                   , declType    = tp
                   } ->
                let
                    locName = stringFromId n
                    idToName = makeImportName importedInModule importedFromModId
                    constrName = idToName n
                    Core.FunctionType args _ = Core.extractFunctionTypeNoSynonyms tp
                    fields = zipWith (\(Field n) arg -> (idToName n, Core.typeIsStrict tp)) fs args
                    isTypeClass = "Dict$" `isPrefixOf` stringFromId n
                    typeName = if isTypeClass
                        then makeImportNameName importedInModule importedFromModId
                            (nameFromString $ "Dict$" ++ drop 5 locName)
                        else nameFromCustoms importedInModule importedFromModId locName cs -- TODO: Use tp to derive data type name
                in if isTypeClass then
                    ( env, dataTypeMapping)
                   else
                    ( addRecordFields constrName fields
                       $ addValueConstructor
                           constrName
                           (typeSchemeFromCore tp)
                           typeName
                           (idFromName typeName `elemSet` transparentNewtypes)
                           env
                    , (typeName, constrName) : dataTypeMapping
                    )

           -- type constructor import
           DeclCustom { declName    = fullname
                      , declAccess  = Export n
                      , declModule  = Just importedFromModId
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs 
                      } 
                      | stringFromId ident == "data" ->
              let typename = makeImportName importedInModule importedFromModId n
                  constructors = case M.lookup (nameFromId fullname) dataTypeToConstructorMap of
                    Nothing -> Just [] -- Data type has no constructors
                    Just cs -> Just cs
                  pair = (arityFromCustoms (stringFromId n) cs, nameFromId fullname, constructors)
              in ( addTypeConstructor typename pair env
                 , dataTypeMapping
                 )

           -- newtype declarations
           -- note that this only creates the data type, the constructor is defined
           -- in a DeclCon
           DeclTypeSynonym { declName = fullname
                           , declAccess = Export n
                           , declModule = Just importedFromModId
                           , declSynonym = TypeSynonymNewtype
                           , declCustoms = cs
                           } ->
              let typename = makeImportName importedInModule importedFromModId n
                  constructors = case M.lookup (nameFromId fullname) dataTypeToConstructorMap of
                    Nothing -> Just []
                    Just cs -> Just cs
                  pair     = (arityFromCustoms (stringFromId n) cs, nameFromId fullname, constructors)
              in ( addTypeConstructor typename pair env
                 , dataTypeMapping
                 )

           -- type synonym declarations
           -- important: a type synonym also introduces a new type constructor!
           DeclTypeSynonym { declName = fullname
                           , declAccess = Export n
                           , declModule = Just importedFromModId
                           , declSynonym = TypeSynonymAlias
                           , declType = tp
                           , declCustoms = cs
                           } ->
              let typename = makeImportName importedInModule importedFromModId n
                  pair = typeSynFromCore tp
                  pair2 = (fst pair, nameFromId fullname, Nothing)
                  pair3 = (fst pair, snd pair, nameFromId fullname)
              in ( addTypeSynonym (nameFromId fullname) pair3 $ addTypeConstructor typename pair2 env
                 , dataTypeMapping
                 )

           -- infix decls
           DeclCustom { declName    = n
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "infix" ->
              ( flip (foldr (uncurry addOperator)) (makeOperatorTable (nameFromId n) cs) env
              , dataTypeMapping
              )

           -- typing strategies
           DeclCustom { declName    = _
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "strategy" ->
              let (CustomDecl _  [CustomBytes bytes]) = head cs
                  text = stringFromBytes bytes
              in case reads text of 
                    [(rule, [])] -> ( addTypingStrategies rule env, dataTypeMapping )
                    _ -> intErr "Could not parse typing strategy from core file"
            
           -- class decls
           DeclCustom { declName    = qualifiedId
                      , declAccess  = Export n
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "ClassDefinition" -> 
                        let 
                            selectCustom :: String -> [Custom] -> [Custom]
                            selectCustom s = filter (isCustom s)
                            isCustom :: String -> Custom -> Bool
                            isCustom s (CustomDecl (DeclKindCustom cid) _) = stringFromId cid == s 
                            isCustom _ _ = False
                            getTypeVariable :: Custom -> Names
                            getTypeVariable (CustomDecl _ [CustomName tn]) = [nameFromString $ stringFromId tn]
                            getTypeVariable _ = internalError "CoreToImportEnv" "getImportEnvironment" 
                                                      ("local function getTypeVariable only defined for CustomDecls")                                
                            className = nameFromString $ stringFromId n
                            classVariables = getTypeVariable $ head (selectCustom "ClassTypeVariables" cs)
                            superClasses = selectCustom "SuperClass" cs
                            qualifiedName = nameFromId qualifiedId
                            addClass :: Name -> [Custom] -> ImportEnvironment -> ImportEnvironment
                            addClass clName superCls env = let
                                    classEnv = classEnvironment env
                                    superClassLabels = map superClassToLabel superCls
                                    superClassToLabel :: Custom -> String
                                    superClassToLabel (CustomDecl _ [CustomName n']) = stringFromId n'
                                    superClassToLabel _ = internalError "CoreToImportEnv" "getImportEnvironment" "local function superClassToLabel only defined for CustomDecls"    
                                    nClassEnv = M.insert (getNameName clName) (superClassLabels, []) classEnv
                                in setClassEnvironment nClassEnv env
                            getFunction :: Custom -> (Name, TpScheme, Bool, HasDefault)
                            getFunction (CustomDecl _ [
                                    CustomName fname,
                                    CustomBytes tps,
                                    CustomInt n'
                                ]) = (nameFromString $ stringFromId fname, makeTpSchemeFromType $ parseFromString type_ $ stringFromBytes tps, False, n' == 1)
                            getFunction _ = internalError "CoreToImportEnv" "getImportEnvironment" "local function getFunction only defined for CustomDecls"    
                            classMembers = (classVariables, map getFunction $ selectCustom "Function" cs)
                        in ( addClassName className qualifiedName $ addClass qualifiedName superClasses $ addClassMember className classMembers env
                           , dataTypeMapping
                           )
           DeclAbstract{ declName = n } ->
              intErr  ("don't know how to handle declared DeclAbstract: " ++ stringFromId n)
           DeclExtern  { declName = n } ->
              intErr  ("don't know how to handle declared DeclExtern: "   ++ stringFromId n)
           DeclCon     { declName = n } ->
              intErr  ("don't know how to handle declared DeclCon: "      ++ stringFromId n)
           DeclCustom  { declName = n } ->
              intErr  ("don't know how to handle DeclCustom: "            ++ stringFromId n)
           DeclValue   { declName = n } ->
              intErr  ("don't know how to handle DeclValue: "             ++ stringFromId n)

      intErr = internalError "CoreToImportEnv" "getImportEnvironment"
