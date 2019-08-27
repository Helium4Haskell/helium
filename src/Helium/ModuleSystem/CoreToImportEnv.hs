{-| Module      :  CoreToImportEnv
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.ModuleSystem.CoreToImportEnv(getImportEnvironment, originFromCustoms) where

import Lvm.Core.Expr
import Lvm.Core.Utils
import Lvm.Common.Id
import Lvm.Common.Byte(stringFromBytes)

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

import Top.Types

import Control.Arrow
import Data.List
import Data.Maybe
import qualified Data.Map as M

typeDictFromCustoms :: String -> [Custom] -> TpScheme
typeDictFromCustoms n [] = internalError "CoreToImportEnv" "typeDictFromCustoms"
                ("function import without type: " ++ n)
typeDictFromCustoms n ( CustomDecl (DeclKindCustom ident) [CustomBytes bytes] : cs) 
    | stringFromId ident == "type" =
        let 
            string = filter (/= '!') (stringFromBytes bytes) 
            -- dictName = takeWhile (/= '$') string
            dictType = drop 1 $ dropWhile (/= '$') string
        in makeTpSchemeFromType (parseFromString contextAndType dictType)
    | otherwise = typeDictFromCustoms n cs
typeDictFromCustoms _ _ = internalError "CoreToImportEnv" "typeDictFromCustoms"
                ("Can only convert CustomDecls to typeDict")

typeFromCustoms :: String -> [Custom] -> TpScheme
typeFromCustoms n [] =
    internalError "CoreToImportEnv" "typeFromCustoms"
        ("function import without type: " ++ n)
typeFromCustoms n ( CustomDecl (DeclKindCustom ident) [CustomBytes bytes] : cs) 
    | stringFromId ident == "type" =
        let string = filter (/= '!') (stringFromBytes bytes) 
        in makeTpSchemeFromType (parseFromString contextAndType string)
    | otherwise =
        typeFromCustoms n cs
typeFromCustoms _ _ = error "Pattern match failure in ModuleSystem.CoreToImportEnv.typeFromCustoms"

nameFromCustoms :: String -> Id -> String -> [Custom] -> Name
nameFromCustoms _ _ conName [] =
    internalError "CoreToImportEnv" "nameFromCustoms"
        ("constructor import without name: " ++ conName)
nameFromCustoms importedInModule importedFromModId conName ( CustomLink parentid (DeclKindCustom ident) : cs) 
    | stringFromId ident == "data" = makeImportName importedInModule importedFromModId "" parentid
    | otherwise =
        nameFromCustoms importedInModule importedFromModId conName cs
nameFromCustoms importedInModule importedFromModId conName (_ : cs) = nameFromCustoms importedInModule importedFromModId conName cs

originFromCustoms :: [Custom] -> String
originFromCustoms [] =
    internalError "CoreToImportEnv" "originFromCustoms" 
        ("something imported without an origin, maybe you should recompile (base) libraries or update lvm.")
originFromCustoms ( CustomDecl (DeclKindCustom ident) [CustomName originid] : cs)
    | stringFromId ident == "origin" = stringFromId originid
    | otherwise                      = originFromCustoms cs
originFromCustoms (_ : cs) = originFromCustoms cs

parseFromString :: HParser a -> String -> a
parseFromString p string = 
    case lexer [] "CoreToImportEnv" string of 
        Left _ -> internalError "CoreToImportEnv" "parseFromString" ("lex error in " ++ string)
        Right (tokens, _) ->
            case runHParser p "CoreToImportEnv" tokens True {- wait for EOF -} of
                Left _  -> internalError "CoreToImportEnv" "parseFromString" ("parse error in " ++ string)
                Right x -> x

typeSynFromCustoms :: String -> [Custom] -> (Int, Tps -> Tp) -- !!! yuck
typeSynFromCustoms n (CustomBytes bs:cs) =
    let
        typeSynDecl = stringFromBytes bs
        -- (too?) simple parser; works because type variables in synonym decls are renamed to 1 letter
        ids         = ( map (\x -> nameFromString [x])
                      . filter    (' '/=)
                      . takeWhile ('='/=)
                      . drop (length n + 1)
                      )
                        typeSynDecl
        rhsType     = ( drop 1
                      . dropWhile ('='/=)
                      )
                        typeSynDecl
    in
        ( arityFromCustoms n cs
        , \ts -> makeTpFromType (zip ids ts) (parseFromString type_ rhsType)
        )
typeSynFromCustoms n _ =
    internalError "CoreToImportEnv" "typeSynFromCustoms"
        ("type synonym import missing definition: " ++ n)

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

makeImportName :: String -> Id -> String -> Id -> Name
makeImportName importedInMod importedFromMod origin n =
    makeImportNameName importedInMod importedFromMod origin (nameFromId n)

makeImportNameName :: String -> Id -> String -> Name -> Name
makeImportNameName importedInMod importedFromMod origin n = setNameOrigin origin $
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
                    , declAccess  = Imported{importModule = _}
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
getImportEnvironment importedInModule decls = foldr (insertDictionaries importedInModule) (foldr locInsert emptyEnvironment decls) decls
   where
      locInsert :: CoreDecl -> (ImportEnvironment -> ImportEnvironment) 
      locInsert decl =
         case decl of 
         
           -- functions
           DeclAbstract { declName    = n
                        , declAccess  = Imported{importModule = importedFromModId}
                        , declCustoms = cs
                        } ->
                \env ->
                    let
                        nEnv = addType
                                    (makeImportName importedInModule importedFromModId (originFromCustoms cs) n)
                                    ((  
                                        if "$dict" `isInfixOf` (stringFromId n) then 
                                            typeDictFromCustoms
                                        else 
                                            typeFromCustoms) 
                                        (stringFromId n) cs) env
                        
                    in nEnv 
                
          
           -- functions from non-core/non-lvm libraries and lvm-instructions
           DeclExtern { declName = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declCustoms = cs
                      } ->
              addType
                 (makeImportName importedInModule importedFromModId (originFromCustoms cs) n)
                 (typeFromCustoms (stringFromId n) cs)
            
           -- constructors
           DeclCon { declName    = n
                   , declAccess  = Imported{importModule = importedFromModId}
                   , declCustoms = cs
                   } -> let locName    = stringFromId n
                            makeName x = makeImportName importedInModule importedFromModId (originFromCustoms cs) x
                            typename   = if "Dict" `isPrefixOf` locName 
                                         then makeImportNameName importedInModule importedFromModId "" 
                                                (nameFromString $ "Dict$" ++ drop 4 locName)
                                         else nameFromCustoms importedInModule importedFromModId locName cs 
                        in
              addValueConstructor
                (makeName n)
                (typeFromCustoms (stringFromId n) cs)
                typename

           -- type constructor import
           DeclCustom { declName    = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs 
                      } 
                      | stringFromId ident == "data" ->
              let origin = originFromCustoms cs
                  typename = makeImportName importedInModule importedFromModId origin n
                  fullname = makeFullQualifiedImportName origin typename
                  pair     = (arityFromCustoms (stringFromId n) cs, fullname)
              in addTypeConstructor typename pair
                 
            
           -- type synonym declarations
           -- important: a type synonym also introduces a new type constructor!
           DeclCustom { declName    = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "typedecl" ->
              let origin = originFromCustoms cs
                  typename = makeImportName importedInModule importedFromModId origin n
                  fullname = makeFullQualifiedImportName origin typename
                  pair = typeSynFromCustoms (stringFromId n) cs
                  pair2 = (fst pair, fullname)
                  pair3 = (fst pair, snd pair, fullname)
              in addTypeSynonym fullname pair3 . addTypeConstructor typename pair2
                             
           -- infix decls
           DeclCustom { declName    = n
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "infix" ->
              flip (foldr (uncurry addOperator)) (makeOperatorTable (nameFromId n) cs)

           -- typing strategies
           DeclCustom { declName    = _
                      , declKind    = DeclKindCustom ident
                      , declCustoms = cs
                      }
                      | stringFromId ident == "strategy" ->
              let (CustomDecl _  [CustomBytes bytes]) = head cs
                  text = stringFromBytes bytes
              in case reads text of 
                    [(rule, [])] -> addTypingStrategies rule
                    _ -> intErr "Could not parse typing strategy from core file"
            
           -- class decls
           DeclCustom { declName    = n
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
                            origin = originFromCustoms cs
                            originModule = takeWhile (/=':') origin
                            qualifiedName = nameFromString $ originModule ++ "." ++ unQualifyString (stringFromId n)
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
                        in addClassName className qualifiedName . addClass qualifiedName superClasses . addClassMember className classMembers 
           -- !!! Print importedFromModId from "declAccess = Imported{importModule = importedFromModId}" as well
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
           DeclImport  { declName = n } ->
              intErr  ("don't know how to handle DeclImport: "            ++ stringFromId n)
        
      intErr = internalError "CoreToImportEnv" "getImportEnvironment"