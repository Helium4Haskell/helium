module CoreToImportEnv(getImportEnvironment) where

import UHA_Syntax(Name(..), Range(..), Position(..))
import UHA_Range(makeImportRange, setNameRange)
import UHA_Utils
import OperatorTable
import ParseLibrary(intUnaryMinusName, floatUnaryMinusName)
import Types
import Utils
import Core
import Byte
import Id
import List(nubBy)
import Char
import qualified CoreParse as C
import ImportEnvironment

typeFromCustoms :: String -> [Custom] -> TpScheme
typeFromCustoms n [] =
    internalError "CoreToImportEnv" "typeFromCustoms"
        ("function import without type: " ++ n)
typeFromCustoms n ( CustomDecl (DeclKindCustom id) [CustomBytes bytes] : cs) 
    | stringFromId id == "type" =
        stringToTpScheme n (Byte.stringFromBytes bytes) Nothing
    | otherwise =
        typeFromCustoms n cs

typeSynFromCustoms :: String -> [Custom] -> (Int, Tps -> Tp)
typeSynFromCustoms n (CustomBytes bs:cs) =
    let
        typeSynDecl = Byte.stringFromBytes bs
        -- (too?) simple parser
        ids         = ( map (\x -> idFromString [x])
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
        , \ts -> stringToType n rhsType (Just (zip ids ts))
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
arityFromCustoms n ( CustomInt arity : _ ) = arity
arityFromCustoms n ( CustomDecl (DeclKindCustom id) [CustomBytes bytes] : cs ) 
    | stringFromId id == "kind" = 
        (length . filter ('*'==) . Byte.stringFromBytes) bytes - 1
        -- the number of stars minus 1 is the arity
arityFromCustoms n (_:cs) = arityFromCustoms n cs

makeOperatorTable :: Name -> [Custom] -> [(Name, (Int, Assoc))]
makeOperatorTable op (Core.CustomInt i : Core.CustomBytes bs : cs) =
    let
        assoc =
            case stringFromBytes bs of
                "left"   -> AssocLeft
                "right"  -> AssocRight
                "none"   -> AssocNone
                assocStr -> intErr ("unknown associativity: " ++ assocStr)
        
        intErr = internalError "CoreToImportEnv" "makeOperatorTable"
    in
        if getNameName op == "-" then
            -- special rule: unary minus has the assoc
            -- and the priority of the infix operator -
            [ (op, (i, assoc))
            , (intUnaryMinusName, (i, assoc))
            , (floatUnaryMinusName, (i, assoc))
            ]
        else
            [(op, (i, assoc))]
makeOperatorTable op cs = 
    internalError "CoreToImportEnv" "makeOperatorTable"
        ("infix decl missing priority or associativity: " ++ show op)

makeImportName :: String -> Id -> Id -> Name
makeImportName importedInMod importedFromMod n =
    setNameRange 
        (nameFromId n)
        (makeImportRange (idFromString importedInMod) importedFromMod)

getImportEnvironment :: String -> [CoreDecl] -> ImportEnvironment
getImportEnvironment importedInModule = foldr insert emptyEnvironment
   where
      insert decl = 
         case decl of 
         
           -- functions
           DeclAbstract { declName    = n
                        , declAccess  = Imported{importModule = importedFromModId}
                        , declCustoms = cs
                        } ->
              addType
                 (makeImportName importedInModule importedFromModId n)
                 (typeFromCustoms (stringFromId n) cs)
          
           -- functions from non-core/non-lvm libraries and lvm-instructions
           DeclExtern { declName = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declCustoms = cs
                      } ->
              addType
                 (makeImportName importedInModule importedFromModId n)
                 (typeFromCustoms (stringFromId n) cs)
            
           -- constructors
           DeclCon { declName    = n
                   , declAccess  = Imported{importModule = importedFromModId}
                   , declArity   = arity
                   , declCustoms = cs
                   } ->
              addValueConstructor
                (makeImportName importedInModule importedFromModId n)
                (typeFromCustoms (stringFromId n) cs)

           -- type constructor import
           DeclCustom { declName    = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declKind    = DeclKindCustom id
                      , declCustoms = cs 
                      } 
                      | stringFromId id == "data" ->
              addTypeConstructor
                 (makeImportName importedInModule importedFromModId n)
                 (arityFromCustoms (stringFromId n) cs)
            
           -- type synonym declarations
           -- important: a type synonym also introduces a new type constructor!
           DeclCustom { declName    = n
                      , declAccess  = Imported{importModule = importedFromModId}
                      , declKind    = DeclKindCustom id
                      , declCustoms = cs
                      }
                      | stringFromId id == "typedecl" ->
              let name = makeImportName importedInModule importedFromModId n
                  pair = typeSynFromCustoms (stringFromId n) cs
              in addTypeSynonym name pair . addTypeConstructor name (fst pair)
                             
           -- infix decls
           DeclCustom { declName    = n
                      , declKind    = DeclKindCustom id
                      , declCustoms = cs
                      }
                      | stringFromId id == "infix" ->
              flip (foldr (uncurry addOperator)) (makeOperatorTable (nameFromId n) cs)

           -- typing strategies
           DeclCustom { declName    = _
                      , declKind    = DeclKindCustom id
                      , declCustoms = cs
                      }
                      | stringFromId id == "strategy" ->
              let (CustomDecl _  [CustomBytes bytes]) = head cs
                  text = stringFromBytes bytes
              in addTypingStrategies (read text)

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
           _ ->
              intErr "unknown kind of declaration in import declarations"
        
      intErr = internalError "CoreToImportEnv" "getImportEnvironment"
         
stringToType :: String -> String -> Maybe [(Id, Tp)] -> Tp
stringToType n typeStr table =
    let
        TpScheme _ _ _ tp = stringToTpScheme n typeStr table
    in
        tp
-- Convert a core type (which is just a string) to Bastiaan's TpScheme type.
-- The function name n is used only for debugging and error messages.
stringToTpScheme :: String -> String -> Maybe [(Id, Tp)] -> TpScheme
stringToTpScheme n typeStr table =
    let coreType =
            (C.coreParseType "Compiler bug in CoreToImportEnv.stringToType" typeStr) -- !!! als je dit aanzet zie je veel imports van String ?? (trace (n ++ " :: " ++ typeStr) typeStr))
        (ids, baseCoreType) =
            splitForalls coreType
        realTable =
            case table of
                Nothing -> zip ids (map TVar [0..])
                Just t  -> t
        tpScheme =
            coreTypeToTpScheme n realTable baseCoreType
    in
        -- trace (n ++ " :: " ++ show coreType ++ " = " ++ typeStr ++ "\n")
        tpScheme

coreTypeToTpScheme :: String -> [(Id, Tp)] -> C.Type -> TpScheme
coreTypeToTpScheme n table coreType =
    generalize [] (convert True n table coreType)

convert :: Bool -> String -> [(Id, Tp)] -> C.Type -> Tp
convert strictAllowed n table t =
    case t of
        C.TFun    { C.tp1  = t1, C.tp2 = t2 } ->
            TApp (TApp (TCon "->") (convert False n table t1)) (convert True n table t2)
        C.TAp     { C.tp1  = t1, C.tp2 = t2 } ->
            TApp (convert strictAllowed n table t1) (convert strictAllowed n table t2)
        C.TForall { C.tpId = id, C.tp  = t  } ->
            intErr ("Forall: " ++ n ++ " :: " ++ show t)
        C.TExist  { C.tpId = id, C.tp  = t  } ->
            intErr ("Exist:" ++ n ++ " :: " ++ show t)
        C.TStrict { C.tp   = t              } ->
            if strictAllowed then
                convert strictAllowed n table t
            else
                intErr ("Strict:" ++ n ++ " :: " ++ show t)
        C.TVar    { C.tpId = tpId             } ->
            maybe
                (intErr ("Var:" ++ n ++ " :: " ++ show t))
                id
                (lookup tpId table)
        C.TCon    { C.tpId = id             } ->
            TCon (stringFromId id)
        C.TAny                                ->
            intErr ("Any:" ++ n ++ " :: " ++ show t)
        C.TString { C.tpString = t          } ->
            intErr ("String:" ++ n ++ " :: " ++ show t)
    where
        intErr = internalError "CoreToImportEnv" "convert"

splitForalls :: C.Type -> ([Id], C.Type)
splitForalls (C.TForall { C.tpId = id, C.tp = rest }) = 
    let (ids, coreType) = splitForalls rest
    in
        (id:ids, coreType)
splitForalls t = ([], t)
