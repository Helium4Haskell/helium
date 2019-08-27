{-| Module      :  CoreUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.CoreUtils
    (   custom, customStrategy
    ,   stringToCore, coreList
    ,   let_, if_, app_, letrec_
    ,   cons, nil
    ,   var, decl
    ,   float, packedString
    ,   setExportsPublic
    ,   toplevelType
    ) where

import Lvm.Core.Expr
import Lvm.Common.Id
import Lvm.Common.IdSet
import Lvm.Core.Utils
import Data.Char
import Lvm.Common.Byte(bytesFromString)
import qualified Lvm.Core.Expr as Core
import qualified Data.Map as M
import Helium.Utils.QualifiedTypes (convertClassNameToQualified)
import Data.List(isPrefixOf)
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils
import Helium.Syntax.UHA_Syntax ( Name )

infixl `app_`

custom :: String -> String -> Custom
custom sort text =
    CustomDecl
        (DeclKindCustom (idFromString sort))
        [CustomBytes (bytesFromString text)]


customStrategy :: String -> Decl a
customStrategy text =
    DeclCustom    
        { declName = idFromString ""
        , declAccess = Defined { accessPublic = True }
        , declKind = DeclKindCustom (idFromString "strategy")
        , declCustoms = [custom "strategy" text]
        }

app_ :: Expr -> Expr -> Expr
app_ f x = Ap f x

let_ :: Id -> Expr -> Expr -> Expr
let_ x e b = Let (NonRec (Bind x e)) b

letrec_ :: [CoreDecl] -> Expr -> Expr
letrec_ bs e = 
    Let 
        (Rec 
            [ Bind ident expr
            | DeclValue { declName = ident, valueValue = expr } <- bs
            ]
        ) 
        e

-- Function "if_" builds a Core expression of the following form
-- let! guardId = <guardExpr> in 
-- match guardId 
--   True -> <thenExpr>
--   _    -> <elseExpr>
if_ :: Expr -> Expr -> Expr -> Expr
if_ guardExpr thenExpr elseExpr =
    Let 
        (Strict (Bind guardId guardExpr))
        (Match guardId
            [ Alt (PatCon (ConId trueId) []) thenExpr
            , Alt PatDefault elseExpr
            ]
        )

-- Function "coreList" builds a linked list of the given expressions
-- Example: coreList [e1, e2] ==> 
--   Ap (Ap (Con ":") e1) 
--           (Ap (Ap (Con ":") e2)
--                    (Con "[]")
--           )
coreList :: [Expr] -> Expr
coreList = foldr cons nil

cons :: Expr -> Expr -> Expr
cons x xs = Con (ConId consId) `app_` x `app_` xs

nil :: Expr
nil = Con (ConId nilId)

nilId, consId, trueId, guardId :: Id 
( nilId : consId :  trueId :  guardId : []) =
   map idFromString ["[]", ":", "True", "guard$"]

-- Function "stringToCore" converts a string to a Core expression
stringToCore :: String -> Expr
stringToCore [x] = cons (Lit (LitInt (ord x))) nil
stringToCore xs = var "$primPackedToString" `app_` packedString xs

var :: String -> Expr
var x = Var (idFromString x)

--Core.Lit (Core.LitDouble (read @value))   PUSHFLOAT nog niet geimplementeerd
float :: String -> Expr
float f = 
    Core.Ap 
        (Core.Var (idFromString "$primStringToFloat")) 
        ( Core.Lit (Core.LitBytes (bytesFromString f)) )

decl :: Bool -> String -> Expr -> CoreDecl
decl isPublic x e = 
    DeclValue 
        { declName = idFromString x
        , declAccess = Defined { accessPublic = isPublic }
        , valueEnc = Nothing
        , valueValue = e
        , declCustoms = []
        }

packedString :: String -> Expr
packedString s = Lit (LitBytes (bytesFromString s))

customInfix :: DeclKind
customInfix = customDeclKind "infix"



setExportsPublic :: Bool -> (IdSet,IdSet,IdSet,IdSet,IdSet) -> ImportEnvironment -> Module v -> Module v
setExportsPublic implicit (exports,exportCons,exportData,exportDataCon,exportMods) env m
  = m { moduleDecls = concatMap setPublic (moduleDecls m) }
  where
    setPublic decl_ | isQual decl_ && (isInstance decl_ || isTypeSynonym decl_ || declPublic decl_) = 
                        let name = stringFromId $! declName decl_
                            newname = idFromString $! (unQualifyString name)
                        in if not ("Dict" `isPrefixOf` name) then
                            [decl_{ declName = newname, declAccess = (declAccess decl_){ accessPublic = True } }, decl_{declAccess = (declAccess decl_){ accessPublic = False }}]
                           else
                            [decl_]
                    | isQual decl_ =
                        [decl_{declAccess = (declAccess decl_){ accessPublic = False }}]
                    | isInstance decl_ || isTypeSynonym decl_ || declPublic decl_ =
                        [decl_{declAccess = (declAccess decl_){ accessPublic = True } }]
                    | otherwise       = [decl_]

    isExported decl_ elemIdSet =
        let access = declAccess decl_ in
        if implicit then
            case decl_ of
                DeclImport{} ->  False
                _ ->
                    case access of
                        Imported{} -> False
                        Defined{}  -> True --accessPublic access
        else
            case access of
                Imported{ importModule = x }
                    | elemSet x exportMods              -> True
                    | otherwise                         -> elemIdSet
                Defined{}
                    | elemSet (moduleName m) exportMods -> True
                    | otherwise                         -> elemIdSet

    declPublic decl_ =
        let name = declName decl_
        in
        case decl_ of
            DeclValue{}     ->  isExported decl_ (elemSet name exports)
            DeclAbstract{}  ->  isExported decl_ 
                                    (  elemSet name exports
                                    || elem (stringFromId name) classMembers
                                    )
            DeclExtern{}    ->  isExported decl_ (elemSet name exports)
            DeclCon{}       ->  isExported decl_
                                    (  elemSet name exportCons
                                    || (elemSet (conTypeName decl_) exportDataCon)
                                    )
            DeclCustom{}    ->  isExported decl_
                                    (declKind decl_ `elem` [customData, customTypeDecl, customClassDefinition] 
                                                && (elemSet name exportData || elemSet name exportDataCon)
                                    || (declKind decl_ `elem` [customInfix] && elemSet name exports)
                                    )
            _               -> internalError "CoreUtils" "setExportsPublic" "We can only deal with Custom, Value, and Con Core.Decl"
    
    isQual decl_ = let name = stringFromId $ declName decl_ in isQualifiedString name

    -- Get all class members that should be exported
    classMembers     = concat $ map (map (\(n,_,_,_) -> getNameName n) . snd) $ M.elems exportClasses
    exportClasses    = M.filterWithKey (const . (`elem` exportClassNames)) classMemberEnv
    exportClassNames = map (convertClassNameToQualified env . nameFromString . stringFromId) (listFromSet exportDataCon)
    classMemberEnv   = classMemberEnvironment env 
    
            -- Always export dictionaries
    isInstance decl_ = let name = stringFromId $ declName decl_ in "$dict" `isPrefixOf` name
    
    --For now we always export type synonyms
    isTypeSynonym decl_ =case decl_ of
        DeclCustom{declKind = k} | k == customTypeDecl -> True
        _ -> False
        

    conTypeName (DeclCon{declCustoms=(_:CustomLink x _:_)}) = x
    conTypeName _ = dummyId

toplevelType :: Name -> ImportEnvironment -> Bool -> [Custom]
toplevelType name ie isTopLevel
    | isTopLevel = [custom "type" typeString]
    | otherwise  = []
    where
        typeString = maybe
            (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
            show
            (M.lookup name (typeEnvironment ie))
