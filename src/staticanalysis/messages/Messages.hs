-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Messages.hs : !!! CLEAN UP THIS MODULE !!!
-- 
-------------------------------------------------------------------------------

module Messages where

import UHA_Syntax
import UHA_Utils
import OneLiner
import qualified PPrint 
import Types
import TypesToAlignedDocs
import Similarity (similar)
import Utils (internalError,commaList)
import SortedAssocList
import List   (sortBy,sort,partition, intersperse,union)
import Maybe (fromJust,isNothing)
import Char  (toUpper)
import ConstraintInfo

type Errors     = [Error]
type TypeErrors = [TypeError]
type Warnings   = [Warning]
data Hint       = Fix String
                | Because String
                | NoHint

data Error = NoFunDef Entity Name {-names in scope-}Names
           | Undefined Entity Name {-names in scope-}Names {-similar name in wrong name-space hint-}(Maybe String)
           | Duplicated Entity Names
           | LastStatementNotExpr Range
           | WrongFileName {-file name-}String {-module name-}String Range {- of module name -}
           | TypeVarApplication Name
           | ArityMismatch {-type constructor-}Entity Name {-verwacht aantal parameters-}Int {-aangetroffen aantal parameters-}Int
           | DefArityMismatch Name (Maybe Int) {- verwacht -} Range
           | RecursiveTypeSynonyms Names
           | PatternDefinesNoVars Range

data TypeError = TypeError Bool String Range SourceDocs (Maybe (Bool,TpScheme),Tp,Tp) Hint
               | NotGeneralEnough TpScheme TpScheme (Tree,Range)

data Warning = NoTypeDef Name TpScheme Bool
             | Shadow Name Name
             | Unused Entity Name {- toplevel or not -} Bool
             | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}

data Entity = TypeSignature
            | TypeVariable
            | TypeConstructor
            | Definition
--            | PatternVariable
            | Constructor
--            | Parameter
            | Variable
--            | FixityDecl
            | Import
            | ExportVariable
            | ExportModule
            | ExportConstructor
            | ExportTypeConstructor
            | Fixity
    deriving Eq

instance Show Range where
    show (Range_Range begin end) = "<" ++ show begin ++ "," ++ show end ++ ">"
instance Show Position where
    show (Position_Position _ begin end) = "<" ++ show begin ++ "," ++ show end ++ ">"
    show (Position_Unknown) = "<unknown>"
instance Show Name where show = getNameName

instance Eq Range where
    Range_Range start1 stop1 == Range_Range start2 stop2 =
        start1 == start2 && stop1 == stop2

instance Ord Range where
    Range_Range start1 stop1 <= Range_Range start2 stop2 =
        (start1 < start2)
        ||
        (start1 == start2 && stop1 <= stop2)

instance Eq Position where
    Position_Position m1 l1 c1 == Position_Position m2 l2 c2 =
        m1 == m2 && l1 == l2 && c1 == c2
    Position_Unknown           == Position_Unknown        = False
    Position_Unknown           == Position_Position _ _ _ = False
    Position_Position _ _ _    == Position_Unknown        = False

instance Ord Position where
    Position_Position _ l1 c1 <= Position_Position _ l2 c2 =
        (l1 < l2)
        ||
        (l1 == l2 && c1 <= c2)
    Position_Unknown        <= Position_Unknown        = False
    Position_Unknown        <= Position_Position _ _ _ = True
    Position_Position _ _ _ <= Position_Unknown        = False

sortOnRangeEnd :: [Range] -> [Range]
sortOnRangeEnd =
    sortBy
        (\x y ->
            compare
                (getRangeEnd x)
                (getRangeEnd y)
        )

showPositions :: [Range] -> String
showPositions rs = showPositions' (sort rs)
showPositions' :: [Range] -> String
showPositions' (range:ranges) = showPosition range ++ concatMap ((", " ++) . showPosition) ranges
showPositions' [] = "<unknown>"

-- !!!! In the special case that the range corresponds to the import range,
-- the module name of the second position should be printed
showPosition :: Range -> String
showPosition range@(Range_Range _ (Position_Position modName _ _))
    | isImportRange range =
        modName
showPosition (Range_Range (Position_Position _ l c) _) =
    "(" ++ show l ++ "," ++ show c ++ ")"
showPosition (Range_Range Position_Unknown _) =
    "<unknown>"
showPosition _ =
    internalError "SAMessages" "showPosition" "unknown kind of position"

instance Show Error where
    show = snd.showError

sortAndShowErrors :: [Error] -> [String]
sortAndShowErrors = sortAndShow showError

sortAndShowTypeErrors :: [TypeError] -> [String]
sortAndShowTypeErrors = sortAndShow showTypeError

sortAndShowWarnings :: [Warning] -> [String]
sortAndShowWarnings = sortAndShow showWarning

sortAndShow :: (a -> (Range, String)) ->  [a] -> [String]
sortAndShow showFun xs =
    map snd $
    sortBy
        (\x y -> compare (fst x) (fst y))
        (map showFun xs)

showFullRange :: Range -> String
showFullRange (Range_Range p1 p2) = "<" ++ showFullPosition p1 ++ "," ++ showFullPosition p2 ++ ">"

showFullPosition :: Position -> String
showFullPosition (Position_Position m l c) = "<" ++ m ++ "," ++ show l ++ "," ++ show c ++ ">"
showFullPosition (Position_Unknown) = "<unknown>"


showError :: Error -> (Range, String)
showError (NoFunDef TypeSignature name inScope) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      "Type signature for " ++ show (show name) ++ " without a definition " ++
      case findSimilar name inScope of
          [] -> ""
          xs -> "\n  HINT - Did you mean "++prettyOrList (map (show . show) xs)++" ?"
    )
showError (NoFunDef Fixity name inScope) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      "Infix declaration for " ++ show (show name) ++ " without a definition " ++
      case findSimilar name inScope of
          [] -> ""
          xs -> "\n  HINT - Did you mean "++prettyOrList (map (show . show) xs)++" ?"
    )
showError (Undefined entity name inScope wrongNameSpace) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      "Undefined " ++ show entity ++ " " ++ show (show name) ++ maybeHint)
      
   where similarNames  = findSimilar name inScope
         similarHint   = if null similarNames 
                          then []
                          else ["Did you mean " ++ prettyOrList (map (show . show) similarNames) ++ " ?"]
         namespaceHint = case wrongNameSpace of
                            Nothing -> []
                            Just h  -> [h]                     
         maybeHint     = if null (similarHint ++ namespaceHint)
                           then ""
                           else "\n" ++ 
                                concat (intersperse "\n" 
                                    (zipWith (++) 
                                        ("  HINT - " : repeat "         ")
                                        (namespaceHint ++ similarHint))
                                    )
                          
showError (Duplicated entity names)
    | all isImportRange nameRanges =
        ( head nameRanges -- it is only used for sorting
        , capitalize (show entity) ++ " " ++
          (show . show . head) names ++
          " imported from multiple modules: " ++ 
          commaList (map (snd.fromJust.modulesFromImportRange) nameRanges)
        )
    | any isImportRange nameRanges =
        let 
            (importRanges, localRanges) = partition isImportRange nameRanges
            plural = if length importRanges > 1 then "s" else ""
        in
            ( head localRanges
            , showPositions localRanges ++ ": " ++
              capitalize (show entity) ++ " " ++ (show.show.head) names ++
              " clashes with definition" ++ plural ++
              " in imported module" ++ plural ++ " " ++ 
              commaList
              [ snd (fromJust (modulesFromImportRange importRange))
              | importRange <- importRanges
--              , let Just (_,s) = 
              ]
            )
    | otherwise =
        ( head nameRanges
        , showPositions nameRanges ++ ": " ++
          "Duplicated " ++ show entity ++ " " ++ (show . show . head) names
        )
    where
        fromRanges = [ if isImportRange range then
                         Range_Range position position
                       else
                         range
                     | range <- nameRanges
                     , let position = getRangeEnd range
                     ]
        nameRanges   = sort (map getNameRange names)
showError (LastStatementNotExpr range) =
    ( range
    , showPosition range ++ ": " ++
      "Last generator in do {...} must be an expression "
    )
showError (TypeVarApplication name) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      "Type variable " ++ show (show name) ++ " cannot be applied to another type"
    )
showError (ArityMismatch entity name expected actual) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      capitalize (show entity) ++ " " ++show (show name) ++
      " should have " ++ prettyNumberOfParameters expected ++
      ", but has " ++ if actual == 0 then "none" else show actual
    )
showError (RecursiveTypeSynonyms strings) =
    ( head ranges
    , showPositions ranges ++ ": " ++ 
      ( if length strings == 1 
          then "Recursive Type Synonym " ++ show (show (head strings)) ++ "\n  HINT: use \"data\" to write a recursive data type"
          else "Recursive Type Synonyms " ++ prettyAndList (map (show . show) strings)
      )
    )
    where ranges = sort (map getNameRange strings)
showError (DefArityMismatch name maybeExpected range) =
    ( range
    , showPosition range ++ ": " ++
      "arity mismatch in function bindings for " ++ show (show name) ++
      case maybeExpected of
          Just arity -> "\n  HINT: " ++ show arity ++ " parameters in most of the clauses"
          Nothing -> ""
    )
showError (PatternDefinesNoVars range) =
    ( range
    , showPosition range ++ ": " ++
      "left hand side pattern defines no variables"
    )
showError (WrongFileName fileName moduleName range) =
    ( range
    , showPosition range ++ ": " ++
      "The file name " ++ show fileName ++ " doesn't match the module name " ++ show moduleName
    )
showError _ = internalError "SAMessages" "showError" "unknown type of Error"

showTypeError :: TypeError -> (Range, String)
showTypeError typeError = case typeError of
                             TypeError _ _ range _ _ _      -> (range,show typeError)
                             NotGeneralEnough _ _ (_,range) -> (range,show typeError)

instance Show Warning where
    show = snd . showWarning

showWarning :: Warning -> (Range, String)
showWarning (NoTypeDef name tpscheme topLevel) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      "Missing type signature: " ++ show name ++ " :: "++show tpscheme
    )
showWarning (Shadow shadowee shadower) =
    ( getNameRange shadower
    , showPosition (getNameRange shadower) ++ ": " ++
      "Variable " ++ show (show shadower) ++
      " shadows the one at " ++
      showPosition (getNameRange shadowee)
    )
showWarning (Unused entity name toplevel) =
    ( getNameRange name
    , showPosition (getNameRange name) ++ ": " ++
      capitalize (show entity) ++ " " ++ show (show name) ++ " is not used"
    )
showWarning (SimilarFunctionBindings suspect witness) =
    ( getNameRange suspect
    , showPosition (getNameRange suspect) ++ ": " ++
      "Suspicious adjacent functions "++ show (show suspect) ++ " and " ++ show (show witness)
    )   
showWarning _ =
    internalError "SAMessages" "show (Warning)" "unknown type of warning"

prettyOrList :: [String] -> String
prettyOrList []  = ""
prettyOrList [s] = s
prettyOrList xs  = foldr1 (\x y -> x++", "++y) (init xs) ++ " or "++last xs

prettyAndList :: [String] -> String
prettyAndList []  = ""
prettyAndList [s] = s
prettyAndList xs  = foldr1 (\x y -> x++", "++y) (init xs) ++ " and "++last xs

prettyNumberOfParameters :: Int -> String
prettyNumberOfParameters 0 = "no parameters"
prettyNumberOfParameters 1 = "1 parameter"
prettyNumberOfParameters n = show n++" parameters"

type SourceDocs      = [ SourceDoc ]
data SourceDoc       = SD_Expr Tree
                     | SD_Pat  Tree
                     | SD_Term Tree
               
instance Show TypeError where
   show (TypeError folklore location range sourcedocs (mts,t1,t2) hint) =
             unlines $ (showPosition range ++ ": Type error in " ++ location)
                     : prettySourcedocs
                    ++ prettyTypesDontMatch
                    ++ prettyHint

    where prettySourcedocs = let f (SD_Expr tree) = prefix "Expression" ++ showOneLine lineLength tree
                                 f (SD_Pat  tree) = prefix "Pattern"    ++ showOneLine lineLength tree
                                 f (SD_Term tree) = prefix "Term"       ++ showOneLine lineLength tree
                             in map f sourcedocs

          prettyTypesDontMatch = let tuple = case mts of 
                                                Nothing     -> (t1,t2)
                                                Just (b,ts) -> if b then (instantiateWithNameMap ts,t2) else (t2,instantiateWithNameMap ts)
                                     render = flip PPrint.displayS [] . PPrint.renderPretty 1.0 lineLength
                                     (d1,d2) = showTwoTypesSpecial tuple
                                     (x1:xs1,x2:xs2) = (lines $ render d1,lines $ render d2)
                                     reason  = if folklore then "Expected type" else "Does not match"
                                 in ( (prefix "Type" ++ x1)
                                    : map (replicate indentation ' ' ++) xs1 
                                    ) ++
                                    ( (prefix reason ++ x2)
                                    : map (replicate indentation ' ' ++) xs2
                                    )
                                     
          prettyHint = case hint of 
                         Fix s     -> [prefix "Probable fix"++s]
                         Because s -> [prefix "Because"++s]
                         _         -> []
          
   show (NotGeneralEnough scheme1 scheme2 (tree,range)) =

           let [s1,s2]   = freezeMonosInTypeSchemes [scheme1,scheme2]
               maybeHint | null (ftv scheme1) = []
                         | otherwise          = [ prefix "Hint" ++ "Try removing the type signature" ]
           in unlines ([ showPosition range ++ ": Declared type is too general"
                       , prefix "Expression"    ++ showOneLine lineLength tree
                       , prefix "Declared type" ++ show s2
                       , prefix "Inferred type" ++ show s1
                       ] ++ maybeHint)

checkTypeError :: OrderedTypeSynonyms -> TypeError -> Maybe TypeError
checkTypeError synonyms typeError@(TypeError folklore location range sourcedocs (mts,t1,t2) hint) = 
   let (x1,x2) = case mts of 
                    Nothing     -> (t1,t2)
                    Just (b,ts) -> if b then (instantiateWithNameMap ts,t2) else (t2,instantiateWithNameMap ts)
   in case mguWithTypeSynonyms synonyms x1 x2 of
         Left InfiniteType  -> Just (setHint (Because "unification would give infinite type") typeError)   
         Left ConstantClash -> Just typeError
         Right _            -> Nothing
checkTypeError _ t = Just t         

splitString :: String -> [String]
splitString [] = []
splitString xs = let (a,b) = splitAt lineLength xs
                 in a : splitString b

lineLength = 80 - indentation - 1

prefix s = "*** "++take 14 (s++repeat ' ')++" : "
indentation = length (prefix "")

capitalize :: String -> String
capitalize (x:xs) = toUpper x : xs

findSimilar :: Name -> Names -> Names
findSimilar n = filter (\n' -> show n `similar` show n')

instance Show Entity where
   show entity = case entity of
                  TypeSignature   -> "type signature"
                  TypeVariable    -> "type variable"
                  TypeConstructor -> "type constructor"
                  Definition      -> "definition"
                  Constructor     -> "constructor"
                  Variable        -> "variable"
                  Import          -> "import"
                  ExportVariable  -> "exported variable"
                  ExportModule    -> "exported module"
                  ExportConstructor
                                  -> "exported constructor"
                  ExportTypeConstructor
                                  -> "exported type constructor"
                  Fixity          -> "infix declaration"
                  _               -> internalError "SAMessages" "instance Show Entity" "unknown entity"

makeUnused :: Entity -> Names -> Bool -> [Warning]
makeUnused entity names toplevel = [ Unused entity name toplevel | name <- names ]

makeUndefined :: Entity -> Names -> Names -> [Error]
makeUndefined entity names inScope = [ Undefined entity name inScope Nothing | name <- names ]

makeDuplicated :: Entity -> [Names] -> [Error]
makeDuplicated entity nameslist = [ Duplicated entity names | names <- nameslist ]

undefinedConstructor :: Name -> Names -> Names -> Error
undefinedConstructor name sims tyconNames = Undefined Constructor name sims hint
   where hint = if name `elem` tyconNames
                  then Just ("Type constructor "++show (show name)++" cannot be used in an expression or pattern") 
                  else Nothing

makeNoFunDef :: Entity -> Names -> Names -> [Error]
makeNoFunDef entity names inScope = [ NoFunDef entity name inScope | name <- names ]

-- Log-codes for Errors
errorsLogCode :: Errors -> String
errorsLogCode [] = "[]"
errorsLogCode xs = foldr1 (\x y -> x++","++y) (map errorLogCode xs)

errorLogCode :: Error -> String
errorLogCode anError = case anError of 
          NoFunDef entity _ _     -> "nf" ++ code entity
          Undefined entity _ _ _  -> "un" ++ code entity
          Duplicated entity _     -> "du" ++ code entity
          LastStatementNotExpr _  -> "ls"
          WrongFileName _ _ _     -> "wf"
          TypeVarApplication _    -> "tv"
          ArityMismatch _ _ _ _   -> "am"
          DefArityMismatch _ _ _  -> "da"
          RecursiveTypeSynonyms _ -> "ts"
          PatternDefinesNoVars _  -> "nv"
          _                       -> "??"
   where code entity = maybe "??" id
                     . lookup entity 
                     $ [ (TypeSignature    ,"ts"), (TypeVariable         ,"tv"), (TypeConstructor,"tc")
                       , (Definition       ,"de"), (Constructor          ,"co"), (Variable       ,"va") 
                       , (Import           ,"im"), (ExportVariable       ,"ev"), (ExportModule   ,"em")
                       , (ExportConstructor,"ec"), (ExportTypeConstructor,"et"), (Fixity         ,"fx")
                       ]

setHint :: Hint -> TypeError -> TypeError
setHint hint (TypeError b s r ds (mts,t1,t2) _) = TypeError b s r ds (mts,t1,t2) hint

instance Substitutable TypeError where
   sub |-> typeError = 
      case typeError of
         TypeError b s r ds (mts,t1,t2) mh -> 
            let mts' = case mts of 
                          Just (b,ts) -> Just (b,sub |-> ts)
                          Nothing     -> Nothing 
            in TypeError b s r ds (mts',sub |-> t1,sub |-> t2) mh
         
         NotGeneralEnough ts1 ts2 (d,r) -> 
            NotGeneralEnough (sub |-> ts1) (sub |-> ts2) (d,r)
     
   ftv typeError = 
      case typeError of
         TypeError b s r ds (mts,t1,t2) mh -> 
            let mts' = case mts of 
                          Just (b,ts) -> ftv ts
                          Nothing     -> [] 
            in mts' `union` ftv t1 `union` ftv t2
         
         NotGeneralEnough ts1 ts2 (d,r) -> 
            ftv ts1 `union` ftv ts2
