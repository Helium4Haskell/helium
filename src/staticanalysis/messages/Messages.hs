-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Messages.hs : ...
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

class IsMessage a where
   getRanges :: a -> [Range]
   display   :: a -> String

-------------------------------------------------------------
-- (Static) Errors

type Errors = [Error]
data Error  = NoFunDef Entity Name {-names in scope-}Names
            | Undefined Entity Name {-names in scope-}Names {-similar name in wrong name-space hint-}(Maybe String)
            | Duplicated Entity Names
            | LastStatementNotExpr Range
            | WrongFileName {-file name-}String {-module name-}String Range {- of module name -}
            | TypeVarApplication Name
            | ArityMismatch {-type constructor-}Entity Name {-verwacht aantal parameters-}Int {-aangetroffen aantal parameters-}Int
            | DefArityMismatch Name (Maybe Int) {- verwacht -} Range
            | RecursiveTypeSynonyms Names
            | PatternDefinesNoVars Range

instance IsMessage Error where
   display = showError
   getRanges anError = case anError of
   
      NoFunDef _ name _           -> [getNameRange name]
      Undefined _ name _ _        -> [getNameRange name]
      Duplicated _ names          -> map getNameRange names
      LastStatementNotExpr range  -> [range]
      WrongFileName _ _ range     -> [range]
      TypeVarApplication name     -> [getNameRange name]
      ArityMismatch _ name _ _    -> [getNameRange name]             
      DefArityMismatch _ _ range  -> [range]
      RecursiveTypeSynonyms names -> map getNameRange names
      PatternDefinesNoVars range  -> [range]
      _                           -> internalError "Messages.hs" 
                                                   "instance IsMessage Error" 
                                                   "unknown type of Error"
         
showError :: Error -> String
showError anError = case anError of 
   
   NoFunDef TypeSignature name inScope ->
      "Type signature for " ++ show (show name) ++ " without a definition " ++
      case findSimilar name inScope of
          [] -> ""
          xs -> "\n  HINT - Did you mean "++prettyOrList (map (show . show) xs)++" ?"
   
   NoFunDef Fixity name inScope ->
      "Infix declaration for " ++ show (show name) ++ " without a definition " ++
      case findSimilar name inScope of
          [] -> ""
          xs -> "\n  HINT - Did you mean "++prettyOrList (map (show . show) xs)++" ?"
     
   Undefined entity name inScope wrongNameSpace ->
      "Undefined " ++ show entity ++ " " ++ show (show name) ++ maybeHint
      
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
                         
   Duplicated entity names
      | all isImportRange nameRanges ->
           capitalize (show entity) ++ " " ++
           (show . show . head) names ++
           " imported from multiple modules: " ++ 
           commaList (map (snd.fromJust.modulesFromImportRange) nameRanges)
        
      | any isImportRange nameRanges ->
           let 
               (importRanges, localRanges) = partition isImportRange nameRanges
               plural = if length importRanges > 1 then "s" else ""
           in
              capitalize (show entity) ++ " " ++ (show.show.head) names ++
              " clashes with definition" ++ plural ++
              " in imported module" ++ plural ++ " " ++ 
              commaList
              [ snd (fromJust (modulesFromImportRange importRange))
              | importRange <- importRanges
              ]
      | otherwise ->
           "Duplicated " ++ show entity ++ " " ++ (show . show . head) names
                 
    where
        fromRanges = [ if isImportRange range then
                         Range_Range position position
                       else
                         range
                     | range <- nameRanges
                     , let position = getRangeEnd range
                     ]
        nameRanges   = sort (map getNameRange names)

   LastStatementNotExpr range ->
      "Last generator in do {...} must be an expression "
    
   TypeVarApplication name ->
      "Type variable " ++ show (show name) ++ " cannot be applied to another type"

   ArityMismatch entity name expected actual ->
      capitalize (show entity) ++ " " ++show (show name) ++
      " should have " ++ prettyNumberOfParameters expected ++
      ", but has " ++ if actual == 0 then "none" else show actual
      
   RecursiveTypeSynonyms strings ->
      ( if length strings == 1 
          then "Recursive Type Synonym " ++ show (show (head strings)) ++ "\n  HINT: use \"data\" to write a recursive data type"
          else "Recursive Type Synonyms " ++ prettyAndList (map (show . show) strings)
      )
       where ranges = sort (map getNameRange strings)
       
   DefArityMismatch name maybeExpected range ->
      "arity mismatch in function bindings for " ++ show (show name) ++
      case maybeExpected of
          Just arity -> "\n  HINT: " ++ show arity ++ " parameters in most of the clauses"
          Nothing -> ""

   PatternDefinesNoVars range ->
      "left hand side pattern defines no variables"

   WrongFileName fileName moduleName range ->
      "The file name " ++ show fileName ++ " doesn't match the module name " ++ show moduleName

   _ -> internalError "Messages.hs" "showError" "unknown type of Error"

-------------------------------------------------------------
-- Type Errors

type TypeErrors = [TypeError]
data TypeError  = TypeError Bool String Range SourceDocs (Maybe (Bool,TpScheme),Tp,Tp) Hint
                | NotGeneralEnough TpScheme TpScheme (Tree,Range)

instance IsMessage TypeError where
   display = showTypeError
   getRanges typeError = case typeError of
                            TypeError _ _ range _ _ _      -> [range]
                            NotGeneralEnough _ _ (_,range) -> [range]    

showTypeError :: TypeError -> String
showTypeError typeError = case typeError of

   TypeError folklore location range sourcedocs (mts,t1,t2) hint ->
             unlines $ ("Type error in " ++ location)
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
          
   NotGeneralEnough scheme1 scheme2 (tree,range) ->

           let [s1,s2]   = freezeMonosInTypeSchemes [scheme1,scheme2]
               maybeHint | null (ftv scheme1) = []
                         | otherwise          = [ prefix "Hint" ++ "Try removing the type signature" ]
           in unlines ([ "Declared type is too general"
                       , prefix "Expression"    ++ showOneLine lineLength tree
                       , prefix "Declared type" ++ show s2
                       , prefix "Inferred type" ++ show s1
                       ] ++ maybeHint)

-------------------------------------------------------------
-- (Static) Warnings

type Warnings = [Warning]
data Warning  = NoTypeDef Name TpScheme Bool
              | Shadow Name Name
              | Unused Entity Name {- toplevel or not -} Bool
              | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}

instance IsMessage Warning where
   display  = showWarning
   getRanges warning = case warning of
      NoTypeDef name _ _             -> [getNameRange name]
      Shadow _ name                  -> [getNameRange name]
      Unused _ name _                -> [getNameRange name]
      SimilarFunctionBindings name _ -> [getNameRange name]
      _                              -> internalError "Messages.hs" 
                                                      "instance IsMessage Warning" 
                                                      "unknown type of Warning"

showWarning :: Warning -> String
showWarning warning = case warning of

   NoTypeDef name tpscheme topLevel ->
      "Missing type signature: " ++ show name ++ " :: "++show tpscheme

   Shadow shadowee shadower ->
      "Variable " ++ show (show shadower) ++
      " shadows the one at " ++
      showPosition (getNameRange shadowee)

   Unused entity name toplevel ->
      capitalize (show entity) ++ " " ++ show (show name) ++ " is not used"
    
   SimilarFunctionBindings suspect witness ->
      "Suspicious adjacent functions "++ show (show suspect) ++ " and " ++ show (show witness)
   
   _ -> internalError "Messages" "showWarning" "unknown type of Warning"

-------------------------------------------------------------
-- Misc

data Hint       = Fix String
                | Because String
                | NoHint

data Entity = TypeSignature
            | TypeVariable
            | TypeConstructor
            | Definition
            | Constructor
            | Variable
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

sortRanges :: [Range] -> [Range]
sortRanges ranges = let (xs,ys) = partition isImportRange ranges
                    in sort ys ++ xs
                                        
sortAndShow :: IsMessage a => [a] -> [String]
sortAndShow xs = let displayAll x = f (filter (not . isImportRange) (getRanges x)) ++ display x
                     f [] = ""
                     f xs = showPositions xs ++ ": "
                 in map (displayAll . snd)
                  . sortBy (\x y -> compare (fst x) (fst y)) 
                  $ [ (sortRanges (getRanges x), x) | x <- xs ]

showFullRange :: Range -> String
showFullRange (Range_Range p1 p2) = "<" ++ showFullPosition p1 ++ "," ++ showFullPosition p2 ++ ">"

showFullPosition :: Position -> String
showFullPosition (Position_Position m l c) = "<" ++ m ++ "," ++ show l ++ "," ++ show c ++ ">"
showFullPosition (Position_Unknown) = "<unknown>"

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
