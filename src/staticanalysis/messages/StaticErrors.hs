-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- StaticErrors.hs : ...
-- 
-------------------------------------------------------------------------------

module StaticErrors where

import UHA_Syntax
import UHA_Utils
import Messages
import List        (intersperse, sort, partition)
import Maybe       (fromJust)
import Utils       (commaList, internalError)

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

instance HasMessage Error where
   getMessage x = let (oneliner, hints) = showError x
                  in [MessageOneLiner oneliner, MessageHints "HINT" hints]
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
         
showError :: Error -> (MessageBlock {- oneliner -}, MessageBlocks {- hints -})
showError anError = case anError of 
  
   NoFunDef TypeSignature name inScope ->
      ( MessageString ("Type signature for " ++ show (show name) ++ " without a definition ")
      , [ MessageString ("Did you mean "++prettyOrList (map (show . show) xs)++" ?")
        | let xs = findSimilar name inScope, not (null xs) 
        ] 
      )

   NoFunDef Fixity name inScope ->
      ( MessageString ("Infix declaration for " ++ show (show name) ++ " without a definition ")
      , [ MessageString ("Did you mean "++prettyOrList (map (show . show) xs)++" ?")
        | let xs = findSimilar name inScope, not (null xs) 
        ] 
      )

   Undefined entity name inScope wrongNameSpace ->
      ( MessageString ("Undefined " ++ show entity ++ " " ++ show (show name))
      , [ MessageString hint
        | Just hint <- [wrongNameSpace]
        ]
        ++
        [ MessageString ("Did you mean " ++ prettyOrList (map (show . show) xs) ++ " ?")
        | let xs = findSimilar name inScope, not (null xs)
        ]
      )
                         
   Duplicated entity names
      | all isImportRange nameRanges ->
           ( MessageString (
                capitalize (show entity) ++ " " ++
                (show . show . head) names ++
                " imported from multiple modules: " ++ 
                commaList (map (snd.fromJust.modulesFromImportRange) nameRanges)), [])
                
      | any isImportRange nameRanges ->
           let 
               (importRanges, localRanges) = partition isImportRange nameRanges
               plural = if length importRanges > 1 then "s" else ""
           in
              ( MessageString ( 
                   capitalize (show entity) ++ " " ++ (show.show.head) names ++
                   " clashes with definition" ++ plural ++
                   " in imported module" ++ plural ++ " " ++ 
                   commaList [ snd (fromJust (modulesFromImportRange importRange)) 
                             | importRange <- importRanges
                             ]), [])
                             
      | otherwise ->
           ( MessageString ("Duplicated " ++ show entity ++ " " ++ (show . show . head) names), [])
                 
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
      ( MessageString "Last generator in do {...} must be an expression ", [])
    
   TypeVarApplication name ->
      ( MessageString ("Type variable " ++ show (show name) ++ " cannot be applied to another type"), [])

   ArityMismatch entity name expected actual ->
      ( MessageString ( capitalize (show entity) ++ " " ++show (show name) ++
           " should have " ++ prettyNumberOfParameters expected ++
           ", but has " ++ if actual == 0 then "none" else show actual), [])
    
   RecursiveTypeSynonyms strings ->
      ( MessageString ("Recursive Type Synonyms " ++ prettyAndList (map (show . show) (sortNamesByRange strings)))
      , [ MessageString "use \"data\" to write a recursive data type"
        | length strings == 1
        ]  
      )     
        
   DefArityMismatch name maybeExpected range ->
      ( MessageString ("Arity mismatch in function bindings for " ++ show (show name))
      , [ MessageString (show arity ++ " parameters in most of the clauses")
        | Just arity <- [maybeExpected]
        ]
      )

   PatternDefinesNoVars range ->
      ( MessageString "left hand side pattern defines no variables", [])

   WrongFileName fileName moduleName range ->
      ( MessageString ("The file name " ++ show fileName ++ " doesn't match the module name " ++ show moduleName), [])
      
   _ -> internalError "Messages.hs" "showError" "unknown type of Error"

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
