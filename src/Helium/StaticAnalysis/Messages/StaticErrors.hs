{-| Module      :  StaticErrors
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    Collection of static error messages.
-}

module Helium.StaticAnalysis.Messages.StaticErrors where


import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Range
import Helium.StaticAnalysis.Messages.Messages
import Data.List        (nub, intersperse, sort, partition)
import Data.Maybe
import Helium.Utils.Utils       (commaList, internalError, maxInt)

import Top.Types
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (MonoType)

-------------------------------------------------------------
-- (Static) Errors

type Errors = [Error]
data Error  = NoFunDef Entity Name {-names in scope-}Names
            | NoTypeDefInClass Entity Name Names
            | FunctionInMultipleClasses Entity Name Names
            | MultiParameterTypeClass Entity Name Names
            | DefNonUniqueInstanceVars Name Names
            | ClassMethodContextError Entity Name Names ContextItems
            | ClassVariableNotInMethodSignature Name Name Names -- Class name, class variable, method name
            | InvalidContext Entity Name Names
            | Undefined Entity Name {-names in scope-}Names {-similar name in wrong name-space hint-}[String] {- hints -}
            | UndefinedClass Name {-Classes in scope -} Names
            | InvalidInstanceConstraint Name Name Name
            | InvalidInstanceType Name
            | UndefinedFunctionForClass Name Name Names
            | TypeSignatureInInstance Name Names
            | TypeClassOverloadRestr Name Names
            | TypeSynonymInInstance Range Predicate
            | DuplicateClassName Names
            | DuplicatedClassImported Name
            | OverlappingInstance String Tp
            | MissingSuperClass Range Predicate Predicate
            | Duplicated Entity Names
            | LastStatementNotExpr Range
            | WrongFileName {-file name-}String {-module name-}String Range {- of module name -}
            | TypeVarApplication Name
            | ArityMismatch {-type constructor-}Entity Name {-verwacht aantal parameters-}Int {-aangetroffen aantal parameters-}Int
            | DefArityMismatch Name (Maybe Int) {- verwacht -} Range
            | RecursiveTypeSynonyms Names
            | PatternDefinesNoVars Range
            | IntLiteralTooBig Range String
            | OverloadingDisabled Range
            | OverloadedRestrPat Name
            | WrongOverloadingFlag Bool{- flag? -}
            | AmbiguousContext Name
            | UnknownClass Name
            | NonDerivableClass Name
            | CannotDerive Name Tps
            | TupleTooBig Range
            | IncorrectConstructorResult Range Name {- Constructor -} TpScheme {- Given result type -} TpScheme {- Expected result type -}
            | MissingGADTOption
            | DuplicateTypeFamily (Name, Name)
            | UndefinedTypeFamily Name Names
            | WronglySaturatedTypeFamily Name Int Int
            | WronglyAlignedATS Name Name MonoType MonoType

instance HasMessage Error where
   getMessage x = let (oneliner, hints) = showError x
                  in [MessageOneLiner oneliner, MessageHints "Hint" hints]
   getRanges anError = case anError of
      NoFunDef _ name _           -> [getNameRange name]
      NoTypeDefInClass _ name _   -> [getNameRange name]
      FunctionInMultipleClasses _ name _ -> [getNameRange name]
      MultiParameterTypeClass _ name _ -> [getNameRange name]
      DefNonUniqueInstanceVars name _ -> [getNameRange name]
      ClassMethodContextError _ name _ _ -> [getNameRange name]
      InvalidContext _ name _     -> [getNameRange name]
      ClassVariableNotInMethodSignature _ _ names -> sortRanges (map getNameRange names)
      DuplicateClassName names -> sortRanges (map getNameRange names)
      DuplicatedClassImported name -> [getNameRange name]
      TypeClassOverloadRestr _ names -> sortRanges (map getNameRange names)
      TypeSynonymInInstance range _   -> [range]
      Undefined _ name _ _        -> [getNameRange name]
      UndefinedClass name _       -> [getNameRange name]
      UndefinedFunctionForClass _ name _ -> [getNameRange name]
      InvalidInstanceType name -> [getNameRange name]
      TypeSignatureInInstance _ names -> sortRanges $ map getNameRange names
      MissingSuperClass range _ _ -> [range]
      InvalidInstanceConstraint _ name _ -> [getNameRange name]
      Duplicated _ names          -> sortRanges (map getNameRange names)
      LastStatementNotExpr range  -> [range]
      WrongFileName _ _ range     -> [range]
      TypeVarApplication name     -> [getNameRange name]
      ArityMismatch _ name _ _    -> [getNameRange name]
      DefArityMismatch _ _ range  -> [range]
      RecursiveTypeSynonyms names -> sortRanges (map getNameRange names)
      PatternDefinesNoVars range  -> [range]
      IntLiteralTooBig range _    -> [range]
      OverloadingDisabled range   -> [range]
      OverloadedRestrPat name     -> [getNameRange name]
      WrongOverloadingFlag _      -> [emptyRange]
      OverlappingInstance _ _     -> [emptyRange]
      AmbiguousContext name       -> [getNameRange name]
      UnknownClass name           -> [getNameRange name]
      NonDerivableClass name      -> [getNameRange name]
      CannotDerive name _         -> [getNameRange name]
      TupleTooBig r               -> [r]
      IncorrectConstructorResult r _ _ _ -> [r]
      MissingGADTOption           -> []
      DuplicateTypeFamily (n1, n2) -> sortRanges [getNameRange n1, getNameRange n2]
      UndefinedTypeFamily name _  -> [getNameRange name]
      WronglySaturatedTypeFamily n _ _ -> [getNameRange n]
      WronglyAlignedATS n1 n2 t1 t2   -> sortRanges [getNameRange n1, getNameRange n2]

sensiblySimilar :: Name -> Names -> [Name]
sensiblySimilar name inScope =
   let
      similars = nub (findSimilar name inScope)
   in
      if length similars <= 3 then -- 3 is the magic number
         similars
      else
         []

showError :: Error -> (MessageBlock {- oneliner -}, MessageBlocks {- hints -})
showError anError = case anError of

   NoFunDef TypeSignature name inScope ->
      ( MessageString ("Type signature for " ++ show (show name) ++ " without a definition ")
      , [ MessageString ("Did you mean "++prettyOrList (map (show . show) xs)++" ?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )

   NoFunDef Fixity name inScope ->
      ( MessageString ("Infix declaration for " ++ show (show name) ++ " without a definition ")
      , [ MessageString ("Did you mean "++prettyOrList (map (show . show) xs)++" ?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )

   NoTypeDefInClass Definition name inScope ->
      ( MessageString ("Function definition for " ++ show (show name) ++ " without a type signature is not allowed in a Class ")
      , [ MessageString ("Did you mean "++prettyOrList (map (show . show) xs)++"?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )

   DuplicateClassName names ->
      ( MessageString ("Found multiple definitions for the class: " ++ show (head names) ++ ".")
      , [ MessageString ("You may only use a class name once.")]
      )

   DuplicatedClassImported name ->
      ( MessageString ("Found a definition for the class: " ++ show name ++ ", but this name is already used by an imported class.")
      , []
      )

   FunctionInMultipleClasses Definition name classes ->
      ( MessageString ("Type declaration for " ++ show (show name) ++ " in multipe classes")
      , [ MessageString ("You declared it in: "++prettyOrList (map (show . show) classes)++" .")]
      )

   MultiParameterTypeClass Definition name vars ->
      ( MessageString ("Multiparameter typeclasses are not supported, error in class definition: " ++ show (show name) ++ ". ")
      , [ MessageString ("You used parameters: "++prettyAndList (map (show . show) vars)++" .")]
      )

   DefNonUniqueInstanceVars name vars ->
      ( MessageString ("Not all type variables in instance declaration of class: " ++ show name ++ " are unique. ")
      , [ MessageString ("Type variable: " ++ show v ++ " occurs more then once.") | v <- vars]
      )

   ClassMethodContextError Definition className methods ctxt ->
      ( MessageString ("Not allowed to put further restictions on typeClass variable in type class: " ++ (show className) ++ ". ")
      , [ MessageString ("In the type signatures of: "++ prettyAndList (map show methods) ++ " the following context items are not allowed: " ++
                          prettyAndList (map (\(ContextItem_ContextItem _ n _) -> show n) ctxt) ++ ".")]
      )

   InvalidContext Definition name vars ->
      ( MessageString ("Context of type class " ++ show (show name) ++ " refers to variables other variables then the one declared in the type class")
      , [ MessageString ("You use: "++prettyOrList (map (show . show) vars)++" .")]
      )

   InvalidInstanceConstraint instanceName contextName var ->
      ( MessageString ("Context item: " ++ show contextName ++ " with variable: " ++ show var ++ " is not valid for instance of: " ++ show instanceName
                                        ++ ".")
      , [ MessageString ("You must use the variable from the context in the instance type.") ]
      )

   ClassVariableNotInMethodSignature className classVariable methods ->
      ( MessageString ("Class method signature must mention class variable: " ++ show classVariable ++ " in class: " ++ show className ++ ".")
      , [MessageString ("The type signatures of the methods: " ++ prettyAndList (map show methods)
                       ++ " must mention type variable: " ++ show classVariable ++ ".")]
      )

   TypeClassOverloadRestr className members ->
      ( MessageString ("Class members may not have names occoring at top level, in class:  " ++ show className ++ ".")
      , [MessageString ("Name: " ++ show member ++ " also used at top level.")
        | member <- members]
      )

   TypeSynonymInInstance _ inst ->
      ( MessageString ("Type synonyms are not allowed as types for instances, in : "  ++ show inst ++ ".")
      , []
      )

   OverlappingInstance className tp ->
      ( MessageString ("Overlapping instances found for class: " ++ show className ++ " for type constructor: " ++ show tp ++ ".")
      , []
      )

   MissingSuperClass _ inst missing ->
      ( MessageString ("Instance for: "  ++ show missing ++ " is needed for the instance of: " ++ show inst ++ " but was not defined.")
      ,  []
      )

   Undefined entity name inScope hints ->
      ( MessageString ("Undefined " ++ show entity ++ " " ++ show (show name))
      , map MessageString hints
        ++
        [ MessageString ("Did you mean " ++ prettyOrList (map (show . show) xs) ++ " ?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )

   UndefinedClass name inScope ->
      ( MessageString ("Trying to instantiate unknown class " ++ show name ++ ".")
      , [ MessageString ("Did you mean " ++ prettyOrList (map (show . show) xs) ++ " ?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )

   UndefinedFunctionForClass instanceName name hints ->
      ( MessageString ("Function " ++ show name ++ " not defined in class: " ++ show instanceName ++ ".")
      , [ MessageString ("Did you mean " ++ prettyOrList (map (show . show) xs) ++ "?")
        | let xs = sensiblySimilar name hints, not (null xs)
        ]
      )

   InvalidInstanceType instanceName ->
      ( MessageString ("Invalid instance type for: " ++ show instanceName ++ ".")
      , [ MessageString ("Type application is only allowed when arguments are type variables")]
      )

   TypeSignatureInInstance instanceName names ->
      ( MessageString ("Type signature for: " ++ prettyAndList (map (show . show) names) ++ " in instance for: " ++ show instanceName ++ ".")
      , [ MessageString ("Type signatures for class members should be defined in class definition.")]
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
               (importRanges, _) = partition isImportRange nameRanges
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
{-        fromRanges = [ if isImportRange range then
                         Range_Range position position
                       else
                         range
                     | range <- nameRanges
                     , let position = getRangeEnd range
                     ] -}
        nameRanges   = sort (map getNameRange names)

   LastStatementNotExpr _ ->
      ( MessageString "Last generator in do {...} must be an expression ", [])

   TypeVarApplication name ->
      ( MessageString ("Type variable " ++ show (show name) ++ " cannot be applied to another type"), [])

   ArityMismatch entity name expected actual ->
      ( MessageString ( capitalize (show entity) ++ " " ++show (show name) ++
           " should have " ++ prettyNumberOfParameters expected ++
           ", but has " ++ if actual == 0 then "none" else show actual), [])

   RecursiveTypeSynonyms [string] ->
      ( MessageString ("Recursive type synonym " ++ show (show string))
      , [ MessageString "Use \"data\" to write a recursive data type" ]
      )

   RecursiveTypeSynonyms strings ->
      ( MessageString ("Recursive type synonyms " ++
            prettyAndList (map (show . show) (sortNamesByRange strings)))
      , []
      )

   DefArityMismatch name maybeExpected _ ->
      ( MessageString ("Arity mismatch in function bindings for " ++ show (show name))
      , [ MessageString (show arity ++ " parameters in most of the clauses")
        | Just arity <- [maybeExpected]
        ]
      )

   PatternDefinesNoVars _ ->
      ( MessageString "Left hand side pattern defines no variables", [])

   WrongFileName fileName moduleName _ ->
      ( MessageString ("The file name " ++ show fileName ++ " doesn't match the module name " ++ show moduleName), [])

   IntLiteralTooBig _ value ->
      ( MessageString ("Integer literal (" ++ value ++ ") too big")
      , [ MessageString $ "Maximum is " ++ show maxInt ]
      )

   OverloadedRestrPat name ->
      ( MessageString ("Illegal overloaded type signature for " ++ show (show name))
      , [MessageString "Only functions and simple patterns can have an overloaded type"]
      )

   OverloadingDisabled _ ->
      ( MessageString "Cannot handle contexts when overloading is disabled"
      , []
      )

   WrongOverloadingFlag False ->
      ( MessageString "Using overloaded Prelude while overloading is not enabled"
      , [MessageString "Compile with --overloading, or use the simple Prelude"]
      )

   WrongOverloadingFlag True ->
      ( MessageString "Using simple Prelude while overloading is enabled"
      , [MessageString "Compile without --overloading, or use the overloaded Prelude"]
      )

   AmbiguousContext name ->
      ( MessageString ("Type variable " ++ show (show name) ++ " appears in the context but not in the type")
      , []
      )

   UnknownClass name ->
      ( MessageString ("Unknown class " ++ show (show name))
      , []
      )

   NonDerivableClass name ->
      ( MessageString ("Cannot derive class " ++ show (show name))
      , [MessageString "Only Show and Eq instances can be derived"]
      )

   CannotDerive name tps ->
      ( MessageString ("Cannot derive instance for class " ++ show (show name))
      , let msg = MessageCompose (intersperse (MessageString ", ") (map (MessageType . toTpScheme) tps))

        in [ MessageCompose
            [ MessageString "There "
            , MessageString ( if length tps == 1 then "is " else "are ")
            , MessageString ("no " ++ show name ++ " instance")
            , MessageString ( if length tps == 1 then " " else "s ")
            , MessageString "for "
            , msg
            ]
           ]
      )

   TupleTooBig _ ->
      ( MessageString "Tuples can have up to 10 elements"
      , []
      )
   --IncorrectConstructorResult Range Name {- Constructor -} TpScheme {- Given result type -} TpScheme {- Expected result type -} 
   IncorrectConstructorResult _ n given expected ->
         (  MessageCompose [
            MessageString "Result of given type ",
            MessageString (show given),
            MessageString " does not match ",
            MessageString (show expected),
            MessageString " in constructor ",
            MessageString (show n)
         ]
      ,  [
            
         ]
      )
   MissingGADTOption ->
      (MessageString "GADTs used, but GADTs are not enabled"
      , [MessageString "Enable the option to use GADTs by using --gadts"])
   DuplicateTypeFamily (n1, _) ->
      (MessageString ("Found conflicting Type Families with the name " ++ show n1)
      , [MessageString "Type families have to be uniquely named"])
   UndefinedTypeFamily name inScope ->
      ( MessageString ("Trying to instantiate unknown type family " ++ show name ++ ".")
      , [ MessageString ("Did you mean " ++ prettyOrList (map (show . show) xs) ++ " ?")
        | let xs = sensiblySimilar name inScope, not (null xs)
        ]
      )
   WronglySaturatedTypeFamily n dl tl ->
      ( MessageString ("Instance for type family " ++ show n ++ " has " ++ show tl ++ " arguments but its declaration requires " ++ show dl)
      , [MessageString "Type family instances may not be over or under saturated"])
   WronglyAlignedATS n1 n2 t1 t2 ->
      ( MessageString ("The type " ++ show t2 ++ " in associated type synonym instance " 
                        ++ show n1 ++ " does not align with " ++  show t1 ++ " from the class instance " ++ show n2)
      , [MessageString "Equal variables in the class declaration and the associated type synonym declaration must be assigned the same type."])

   _ -> internalError "StaticErrors.hs" "showError" "unknown type of Error"

makeUndefined :: Entity -> Names -> Names -> [Error]
makeUndefined entity names inScope = [ Undefined entity name inScope [] | name <- names ]

makeDuplicated :: Entity -> [Names] -> [Error]
makeDuplicated entity nameslist = [ Duplicated entity names | names <- nameslist ]

undefinedConstructorInExpr :: Name -> Names -> Names -> Error
undefinedConstructorInExpr name sims tyconNames =
   let hints = [ "Type constructor "++show (show name)++" cannot be used in an expression"
               | name `elem` tyconNames
               ]
   in Undefined Constructor name sims hints

undefinedConstructorInPat :: Bool -> Name -> Names -> Names -> Error
undefinedConstructorInPat lhsPattern name sims tyconNames =
   let hints = [ "Use identifiers starting with a lower case letter to define a function or a variable"
               | lhsPattern
               ] ++
               [ "Type constructor "++show (show name)++" cannot be used in a pattern"
               | name `elem` tyconNames
               ]

   in Undefined Constructor name sims hints

makeNoFunDef :: Entity -> Names -> Names -> [Error]
makeNoFunDef entity names inScope = [ NoFunDef entity name inScope | name <- names ]

-- Log-codes for Errors
errorsLogCode :: Errors -> String
errorsLogCode [] = "[]"
errorsLogCode xs = foldr1 (\x y -> x++","++y) (map errorLogCode xs)

errorLogCode :: Error -> String
errorLogCode anError = case anError of
          NoFunDef entity _ _                     -> "nf" ++ code entity
          Undefined entity _ _ _                  -> "un" ++ code entity
          Duplicated entity _                     -> "du" ++ code entity
          LastStatementNotExpr _                  -> "ls"
          WrongFileName _ _ _                     -> "wf"
          TypeVarApplication _                    -> "tv"
          ArityMismatch _ _ _ _                   -> "am"
          DefArityMismatch _ _ _                  -> "da"
          RecursiveTypeSynonyms _                 -> "ts"
          PatternDefinesNoVars _                  -> "nv"
          IntLiteralTooBig _ _                    -> "il"
          OverloadingDisabled _                   -> "od"
          OverloadedRestrPat _                    -> "or"
          WrongOverloadingFlag _                  -> "of"
          AmbiguousContext _                      -> "ac"
          UnknownClass _                          -> "uc"
          NonDerivableClass _                     -> "nd"
          CannotDerive _ _                        -> "cd"
          TupleTooBig _                           -> "tt"
          NoTypeDefInClass _ _ _                  -> "tc"
          FunctionInMultipleClasses _ _ _         -> "fm"
          MultiParameterTypeClass _ _ _           -> "mt"
          DefNonUniqueInstanceVars _ _            -> "dn"
          ClassMethodContextError _ _ _ _         -> "ce"
          ClassVariableNotInMethodSignature _ _ _ -> "cv"
          InvalidContext _ _ _                    -> "ic"
          UndefinedClass _ _                      -> "nc"
          InvalidInstanceConstraint _ _ _         -> "ii"
          InvalidInstanceType _                   -> "it"
          UndefinedFunctionForClass _ _ _         -> "fc"
          TypeSignatureInInstance _ _             -> "ti"
          TypeClassOverloadRestr _ _              -> "to"
          TypeSynonymInInstance _ _               -> "si"
          DuplicateClassName _                    -> "dc"
          DuplicatedClassImported _               -> "di"
          OverlappingInstance _ _                 -> "oi"
          MissingSuperClass _ _ _                 -> "ms"
          IncorrectConstructorResult _ _ _ _      -> "wc"
          MissingGADTOption                       -> "mg"
          DuplicateTypeFamily _                   -> "dtf"
   where code entity = fromMaybe "??"
                     . lookup entity
                     $ [ (TypeSignature    ,"ts"), (TypeVariable         ,"tv"), (TypeConstructor,"tc")
                       , (Definition       ,"de"), (Constructor          ,"co"), (Variable       ,"va")
                       , (Import           ,"im"), (ExportVariable       ,"ev"), (ExportModule   ,"em")
                       , (ExportConstructor,"ec"), (ExportTypeConstructor,"et"), (Fixity         ,"fx")
                       ]
