module UHA_Range where

import UHA_Syntax
import Id(Id, stringFromId)
import Utils(internalError)
import Maybe(isJust)
import List(sort, partition)

instance Show Range where
    show = showRange
    
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

getNameRange :: Name -> Range
getNameRange (Name_Identifier r _ _) = r
getNameRange (Name_Operator   r _ _) = r
getNameRange (Name_Special    r _ _) = r

setNameRange :: Name -> Range -> Name
setNameRange (Name_Identifier _ s e) r = Name_Identifier r s e
setNameRange (Name_Operator   _ s e) r = Name_Operator   r s e
setNameRange (Name_Special    _ s e) r = Name_Special    r s e

rangeFromImportDeclaration :: ImportDeclaration -> Range
rangeFromImportDeclaration importDecl =
    case importDecl of
        ImportDeclaration_Import r _ _ _ _ -> r
        ImportDeclaration_Empty r -> r
    
mergeRanges :: Range -> Range -> Range
mergeRanges
    (Range_Range
        (Position_Position startF1 startL1 startC1)
        (Position_Position stopF1  stopL1  stopC1 )
    )
    (Range_Range
        (Position_Position startF2 startL2 startC2)
        (Position_Position stopF2  stopL2  stopC2 )
    )
    | startF1 == stopF1 && startF2 == stopF2 && startF1 == startF2 =
        let
            (startL, startC, stopL, stopC) =
                if startL1 < startL2 || (startL1 == startL2 && startC1 <= startC2) then
                    (startL1, startC1, stopL2, stopC2)
                else
                    (startL2, startC2, stopL1, stopC1)
        in
            Range_Range
                (Position_Position startF1 startL startC)
                (Position_Position startF1 stopL  stopC )
mergeRanges _ _ = Range_Range Position_Unknown Position_Unknown

-- In UHA there is no room for the position of built-in constructs
noRange :: Range
noRange = Range_Range Position_Unknown Position_Unknown

-----------------------------------------------------
-- Misuse the second position of the range to
-- store where the name was imported from.
makeImportRange :: Id -> Id -> Range
makeImportRange importedInId importedFromId =
    Range_Range
        (Position_Position (stringFromId importedInId  ) 0 0)
        (Position_Position (stringFromId importedFromId) 0 0)

isImportRange :: Range -> Bool
isImportRange = isJust . modulesFromImportRange

isImportName :: Name -> Bool
isImportName = isImportRange.getNameRange

modulesFromImportRange :: Range -> Maybe (String, String)
modulesFromImportRange
    (Range_Range
        (Position_Position importedIn   0 0)
        (Position_Position importedFrom 0 0)
    ) =
        Just (importedIn, importedFrom)
modulesFromImportRange _ = Nothing
-- End of misuse functions
-----------------------------------------------------
getRangeStart :: Range -> Position
getRangeStart (Range_Range start end) = start

getRangeEnd :: Range -> Position
getRangeEnd (Range_Range start end) = end

getStatementRange :: Statement -> Range
getStatementRange s = 
    case s of
        Statement_Expression r _ -> r
        Statement_Let r _ -> r
        Statement_Generator r _ _ -> r
        Statement_Empty r -> r
        _ -> internalError "UHA_Utils" "getStatementRange" "unknown kind of statement"
        
getPatRange :: Pattern -> Range
getPatRange (Pattern_As r _ _) = r
getPatRange (Pattern_Constructor r _ _) = r
getPatRange (Pattern_InfixConstructor r _ _ _) = r
getPatRange (Pattern_Irrefutable r _) = r
getPatRange (Pattern_List r _) = r
getPatRange (Pattern_Literal r _) = r
getPatRange (Pattern_Negate r _) = r
getPatRange (Pattern_Parenthesized r _) = r
getPatRange (Pattern_Record r _ _) = r
getPatRange (Pattern_Successor r _ _) = r
getPatRange (Pattern_Tuple r _) = r
getPatRange (Pattern_Variable r _) = r
getPatRange (Pattern_Wildcard r) = r
getPatRange _ = internalError "UHA_Utils" "getPatRange" "unknown pattern"

getExprRange :: Expression -> Range
getExprRange (Expression_Literal            r _    ) = r
getExprRange (Expression_Variable           r _    ) = r
getExprRange (Expression_Constructor        r _    ) = r
getExprRange (Expression_Parenthesized      r _    ) = r
getExprRange (Expression_NormalApplication  r _ _  ) = r
getExprRange (Expression_InfixApplication   r _ _ _) = r
getExprRange (Expression_If                 r _ _ _) = r
getExprRange (Expression_Lambda             r _ _  ) = r
getExprRange (Expression_Case               r _ _  ) = r
getExprRange (Expression_Let                r _ _  ) = r
getExprRange (Expression_Do                 r _    ) = r
getExprRange (Expression_List               r _    ) = r
getExprRange (Expression_Tuple              r _    ) = r
getExprRange (Expression_Comprehension      r _ _  ) = r
getExprRange (Expression_Typed              r _ _  ) = r
getExprRange (Expression_RecordConstruction r _ _  ) = r
getExprRange (Expression_RecordUpdate       r _ _  ) = r
getExprRange (Expression_Enum               r _ _ _) = r
getExprRange (Expression_Negate             r _    ) = r

showRanges :: [Range] -> String
showRanges rs = showRanges' (sort rs)
  where
    showRanges' :: [Range] -> String
    showRanges' (range:ranges) = show range ++ concatMap ((", " ++) . show) ranges
    showRanges' [] = "<unknownNR>"

-- !!!! In the special case that the range corresponds to the import range,
-- the module name of the second position should be printed
showRange :: Range -> String
showRange range@(Range_Range startPos endPos)
    | isImportRange range =
        moduleFromPosition endPos
    | otherwise =
        showPosition startPos
showRange _ =
    "<unknown range>"

showPosition :: Position -> String
showPosition (Position_Position _ line column) =
    "(" ++ show line ++ "," ++ show column ++ ")"
showPosition _ =
    "<unknown position>"

sortRanges :: [Range] -> [Range]
sortRanges ranges = let (xs,ys) = partition isImportRange ranges
                    in sort ys ++ xs
                                        
moduleFromPosition :: Position -> String
moduleFromPosition pos =
    case pos of
        Position_Position mod _ _ -> mod
        _                         -> internalError "UHA_Range" "moduleFromPosition" "unknown position"
