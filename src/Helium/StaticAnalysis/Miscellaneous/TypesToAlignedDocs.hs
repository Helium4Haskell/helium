{-| Module      :  TypesToAlignedDocs
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Functions to align and show types.
-}

module Helium.StaticAnalysis.Miscellaneous.TypesToAlignedDocs (qualifiedTypesToAlignedDocs, typesToAlignedDocs, qualifiedPolyTypesToAlignedDocs) where

import Data.List     ( transpose, intercalate )
import Top.Types
import Text.PrettyPrint.Leijen
import qualified Text.PrettyPrint.Leijen as PPrint

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Rhodium.TypeGraphs.GraphProperties

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Alpha

import Debug.Trace

qualifiedPolyTypesToAlignedDocs :: [PolyType ci] -> [PPrint.Doc]
qualifiedPolyTypesToAlignedDocs pts = let
        (css, ms) = unzip $ map extractPolyType pts
        docContexts = map text . sameLengthRight . map showContext $ css
        docTypes = typesToAlignedDocs (map monoTypeToTp ms)
      in if null (concat css)
        then docTypes
        else zipWith (<>) docContexts docTypes
    where
      extractPolyType (PolyType_Mono cs m) = (filter hasConstraintInformation cs, m)
      showContext :: [Constraint ci] -> String
      showContext [] = ""
      showContext [c] = showClassConstraint c ++ " => "
      showContext cs = "(" ++ intercalate ", " (map showClassConstraint cs) ++ ") => "
      showClassConstraint :: Constraint ci -> String
      showClassConstraint (Constraint_Class cn [m] _) = cn ++ " " ++ show m

monoTypeToTp :: MonoType -> Tp
monoTypeToTp (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) _) = TCon "String"
monoTypeToTp (MonoType_Var (Just s) _ _) = TCon s
monoTypeToTp (MonoType_Var Nothing n _) = TVar (fromInteger (name2Integer n))
monoTypeToTp (MonoType_Con n _)   = TCon n
monoTypeToTp (MonoType_App f a _) = TApp (monoTypeToTp f) (monoTypeToTp a)
monoTypeToTp (MonoType_Fam s a _) = foldl TApp (TCon s) (map monoTypeToTp a)


qualifiedTypesToAlignedDocs :: [QType] -> [PPrint.Doc]
qualifiedTypesToAlignedDocs qtps = 
   let (contexts, types) = unzip (map split qtps)
       docContexts = map text . sameLengthRight . map showContext $ contexts
       docTypes    = typesToAlignedDocs types
   in if null (concat contexts)
         then docTypes
         else zipWith (<>) docContexts docTypes

typesToAlignedDocs :: Tps -> [PPrint.Doc]
typesToAlignedDocs []  = []
typesToAlignedDocs tps

   | allFunctionType
     = let functionSpines = map functionSpine tps
           shortestSpine  = minimum (map (length . fst) functionSpines)
           tupleSpines    = map partOfSpine functionSpines
           partOfSpine (ts, t) = let (xs, ys) = splitAt shortestSpine ts 
                                 in (xs, foldr (.->.) t ys)
           (left, right)  = unzip tupleSpines
           docsLeft       = recs (<1) left
           docsRight      = rec_  (const False) right
       in map funDocs (zipWith (\xs x -> xs++[x]) docsLeft docsRight)
  
   | allVariable
     = map PPrint.text (sameLength [ 'v' : show i | (TVar i, _) <- spines])

   | allConstant
     = map PPrint.text (sameLength [ s | (TCon s, _) <- spines])
   
   | allListType
     = map PPrint.brackets (rec_ (const False) (map (head . snd) spines))

   | allSameTuple
     = map tupleDocs (recs (const False) (map snd spines))   
     
   | allSameConstructor 
     = map appDocs (recs (<2) [ x:xs | (x, xs) <- spines ])
           
   | otherwise 
     = map PPrint.text $ sameLength $ map show tps
   
   where spines = map leftSpine tps
         allSameConstructor = all isTCon (map fst spines)
                           && allEqual [ s | (TCon s, _) <- spines ]
                           && allEqual [ length xs | (_, xs) <- spines ]
         allSameTuple       = all isTCon (map fst spines)
                           && all isTupleConstructor [ s | (TCon s, _) <- spines ]
                           && allEqual [ s | (TCon s, _) <- spines ]
                           && allEqual [ length xs | (_, xs) <- spines ]      
         allListType        = all isTCon (map fst spines)
                           && all ("[]"==) [ s | (TCon s, _) <- spines ]
                           && all (1==) [length xs | (_, xs) <- spines ]
         allConstant        = all isTCon (map fst spines)
                           && all null (map snd spines)
         allVariable        = all isTVar (map fst spines)
                           && all null (map snd spines)
         allFunctionType    = all isTCon (map fst spines)
                           && all ("->"==) [ s | (TCon s, _) <- spines ]
                           && all (2==) [length xs | (_, xs) <- spines ]

recs :: (Int -> Bool) -> [Tps] -> [[PPrint.Doc]]
recs predicate = transpose . map (rec_ predicate) . transpose 

rec_ :: (Int -> Bool) -> Tps -> [PPrint.Doc]    
rec_ predicate tps = 
   let docs  = typesToAlignedDocs tps     
       bools = map (predicate . priorityOfType) tps
       maybeParenthesize b doc
          | b         = PPrint.parens doc
          | or bools  = doc <> PPrint.text "  "
          | otherwise = doc
   in zipWith maybeParenthesize bools docs

--showTwoTypesSpecial (t1,t2) = 
--   let [d1,d2] = typesToAlignedDocs [t1,t2]
--   in (d1,d2)

--showTwoTypes = showTwoTypesSpecial 
   
allEqual :: Eq a => [a] -> Bool
allEqual []     = True
allEqual (x:xs) = all (x==) xs
 
sameLength :: [String] -> [String]
sameLength xs = 
   let n = maximum (0 : map length xs)  
       f = take n . (++repeat ' ') 
   in map f xs

sameLengthRight :: [String] -> [String]
sameLengthRight = 
   map reverse . sameLength . map reverse

appDocs :: [Doc] -> Doc
appDocs = foldl1 (\d1 d2 -> PPrint.group $ d1 <> line <> d2)

tupleDocs :: [Doc] -> Doc
tupleDocs [] = PPrint.text "()"
tupleDocs ds = PPrint.hang 0 $ PPrint.group  (PPrint.text "(" <> 
          foldl1 (\d1 d2 -> d1 <> line <> PPrint.text "," <+> d2) ds) 
          <> PPrint.text ")"   

funDocs :: [Doc] -> Doc
funDocs = PPrint.group . foldl1 (\d1 d2 -> d1 <> line <> text "->" <+> d2)          
