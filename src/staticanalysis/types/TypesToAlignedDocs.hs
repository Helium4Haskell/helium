-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypesToAlignedDocs.hs : Shos and align two types
--
-------------------------------------------------------------------------------

module TypesToAlignedDocs where

import List     ( (\\), union )
import Types
import PPrint
   
-- shows and aligns the two types
showTwoTypesSpecial :: (Tp,Tp) -> (PPrint.Doc,PPrint.Doc)
showTwoTypesSpecial (t1,t2) = let vars = ftv [t1,t2]
                                  cons = constantsInType t1 `union` constantsInType t2
                                  newcons = [ TCon [c] | c <- ['a'..], [c] `notElem` cons ]
                                  sub  = listToSubstitution (zip vars newcons)
                              in showTwoTypes (sub |-> t1) (sub |-> t2)

showTwoTypes :: Tp -> Tp -> (PPrint.Doc,PPrint.Doc)
showTwoTypes t1 t2 = case (leftSpine t1,leftSpine t2) of 
       ((TCon "->",_),(TCon "->",_)) -> let (listA,tpA)   = functionSpine t1
                                            (listB,tpB)   = functionSpine t2
                                            listLength    = length listA `min` length listB
                                            (listA',tpA') = let (xs,ys) = splitAt listLength listA
                                                            in (xs,foldr (.->.) tpA ys)
                                            (listB',tpB') = let (xs,ys) = splitAt listLength listB
                                                            in (xs,foldr (.->.) tpB ys)
                                            (adocs,bdocs) = unzip (map (rec (<1)) (zip listA' listB'))
                                            (adoc ,bdoc ) = rec (const False) (tpA',tpB')
                                        in (funDocs (adocs++[adoc]),funDocs (bdocs++[bdoc]))
       ((TVar i,[]),(TVar j,[])) -> let (s1,s2) = sameLength ('v' : show i,'v' : show j)
                                    in (PPrint.text s1,PPrint.text s2)
       ((TCon s,[]),(TCon t,[])) -> let (s1,s2) = sameLength (s,t)
                                    in (PPrint.text s1,PPrint.text s2)
       ((TCon "[]",[t1]),(TCon "[]",[t2])) -> let (d1,d2) = rec (const False) (t1,t2) 
                                              in (PPrint.squares d1,PPrint.squares d2) 
       ((TCon s,ss),(TCon t,tt)) | isTupleConstructor s && s==t && length ss == length tt
            -> let (ssdocs,ttdocs) = unzip (map (rec (const False)) (zip ss tt))
               in (tupleDocs ssdocs,tupleDocs ttdocs)
       ((x@(TCon c),xs),(y@(TCon d),ys)) | c == d && length xs == length ys 
            -> let (xsdocs,ysdocs) = unzip (map (rec (<2)) (zip (x:xs) (y:ys))) 
               in (appDocs xsdocs,appDocs ysdocs)
       _ -> let (s1,s2) = sameLength (show t1,show t2)
            in (PPrint.text s1,PPrint.text s2)
       
    where rec p (t1,t2) = let (s1,s2) = showTwoTypes t1 t2
                              bool1   = p (priorityOfType t1)
                              bool2   = p (priorityOfType t2)
                          in ( (parIf bool1 s1) <> (PPrint.text (if bool2 && not bool1 then "  " else ""))
                             , (parIf bool2 s2) <> (PPrint.text (if bool1 && not bool2 then "  " else ""))
                             )
          parIf True  = PPrint.parens
          parIf False = id
          sameLength (s1,s2) = let i = length s1 `max` length s2
                               in (take i (s1++repeat ' '),take i (s2++repeat ' '))

          funDocs :: [Doc] -> Doc
          funDocs = PPrint.group . foldl1 (\d1 d2 -> d1 <> line <> text "->" <+> d2)

          appDocs :: [Doc] -> Doc
          appDocs = foldl1 (\d1 d2 -> PPrint.group $ d1 <> line <> d2)

          tupleDocs :: [Doc] -> Doc
          tupleDocs [] = PPrint.text "()"
          tupleDocs ds = PPrint.hang 0 $ PPrint.group  (PPrint.text "(" <> 
                    foldl1 (\d1 d2 -> d1 <> line <> PPrint.text "," <+> d2) ds) 
                    <> PPrint.text ")"                               


       
   
