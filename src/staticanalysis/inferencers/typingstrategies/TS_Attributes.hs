module TS_Attributes where

import Char (isAlphaNum)

type AttributeTable   result = [((String, Maybe String), result)]
type AttributeAlgebra result = (String -> result, AttributeTable result, (String, Maybe String) -> result) 

substituteAttributes :: AttributeAlgebra result -> String -> [result]
substituteAttributes (funString, attributetable, funNotInTable) = rec
   where rec "" = []
         rec xs = let (begin, rest) = span (/= '@') xs
                  in case rest of
                        []           -> [funString begin]
                        '@':rest     -> let (variableName, as) = span isAlphaNum rest
                                        in case as of
                                              '@':rest -> let key   = (variableName, Nothing)
                                                              value = maybe (funNotInTable key) id (lookup key attributetable)
                                                          in funString begin : value : rec rest                                              
                                              '.':rest -> let (fieldName, bs) = span isAlphaNum rest
                                                          in case bs of
                                                                '@':rest -> let key   = (variableName, Just fieldName)
                                                                                value = maybe (funNotInTable key) id (lookup key attributetable)
                                                                            in funString begin : value : rec rest
                                                                _ -> []
                                              _ -> []

showAttribute :: (String, Maybe String) -> String
showAttribute (s, ms) = "@" ++ s ++ maybe "" ('.':) ms ++ "@"
