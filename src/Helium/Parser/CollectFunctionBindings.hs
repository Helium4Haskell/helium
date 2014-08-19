{-| Module      :  CollectFunctionBindings
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Parser.CollectFunctionBindings where

import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils ()
import Helium.Syntax.UHA_Range
import Helium.Utils.Utils

-- Assumption: each FunctionBindings contains exactly one FunctionBinding

decls :: Declarations -> Declarations
decls = decls' . mergeFeedback

mergeFeedback :: Declarations -> Declarations
mergeFeedback [] = []
mergeFeedback ((Declaration_FunctionBindings _ [FunctionBinding_Feedback rfb fb _]):ds) =
    case mergeFeedback ds of
      ((Declaration_FunctionBindings rdcls (funb : fbs)) : mds) ->
          Declaration_FunctionBindings
            (mergeRanges rfb rdcls)
            (FunctionBinding_Feedback (mergeRanges rfb $ rangeOfFunctionBinding funb) fb funb : fbs) : mds
      rs -> rs
mergeFeedback (x : xs) = x : mergeFeedback xs

decls' :: Declarations -> Declarations
decls' [] = []
decls' (d@(Declaration_FunctionBindings _ [_]):ds) =
    let mn = nameOfDeclaration d
        (same, others) = span ((== mn) . nameOfDeclaration) (d:ds)
        fs = map functionBindingOfDeclaration same
    in Declaration_FunctionBindings 
        (mergeRanges (rangeOfFunctionBinding (head fs)) (rangeOfFunctionBinding (last fs)))
        fs
       :
       decls' others
decls' (Declaration_FunctionBindings _ _:_) =
    internalError "CollectFunctionBindings" "decls" "not exactly one function binding in FunctionBindings"
decls' (d:ds) = d : decls' ds

functionBindingOfDeclaration :: Declaration -> FunctionBinding
functionBindingOfDeclaration (Declaration_FunctionBindings _ [f]) = f
functionBindingOfDeclaration _ = 
    internalError "CollectFunctionBindings" "getFunctionBinding" "unexpected declaration kind"

rangeOfFunctionBinding :: FunctionBinding -> Range
rangeOfFunctionBinding (FunctionBinding_FunctionBinding r _ _) = r
rangeOfFunctionBinding (FunctionBinding_Feedback r _ _) = r
rangeOfFunctionBinding (FunctionBinding_Hole _ _) = error "not supported"

nameOfDeclaration :: Declaration -> Maybe Name
nameOfDeclaration d =
    case d of 
        Declaration_FunctionBindings _ [FunctionBinding_FunctionBinding _ l _] ->
            Just (nameOfLeftHandSide l)
        Declaration_FunctionBindings r [FunctionBinding_Feedback _ _ fb] ->
            nameOfDeclaration (Declaration_FunctionBindings r [fb])
        _ -> Nothing

nameOfLeftHandSide :: LeftHandSide -> Name
nameOfLeftHandSide lhs =
    case lhs of
        LeftHandSide_Function _ n _ -> n
        LeftHandSide_Infix _ _ n _ -> n
        LeftHandSide_Parenthesized _ innerLhs _ -> nameOfLeftHandSide innerLhs

mergeCaseFeedback :: Alternatives -> Alternatives
mergeCaseFeedback [] = []
mergeCaseFeedback (Alternative_Feedback r v _ : rs) =
  case mergeCaseFeedback rs of
    []       -> []
    (x : xs) -> Alternative_Feedback r v x : xs
mergeCaseFeedback (x : xs) = x : mergeCaseFeedback xs
