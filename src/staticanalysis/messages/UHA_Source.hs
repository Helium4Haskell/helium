module UHA_Source where

import OneLiner
import UHA_Range
import UHA_Syntax
import UHA_Utils
import qualified UHA_OneLine as PP

data UHA_Source =
     UHA_Expr   Expression                 
   | UHA_Pat    Pattern
   | UHA_Stat   Statement
   | UHA_Qual   Qualifier
   | UHA_FB     FunctionBinding
   | UHA_Decl   Declaration
   | UHA_Decls  Declarations
          
rangeOfSource :: UHA_Source -> Range
rangeOfSource source =
   case source of
      UHA_Expr  expr  -> getExprRange expr
      UHA_Pat   pat   -> getPatRange pat
      UHA_Stat  stat  -> getStatementRange stat
      UHA_Qual  qual  -> getQualifierRange qual
      UHA_FB    fb    -> getFBRange fb
      UHA_Decl  decl  -> getDeclarationRange decl
      UHA_Decls decls -> if null decls then noRange else foldr1 mergeRanges (map getDeclarationRange decls)

oneLinerSource :: UHA_Source -> OneLineTree
oneLinerSource source = 
   case source of
      UHA_Expr  expr  -> fst (PP.sem_Expression expr)
      UHA_Pat   pat   -> fst (PP.sem_Pattern pat)
      UHA_Stat  stat  -> fst (PP.sem_Statement stat)
      UHA_Qual  qual  -> fst (PP.sem_Qualifier qual)
      UHA_FB    fb    -> fst (PP.sem_FunctionBinding fb)
      UHA_Decl  decl  -> fst (PP.sem_Declaration decl)
      UHA_Decls decls -> PP.encloseSep "{" "; " "}" (fst (PP.sem_Declarations decls))

descriptionOfSource :: UHA_Source -> String
descriptionOfSource source = 
   case source of
      UHA_Expr  expr  -> "expression"
      UHA_Pat   pat   -> "pattern"
      UHA_Stat  stat  -> "statement"
      UHA_Qual  qual  -> "qualifier"
      UHA_FB    fb    -> "function binding"
      UHA_Decl  decl  -> "declaration"
      UHA_Decls decls -> "declarations"
      
convertSources :: (UHA_Source, Maybe UHA_Source) -> [(String, UHA_Source)]
convertSources (source, maybeSource) = 
   (descriptionOfSource source, source) : maybe [] (\s -> [(f s, s)]) maybeSource
  where
    f (UHA_Expr (Expression_Variable _ name))
       | isConstructor  name = "constructor"
       | isOperatorName name = "operator"
    f _                      = "term"      
