{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.TopSolver where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import qualified Text.ParserCombinators.Parsec.Language as P
import Helium.Top.Top.Constraint
import Helium.Top.Top.Types
import Helium.Top.Top.Constraint.Information
import Helium.Top.Top.Constraint.Qualifier
import Helium.Top.Top.Constraint.Equality
import Helium.Top.Top.Constraint.Polymorphism (PolymorphismConstraint(..))
import Helium.Top.Top.Interface.TypeInference
import Helium.Top.Top.Solver
import Helium.Top.Top.Solver.TypeGraph
import Helium.Top.Utils (internalError)
import Data.Char (isDigit, isLower)
import Data.List (intercalate, intersperse)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import System.Environment (getArgs)
import Control.Monad (void, liftM)

---------------------------------------------------------------------
-- * Top logo

logo :: [String]
logo = [ "__ __|"        
       , "  |  _ \\  _ \\"
       , " _|\\___/ .__/"
       , "        _|"
       ]

---------------------------------------------------------------------
-- * Top constraint information

newtype TopInfo = TopInfo [(String, String)]

instance Show TopInfo where 
   show (TopInfo xs)
      | null xs   = "[]"
      | otherwise = snd (last xs)

addTopInfo :: String -> String -> TopInfo -> TopInfo
addTopInfo s1 s2 (TopInfo xs) = TopInfo ((s1, s2) : xs)

instance TypeConstraintInfo TopInfo where
   ambiguousPredicate p    = addTopInfo "ambiguous predicate"  (show p)
   unresolvedPredicate p   = addTopInfo "unresolved predicate" (show p)
   equalityTypePair pair   = addTopInfo "type pair"            (show pair)
   parentPredicate p       = addTopInfo "parent predicate"     (show p)
   escapedSkolems is       = addTopInfo "escaped skolems"      (show is)
   neverDirective tuple    = addTopInfo "never directive"      (show tuple)
   closeDirective tuple    = addTopInfo "close directive"      (show tuple)
   disjointDirective t1 t2 = addTopInfo "disjoint directive"   (show (t1, t2))
   
instance PolyTypeConstraintInfo TopInfo where
   instantiatedTypeScheme s = addTopInfo "instantiated type scheme" (show s)
   skolemizedTypeScheme s   = addTopInfo "skolemized type scheme" (show s)
  
---------------------------------------------------------------------
-- * Top constraints

type TopQualifiers = Predicates
type TopConstraint = ConstraintSum EqualityConstraint
                        (ConstraintSum PolymorphismConstraint ExtraConstraint)
                        TopInfo
                 
class IsTopConstraint a where
   toTopCon :: a -> TopConstraint

instance IsTopConstraint (EqualityConstraint TopInfo) where
   toTopCon = SumLeft
   
instance IsTopConstraint (PolymorphismConstraint TopInfo) where
   toTopCon = SumRight . SumLeft

instance IsTopConstraint (ExtraConstraint TopInfo) where
   toTopCon = SumRight . SumRight                 

---------------------------------------------------------------------
-- * Top solve monad

-- type TopExtraState = () --(DependencyState TopInfo, (ImplicitParameterState TopInfo, SubtypingState TopInfo))
type TopSolve      = TG TopInfo --TypeGraphX TopInfo TopQualifiers TopExtraState
   {-
instance HasDep TopSolve TopInfo where
   depGet    = do (_, (_, (_, (x1, _)))) <- getX ; return x1
   depPut x1 = do (a, (b, (c, (_, xr)))) <- getX ; putX (a, (b, (c, (x1, xr))))

instance HasIP TopSolve TopInfo where
   ipGet    = do (_, (_, (_, (_, (x2, _ ))))) <- getX ; return x2
   ipPut x2 = do (a, (b, (c, (x1, (_, xr))))) <- getX ; putX (a, (b, (c, (x1, (x2, xr)))))

instance HasST TopSolve TopInfo where
   stGet    = do (_, (_, (_, (_, (_, x3))))) <- getX ; return x3
   stPut x3 = do (a, (b, (c, (x1, (x2, _))))) <- getX ; putX (a, (b, (c, (x1, (x2, x3))))) -}

---------------------------------------------------------------------
-- * Top lexer

lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
           ( P.haskellStyle 
                { P.reservedOpNames = ["==", "::", "<=", "=>", ":=", "~>", "<:" ] 
                , P.reservedNames   = ["forall", "Generalize", "Instantiate", "Skolemize", "Implicit",
                                       "Prove", "Assume", "MakeConsistent", "LogState", "Stop", 
                                       "Declare", {- "Enter", "Leave", "ContextReduction",-} 
                                       "Class", "Instance", "Never", "Close", 
                                       "Disjoint", "Default" ]
                })

runLex :: Parser (Constraints TopSolve, Int) -> String -> IO ()
runLex p
        = run (do { whiteSpace
                  ; x <- p
                  ; eof
                  ; return x
                  })

whiteSpace, comma, dot :: CharParser () ()
identifier             :: CharParser () String
parens, brackets       :: CharParser () a -> CharParser () a
reserved, reservedOp   :: String -> CharParser () ()

whiteSpace = P.whiteSpace lexer
comma      = Control.Monad.void (P.comma lexer)
dot        = Control.Monad.void (P.dot lexer)
parens     = P.parens lexer
brackets   = P.brackets lexer
identifier = P.identifier lexer
reserved   = P.reserved lexer
reservedOp = P.reservedOp lexer

---------------------------------------------------------------------
-- * Top parser and main function

main :: IO ()
main = do args <- getArgs
          case args of
             [filename] -> 
                do content <- readFile filename
                   runLex pStatements content
             _ -> do putStrLn "Incorrect number of arguments for topsolver"
                     putStrLn "Usage: topsolver <filename>"

run :: Parser (Constraints TopSolve, Int) -> String -> IO ()
run p input =
   case parse p "" input of
      Left err -> 
         do putStr "parse error at "
            print err
      Right (cset, unique) -> 
         do putStrLn (unlines logo)
            let result :: SolveResult TopInfo
                options = solveOptions { uniqueCounter = unique, typeSynonyms = stringAsTypeSynonym }
                (result, logm) = solve options cset typegraphConstraintSolverDefault
                
            print logm
            
            putStrLn . concat $ 
               "Substitution: " : intersperse ", "
                  [ show (i, lookupInt i (substitutionFromResult result)) 
                  | i <- dom (substitutionFromResult result) 
                  ]
               
            case errorsFromResult result of
               [] -> putStrLn "(No errors)"
               es -> let nice (info, lab) =
                            let TopInfo xs = addTopInfo "label" (show lab) info
                            in "{" ++ intercalate ", " [ a++"="++b | (a, b) <- xs] ++ "}"
                     in do putStr (unlines (map nice es))
                           putStrLn ("(Failed with "++show (length es)++" errors)")
  
pStatements :: Parser (Constraints TopSolve, Int)
pStatements = 
   do xs <- many pStatement
      let vars = S.filter (isLower . head) . S.unions . map (either fst fst) $ xs
          varmap = M.fromList (zip (S.elems vars) [0..])
          g (Left (_,f))   = liftConstraint (f varmap)
          g (Right (_, f)) = f varmap
      return (map g xs, S.size vars)

pStatement :: Parser (Either (Result TopConstraint) (Result (Constraint TopSolve)))
pStatement = 
   tryList (map (Control.Monad.liftM Right) decl ++ [ Control.Monad.liftM Left pConstraint ])
 where
   decl = [ pOperation {-, pSubtypingRule, pClassDecl, pInstanceDecl, pNeverDecl
          , pCloseDecl, pDisjointDecl, pDefaultDecl -}
          ]
          
---------------------------------------------------------------------
-- * Top constraint parser 

pConstraint :: Parser (Result TopConstraint)
pConstraint =
   do f <- tryList $
              change pEquality :
              map change
                 [ pGeneralize, pInstantiate, pExplicit, pSkolemize, pImplicit
                 ] ++
              map change 
                 [ pProve, pAssume
                 ]
      info <- pInfo
      let (list, fun) = f info
      return (S.fromList list, fun)
             
 where
   change parser =  
      do g <- parser 
         return $ \info ->
            let (a, b) = g info 
            in (a, toTopCon . b)
      
   pEquality =
      do t1 <- pType
         reservedOp "=="
         t2 <- pType
         return $ \info -> 
            ( allTypeConstants t1 ++ allTypeConstants t2
            , \varMap -> Equality (applyVarMap varMap t1) (applyVarMap varMap t2) info
            )
            
   pGeneralize = 
      do sv <- pSigmaVar   
         reservedOp ":="
         reserved "Generalize"
         (monos, tp) <- parens pMonosType
         return $ \info ->
            ( sv : allTypeConstants monos ++ allTypeConstants tp
            , \varMap -> Generalize (fromMaybe (-1) $ M.lookup sv varMap) (applyVarMap varMap monos, applyVarMap varMap tp) info
            )
            
   pInstantiate = 
      do tp <- pType   
         reservedOp ":="
         reserved "Instantiate"
         sigma <- parens pSigma
         return $ \info ->
            ( allTypeConstants tp ++ either toList allTypeConstants sigma
            , \varMap -> Instantiate (applyVarMap varMap tp) (makeSigma varMap sigma) info
            ) 

   -- explicit instance constraint = instantiate            
   pExplicit = 
      do tp <- pType   
         reservedOp "::"
         sigma <- pSigma
         return $ \info ->
            ( allTypeConstants tp ++ either toList allTypeConstants sigma
            , \varMap -> Instantiate (applyVarMap varMap tp) (makeSigma varMap sigma) info
            )
           
   pSkolemize = 
      do tp <- pType   
         reservedOp ":="
         reserved "Skolemize"
         (monos, sigma) <- parens $ 
                              do ms <- brackets (commas identifier)
                                 comma
                                 sigma <- pSigma
                                 return (map TCon ms, sigma)
         return $ \info ->
            ( allTypeConstants tp ++ allTypeConstants monos ++ either toList allTypeConstants sigma
            , \varMap -> Skolemize (applyVarMap varMap tp) (applyVarMap varMap monos, makeSigma varMap sigma) info
            ) 
       
   pProve = 
      do reserved "Prove"
         q <- parens pPredicate
         return $ \info ->
            ( allTypeConstants q
            , \varMap -> Prove (applyVarMap varMap q) info
            )
            
   pAssume = 
      do reserved "Assume"
         q <- parens pPredicate
         return $ \info ->
            ( allTypeConstants q
            , \varMap -> Assume (applyVarMap varMap q) info
            )
            
   pImplicit =
      do t1 <- pType
         reservedOp ":="
         reserved "Implicit"
         (monos, t2) <- parens pMonosType
         return $ \info ->
            ( allTypeConstants t1 ++ allTypeConstants monos ++ allTypeConstants t2
            , \varMap -> Implicit (applyVarMap varMap t1) (applyVarMap varMap monos, applyVarMap varMap t2) info
            )

---------------------------------------------------------------------
-- * Top operation parser 

pOperation :: Parser (Result (Constraint TopSolve))
pOperation = 
   let ops = [ --("Enter"           , enterGroup)
             --, ("Leave"           , do qsInfo <- doContextReduction; (_ :: TopQualifiers) <- removeAnnotation qsInfo ; leaveGroup)
               ("MakeConsistent"  , makeConsistent) 
             --, ("ContextReduction", do qsInfo <- doContextReduction; (_ :: TopQualifiers) <- removeAnnotation qsInfo; return ())
             -- , ("LogState"        , logState)
             -- , ("Stop"            , do logState; error "***** Stop reached *****")
             ]
       f (s, a) = do reserved s
                     return (S.empty, const (operation s a))
   in tryList (map f ops)   

---------------------------------------------------------------------
-- * Top subtyping rule parser 
  {-
pSubtypingRule :: Parser (Result (Constraint TopSolve))
pSubtypingRule =
   do reserved lexer "Declare"
      (xs, x) <- parens lexer (pContext pSubtyping pSubtyping)
      info    <- pInfo
      let rule   = SubtypingRule xs x
          vars   = filter (isLower . head) . nub . allTypeConstants $ rule
          varmap = zip vars [0..]
      return $ ([], \_ -> Constraint 
         (declareSubtypingRule (applyVarMap varmap rule) info, return True, "Declare "++show rule)) -} 
    
---------------------------------------------------------------------
-- * Top class/instance declaration parser 
{-
pClassDecl :: Parser (Result (Constraint TopSolve))
pClassDecl = 
   do reserved lexer "Class"
      tuple@(supers, className) <- pContext (identifier lexer) (identifier lexer)
      
      let f :: TIState info -> TIState info
          f s = s { classenv = g (classenv s) }
          g = M.insertWith (\(s1,is1) (s2,is2) -> (s1 `union` s2,is1 `union` is2)) className (supers, [])
      
      return ([], \_ -> operation ("Class "++show tuple) (deselect (modify f)))

pInstanceDecl :: Parser (Result (Constraint TopSolve))
pInstanceDecl =
   do reserved lexer "Instance"
      tuple@(ps, p@(Predicate className _)) <- pContext pPredicate pPredicate
      
      let vars   = filter (isLower . head) . nub . allTypeConstants $ (ps, p)
          varmap = zip vars [0..]
          tuple' = applyVarMap varmap (p, ps)
          
          f :: TIState info -> TIState info
          f s = s { classenv = g (classenv s) }
          g = M.insertWith (\(s1,is1) (s2,is2) -> (s1 `union` s2,is1 `union` is2)) className ([], [tuple'])
      
      return ([], \_ -> operation ("Instance "++show tuple) (deselect (modify f)))

pNeverDecl :: Parser (Result (Constraint TopSolve))
pNeverDecl = 
   do reserved lexer "Never"
      p    <- pPredicate
      info <- pInfo
      
      let vars   = filter (isLower . head) . nub . allTypeConstants $ p
          varmap = zip vars [0..]
          p'     = applyVarMap varmap p
      
      return ([], \_ -> operation ("Never " ++ show p ++ "   : {" ++ show info ++ "}") (addNeverDirective (p', info)))

pCloseDecl :: Parser (Result (Constraint TopSolve))
pCloseDecl = 
   do reserved lexer "Close"
      s    <- identifier lexer
      info <- pInfo
      
      return ([], \_ -> operation ("Close " ++ s ++ "   : {" ++ show info ++ "}") (addCloseDirective (s, info)))

pDisjointDecl :: Parser (Result (Constraint TopSolve))
pDisjointDecl = 
   do reserved lexer "Disjoint"
      ss    <- commas (identifier lexer)
      info <- pInfo
      
      return ([], \_ -> operation ("Disjoint " ++ show ss ++ "   : {" ++ show info ++ "}") (addDisjointDirective (ss, info)))

pDefaultDecl :: Parser (Result (Constraint TopSolve))
pDefaultDecl = 
   do reserved lexer "Default"
      className <- identifier lexer    
      typeList  <- 
         let single = pType >>= \tp -> return [tp]
             more   = parens lexer (commas pType)
         in tryList [more, single]
      info      <- pInfo
      return ([], \_ -> operation 
         ("Default " ++ className ++ " (" ++ concat (intersperse "," (map show typeList)) ++ ")   : {" ++ show info ++ "}")
         ( addDefaultDirective (className, (typeList, info)))) -}
                
---------------------------------------------------------------------
-- * Other parsers 
         
pInfo :: Parser TopInfo
pInfo = tryList [ withInfo, withoutInfo ]
   where
      withInfo =
         do reservedOp ":"
            s <- manyTill anyChar (do { Control.Monad.void (char '\n') ; return () } <|> eof)
            whiteSpace
            return (TopInfo [("msg", s)])
      withoutInfo =
         do reservedOp ";"
            whiteSpace
            return (TopInfo [("msg", "<no message>")])

pContext :: Parser a -> Parser b -> Parser ([a], b)
pContext p1 p2 = 
   do as <- tryList [ listContext, singletonContext, emptyContext]
      b  <- p2
      return (as, b)     
 where
   emptyContext = 
      return []
   singletonContext = 
      do a <- p1
         reservedOp "=>"  
         return [a]        
   listContext = 
      do as <- parens (commas p1)      
         reservedOp "=>"
         return as
         
pSigma :: Parser (Either String (Scheme TopQualifiers))
pSigma = try (do s <- pSigmaVar; return (Left s)) 
         <|> (do s <- pTypeScheme; return (Right s))

pSigmaVar :: Parser String
pSigmaVar = do s <- identifier
               case s of
                  's' : rest | all isDigit rest -> return s
                  _ -> fail ""

pTypeScheme :: Parser (Scheme TopQualifiers)
pTypeScheme = do qs <- option [] $
                          do reserved "forall"
                             xs <- many1 identifier
                             dot
                             return xs
                 (pss, tp) <- pContext pOneQualifier pType 
                 let sub = M.fromList (zip qs [10000..])
                 return (quantify (M.elems sub) (applyVarMap sub (concat pss) .=>. applyVarMap sub tp))

pQualifierList :: Parser TopQualifiers
pQualifierList = 
   tryList [ Control.Monad.liftM concat (parens (commas pOneQualifier))
           , pOneQualifier
           ]
 
pOneQualifier :: Parser TopQualifiers
pOneQualifier = tryList
   [ Control.Monad.liftM return pPredicate
   --, pDependency        >>= (return . toTopQual)
   --, pImplicitParameter >>= (return . toTopQual)
   --, pSubtyping         >>= (return . toTopQual)
   , parens pOneQualifier
   ]

pPredicate :: Parser Predicate
pPredicate = 
   do s  <- identifier
      tp <- pType2
      return (Predicate s tp)

{- pDependency :: Parser Dependency
pDependency = 
   do s <- identifier lexer
      symbol lexer "."
      t1 <- pType
      reservedOp lexer "~>"
      t2 <- pType
      return (Dependency s t1 t2) -}

{-pImplicitParameter :: Parser ImplicitParameter
pImplicitParameter = 
   do reservedOp lexer "?"
      s <- identifier lexer
      reservedOp lexer "::"
      tp <- pType
      return (ImplicitParameter s tp) -}

{- pSubtyping :: Parser Subtyping
pSubtyping = 
   do t1 <- pType
      reservedOp lexer "<:"
      t2 <- pType
      return (t1 :<: t2) -}

pType :: Parser Tp
pType = do left <- pType1
           option left $
             do reservedOp "->"
                right <- pType
                return (left .->. right)

pType1 :: Parser Tp
pType1 = do tps <- many1 pType2
            return (foldl1 TApp tps)
      
pType2 :: Parser Tp
pType2 = tryList [
          do s <- identifier
             return (TCon s)
        , do tps <- parens (commas pType)
             case tps of
                [tp] -> return tp
                _    -> return (tupleType tps)
        , do tp <- brackets pType
             return (listType tp)
    ]

pMonosType :: Parser ([Tp], Tp)
pMonosType = do 
   ms <- brackets (commas identifier)
   comma
   tp <- pType
   return (map TCon ms, tp)
    
---------------------------------------------------------------------
-- * Miscellaneous

type VarMap   = M.Map String Int
type Result a = (S.Set String, VarMap -> a)

applyVarMap :: HasTypes a => VarMap -> a -> a
applyVarMap varmap = 
   let f tp =
          case tp of
             TApp l r -> TApp (f l) (f r)
             TCon s   -> maybe (TCon s) TVar (M.lookup s varmap)
             TVar _   -> tp   
   in changeTypes f

commas :: Parser a -> Parser [a]
commas = (`sepBy` comma)

tryList :: [Parser a] -> Parser a 
tryList = foldr1 (<|>) . map try

toList :: a -> [a]
toList a = [a]

makeSigma :: VarMap -> Either String (Scheme TopQualifiers) -> Sigma TopQualifiers
makeSigma vm (Left s)  = let err = internalError "TopSolver.hs" "makeSigma" "sigma var not in variable map" 
                         in SigmaVar (fromMaybe err $ M.lookup s vm)
makeSigma vm (Right s) = SigmaScheme (applyVarMap vm s)