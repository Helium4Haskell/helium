{-| Module      :  BindingGroupAnalysis
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Binding groups (mutually recursive function definitions)
-}

-- To do: clean up this module. Also see BGA for kind inferencing

module BindingGroupAnalysis where

import UHA_Syntax
import TypeConstraints
import ConstraintInfo
import TopSort (topSort)
import Top.Types
import Top.ComposedSolvers.Tree
import Data.FiniteMap
import Data.List

type Assumptions        = FiniteMap Name [(Name,Tp)]
type PatternAssumptions = FiniteMap Name Tp
type Monos              = Tps

noAssumptions :: FiniteMap Name a
noAssumptions = emptyFM

listToAssumptions :: [(Name, Tp)] -> Assumptions
listToAssumptions list =
   foldr combine noAssumptions [ listToFM [(n, [tuple])] | tuple@(n, _) <- list ]

combine :: Assumptions -> Assumptions -> Assumptions
combine = plusFM_C (++)

single :: Name -> Tp -> Assumptions
single n t = unitFM n [(n,t)]

type BindingGroups = [BindingGroup]
type BindingGroup  = (PatternAssumptions, Assumptions, ConstraintSets)
type InheritedBDG  = [(Names, (Monos, Int))]

emptyBindingGroup :: BindingGroup
emptyBindingGroup = 
   (noAssumptions, noAssumptions, [])

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1) (e2,a2,c2) = 
   (e1 `plusFM` e2, a1 `combine` a2, c1++c2)

concatBindingGroups :: BindingGroups -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup

-- |Input for binding group analysis
type InputBDG     = (Bool, Int, Int, Monos, FiniteMap Name TpScheme, Maybe (Assumptions, ConstraintSets), Int)
type OutputBDG    = (Assumptions, ConstraintSet, InheritedBDG, Int, Int, FiniteMap Name (Sigma Predicates))

performBindingGroup :: InputBDG -> BindingGroups -> OutputBDG
performBindingGroup (topLevel, currentChunk, uniqueChunk, monos, typeSignatures, chunkContext, unique) groups = 
   variableDependencies 

   where   
        bindingGroupAnalysis :: BindingGroups -> BindingGroups
        bindingGroupAnalysis cs =
           let explicits = keysFM typeSignatures
               indexMap = concat (zipWith f cs [0..])
               f (env,_,_) i = [ (n,i) | n <- keysFM env, n `notElem` explicits ]
               edges    = concat (zipWith f' cs [0..])
               f' (_,ass,_) i = [ (i,j)| n <- keysFM ass, (n',j) <- indexMap, n==n' ]
               list = topSort (length cs-1) edges
           in map (concatBindingGroups . map (cs !!)) list

        chunkedBindingGroups  :: [(Int, BindingGroup)]
        chunkedBindingGroups = 
           zip [uniqueChunk..] (bindingGroupAnalysis groups) ++ 
           case chunkContext of 
              Nothing     -> []
              Just (a, c) -> [(currentChunk, (emptyFM, a, c))]
        
        monomorphicNames :: [Name]
        monomorphicNames = 
           let initial = let f (e, a, _) = if any (`elem` ftv monos) (ftv $ map snd $ concat $ eltsFM a)
                                             then keysFM e
                                             else []
                         in concatMap f groups
               expand [] _       = []
               expand (n:ns) gps = let (xs, ys)  = partition p gps
                                       p (_,a,_) = n `elem` keysFM a
                                       f (e,_,_) = keysFM e
                                   in n : expand (concatMap f xs ++ ns) ys
           in expand initial groups
                          
        variableDependencies :: OutputBDG
        variableDependencies = 
           let (aset, cset, mt, newUnique, fm) = foldr op initial chunkedBindingGroups
           in (aset, cset, mt, uniqueChunk + length groups, newUnique, fm)

          where        
            initial = (noAssumptions, emptyTree, [], unique, emptyFM)
          
            op (cnr, (e, a, c)) (aset, cset, mt, un, fm) =
               let (cset1,e'   )  = (typeSignatures !:::! e) monos cinfoBindingGroupExplicitTypedBinding                
                   (cset2,a'   )  = (typeSignatures .:::. a) (cinfoBindingGroupExplicit monos (keysFM e))
                   (cset3,a''  )  = (e' .===. a')            cinfoSameBindingGroup
                   
                   implicits      = zip [un..] (fmToList e')
                   implicitsFM    = listToFM [ (name, SigmaVar sv) | (sv, (name, _)) <- implicits ]
                   cset4          = genConstraints monos cinfoGeneralize implicits                   
                   (cset5, aset') = (implicitsFM .<==. aset) cinfoBindingGroupImplicit
                                    
                   monomorphic    = not topLevel -- simplification: was 
                                                 -- any (`elem` monomorphicNames) (keysFM e) || cnr == currentChunk

                   constraintTree =
                      StrictOrder 
                         ( (if monomorphic then id else Chunk cnr)
                         $ StrictOrder
                              ( (cset1 ++ cset2 ++ cset3) .>>. Node (reverse c) )
                              (listTree cset4))
                         (cset5 .>>. cset)
               in
                  ( a'' `combine` aset'
                  , constraintTree
                  , (keysFM e, (eltsFM e', if monomorphic then currentChunk else cnr)) : mt
                  , un + sizeFM e'
                  , implicitsFM `plusFM` fm
                  ) 

findMono :: Name -> InheritedBDG -> Monos
findMono n = let p = elem n . fst
             in fst . snd . head . filter p                  

getMonos :: TypeConstraints info -> Monos
getMonos tcs = [ TVar i | tc <- tcs, i <- ftv tc ]

findCurrentChunk :: Name -> InheritedBDG -> Int
findCurrentChunk n = let p = elem n . fst
                     in snd . snd . head . filter p