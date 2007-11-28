module Simple where

-- No need to import Prelude

import Char
import List
import Base

type Strand = String
type DStrand = (Strand, Strand)
type WSMData = (Strand, Strand, Bool, Int, Int)
type WSM = Maybe WSMData
type Axiom = DStrand
type StickerSystem = ([Axiom], [Strand], [Strand])

dStrandToWSM :: DStrand -> WSM
dStrandToWSM (u,l) = convert u l [] where
     convert u [] r = Just (reverse r, u, True, 0, 0)
     convert [] l r = Just (reverse r, l, False, 0, 0)
     convert (a:u) (b:l) r = if (eqChar a b) then convert u l (a:r) else Nothing

axioms::StickerSystem -> [Axiom]
axioms = fst3

upperStrands::StickerSystem -> [Strand]
upperStrands = snd3

lowerStrands::StickerSystem -> [Strand]
lowerStrands = thd3

getStrand :: WSM -> Strand
getStrand Nothing = error "Should not occur"
getStrand (Just a) = fst5 a

example1 = ("ab","a")
example2 = ("aaaab","aaab")
exampleSS1 = ([example1,example2, ("","")],["a","b"],["aa","bb"])

fullSticker :: WSM -> Bool
fullSticker Nothing = error "Should not occur"
fullSticker (Just a) = null (snd5 a)
fairSticker :: WSM -> Bool
fairSticker Nothing = error "Should not occur"
fairSticker (Just a) = frth5 a == ffth5 a

wrongWSM :: WSM -> Bool
wrongWSM Nothing = True
wrongWSM _ = False

okayWSM = not . wrongWSM

glueIt :: Strand -> Strand -> WSM
glueIt = curry dStrandToWSM

combine :: Int -> Int -> Strand -> WSM -> WSM
combine u l soFar (Just (added,remains,bool,_,_)) = Just (soFar++added,remains,bool,u,l)
combine _ _ _ Nothing = Nothing

glue :: [Strand] -> [Strand] -> WSM -> [WSM]
glue _ _ Nothing = error "Should not occur"
glue _ ls (Just (a,b,True,u,l)) = map (combine (u+1) l a) (filter okayWSM (map (glueIt b) ls))
glue us _ (Just (a,b,False,u,l)) = map (combine u (l+1) a) (filter okayWSM (map ((flip glueIt) b) us))

genNext :: [Strand] -> [Strand] -> ([WSM] -> [WSM])
genNext us ls = concat . (map (glue us ls))

genProcess :: Bool -> Bool -> [Strand] -> [Strand] -> [WSM] -> [Strand]
genProcess isFair isPrimitive us ls sts = 
        let
          fullSts = filter fullSticker sts
          fullAndFair = if isFair then filter fairSticker fullSts else fullSts
          nextSts = if isPrimitive then filter (not . fullSticker) sts else sts
        in
          (map getStrand fullAndFair) ++ genProcess isFair isPrimitive us ls (genNext us ls nextSts)
 
-- Starts the actual process after computing the internal format for axioms and doing some sanity checks.
-- For example, in an axiom either the upper is prefix of the lower or vice versa.
stickerGame :: Bool -> Bool -> [Axiom] -> [Strand] -> [Strand] -> [Strand]
stickerGame isFair isPrimitive axs us ls = 
        let
          tfmdAxioms = map dStrandToWSM axs            
        in
          if (any null us) || (any null ls) || (any wrongWSM tfmdAxioms) then
            error "Error in axioms or upper/lower strand found"   
          else
            nubBy eqString (genProcess isFair isPrimitive us ls tfmdAxioms)

playWithStickers :: Bool -> Bool -> StickerSystem -> [Strand]
playWithStickers isFair isPrimitive (a,b,c) = stickerGame isFair isPrimitive a b c

sl :: StickerSystem -> [Strand]
sl = playWithStickers False False

slf :: StickerSystem -> [Strand]
slf = playWithStickers True False

slp :: StickerSystem -> [Strand]
slp = playWithStickers False True

slpf :: StickerSystem -> [Strand]
slpf = playWithStickers True True

slfp = slpf

exampleSS2 = ([("","aaa"),("a","aaaa"),("aa","aaaaa"),("aaa","aaaaaa")],
              ["aaaa", "b", "cc", "cba", "baa", "cbaaa"],
              ["aaaa", "abc", "cc", "cb", "ba", "cbaa", "baaa", "abb", "aa"])
simple = ([("","")],["a","2","a2"],["a","2","a2"])
simplefair = ([("","")],["aaab","aa"],["aa","ab"])
-- slf simplefair soon gives garbage collection problems.

hasa = elemBy eqChar 'a'
hasnob = not . (elemBy eqChar 'b')

main = take 8 (filter (all isAlpha) (sl simple))

