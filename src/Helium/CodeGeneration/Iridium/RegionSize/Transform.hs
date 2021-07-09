module Helium.CodeGeneration.Iridium.RegionSize.Transform
    (transform, collectEffects, remEmptyRegs,
    collectRegs, collectEmptyRegs, collectBoundedRegs, collectUnboundedRegs)
where

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Annotation

import Data.Maybe (fromMaybe)

----------------------------------------------------------------
-- Retrieve all effect sets from the annotation
----------------------------------------------------------------

-- | Collect all constraint sets from an annotation
collectEffects :: Annotation -> Constr
collectEffects = foldAnnAlg collectAlg
    where collectAlg = AnnAlg {
        aVar    = \_ _   -> constrBot,
        aReg    = \_ _   -> constrBot,
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> constrAdd a b,
        aConstr = \_ c   -> c,
        aUnit   = \_     -> constrBot,
        aTuple  = \_ as  -> foldr constrAdd constrBot as,
        aProj   = \_ _ a -> a,
        aAdd    = \_ a b -> constrAdd a b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> constrAdd a b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \_ _ c -> c,
        aBot    = \_ _   -> constrBot,
        aFix    = \_ _ a -> foldr constrAdd constrBot a
    }

----------------------------------------------------------------
-- Fill in region sizes
----------------------------------------------------------------

transform :: Constr -> Method -> Method
transform bounds (Method a b c d e f fstBlock otherBlocks) =
    let fstBlock'    = transformBlock bounds     fstBlock
        otherBlocks' = transformBlock bounds <$> otherBlocks
    in (Method a b c d e f fstBlock' otherBlocks')

transformBlock :: Constr -> Block -> Block
transformBlock bounds (Block a instr) =
    let instr' = transformInstr bounds instr
    in (Block a instr')

transformInstr :: Constr -> Instruction -> Instruction
transformInstr bounds instr = 
    case instr of
        NewRegion reg _ next -> let bound = lookupBound reg bounds
                                in NewRegion reg bound $ transformInstr bounds next
        Let         a b next -> Let         a b $ transformInstr bounds next
        LetAlloc      a next -> LetAlloc      a $ transformInstr bounds next
        Match   a b c d next -> Match   a b c d $ transformInstr bounds next
        ReleaseRegion a next -> ReleaseRegion a $ transformInstr bounds next
        terminalInstr -> terminalInstr -- Other terminal nodes 

-- Lookup a bound in a constraint set and convert it to a maybe int
lookupBound :: RegionVar -> Constr -> Maybe Int
lookupBound r c = case constrIdx (Region r) c of
                    Nat n -> Just n
                    Infty -> Nothing

----------------------------------------------------------------
-- Collect regions
----------------------------------------------------------------

collectEmptyRegs :: Method -> [RegionVar]
collectEmptyRegs method = fst <$> (filter (\(_,b) -> b == Just 0) $ collectRegs method)

collectBoundedRegs :: Method -> [RegionVar]
collectBoundedRegs method = fst <$> (filter (\(_,b) -> 0 < fromMaybe 0 b) $ collectRegs method)

collectUnboundedRegs :: Method -> [RegionVar]
collectUnboundedRegs method = fst <$> (filter (\(_,b) -> b == Nothing) $ collectRegs method)

collectRegs :: Method -> [(RegionVar, Maybe Int)]
collectRegs (Method _ _ _ _ _ _ fstBlock otherBlocks) =
    concat $ collectRegsBlock <$> fstBlock:otherBlocks

collectRegsBlock :: Block -> [(RegionVar, Maybe Int)]
collectRegsBlock (Block _ instr) =
    collectRegsInstr instr

collectRegsInstr :: Instruction -> [(RegionVar, Maybe Int)]
collectRegsInstr instr = 
    case instr of
        NewRegion reg bound next -> (reg,bound) : collectRegsInstr next
        Let         _ _ next -> collectRegsInstr next
        LetAlloc      _ next -> collectRegsInstr next
        Match   _ _ _ _ next -> collectRegsInstr next
        ReleaseRegion _ next -> collectRegsInstr next
        _                    -> []

----------------------------------------------------------------
-- Remove 0-size regions
----------------------------------------------------------------

remEmptyRegs :: [RegionVar] -> Method -> Method
remEmptyRegs emptyRegs (Method a b c d e f fstBlock otherBlocks) =
    let fstBlock'    = remEmptyRegsBlock emptyRegs     fstBlock
        otherBlocks' = remEmptyRegsBlock emptyRegs <$> otherBlocks
    in (Method a b c d e f fstBlock' otherBlocks')

remEmptyRegsBlock :: [RegionVar] -> Block -> Block
remEmptyRegsBlock emptyRegs (Block a instr) =
    let instr' = remEmptyRegsInstr emptyRegs instr
    in (Block a instr')

remEmptyRegsInstr :: [RegionVar] -> Instruction -> Instruction
remEmptyRegsInstr emptyRegs instr = 
    case instr of
        NewRegion   reg b next -> if reg `elem` emptyRegs
                                  then remEmptyRegsInstr emptyRegs next
                                  else NewRegion   reg b $ remEmptyRegsInstr emptyRegs next
        ReleaseRegion reg next -> if reg `elem` emptyRegs
                                  then remEmptyRegsInstr emptyRegs next
                                  else ReleaseRegion reg $ remEmptyRegsInstr emptyRegs next
        Let           a b next -> Let         a b $ remEmptyRegsInstr emptyRegs next
        LetAlloc        a next -> LetAlloc      a $ remEmptyRegsInstr emptyRegs next
        Match     a b c d next -> Match   a b c d $ remEmptyRegsInstr emptyRegs next
        terminalInstr -> terminalInstr
