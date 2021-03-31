module Helium.CodeGeneration.Iridium.RegionSize.Transform
    (transform)
where

import Helium.CodeGeneration.Iridium.Data

import Helium.CodeGeneration.Iridium.RegionSize.Constraints

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
        instr -> instr -- Other terminal nodes 

lookupBound :: RegionVar -> Constr -> Maybe Int
lookupBound r c = case constrIdx (Region r) c of
                    Nat n -> Just n
                    Infty -> Nothing