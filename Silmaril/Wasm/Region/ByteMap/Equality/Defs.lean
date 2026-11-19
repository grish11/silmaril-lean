module

public import Silmaril.Wasm.Instructions

/-! Total syntax comparison for the optional binary checker. Recursive child
sequences are compared structurally, without relying on an opaque partial
BEq derivation for this nested inductive. No execution/region assumption. -/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Equality

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

mutual
def equal : Instr → Instr → Bool
  | .nop, .nop => true
  | .unreachable, .unreachable => true
  | .drop, .drop => true
  | .select a0, .select b0 => decide (a0 = b0)
  | .block a0 a1, .block b0 b1 => decide (a0 = b0) && equalList a1 b1
  | .loop a0 a1, .loop b0 b1 => decide (a0 = b0) && equalList a1 b1
  | .if_ a0 a1 a2, .if_ b0 b1 b2 => decide (a0 = b0) && equalList a1 b1 && equalList a2 b2
  | .br a0, .br b0 => decide (a0 = b0)
  | .brIf a0, .brIf b0 => decide (a0 = b0)
  | .brTable a0 a1, .brTable b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .brOnNull a0, .brOnNull b0 => decide (a0 = b0)
  | .brOnNonNull a0, .brOnNonNull b0 => decide (a0 = b0)
  | .brOnCast a0 a1 a2, .brOnCast b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .brOnCastFail a0 a1 a2, .brOnCastFail b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .call a0, .call b0 => decide (a0 = b0)
  | .callRef a0, .callRef b0 => decide (a0 = b0)
  | .callIndirect a0 a1, .callIndirect b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .return_, .return_ => true
  | .returnCall a0, .returnCall b0 => decide (a0 = b0)
  | .returnCallRef a0, .returnCallRef b0 => decide (a0 = b0)
  | .returnCallIndirect a0 a1, .returnCallIndirect b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .throw a0, .throw b0 => decide (a0 = b0)
  | .throwRef, .throwRef => true
  | .tryTable a0 a1 a2, .tryTable b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && equalList a2 b2
  | .localGet a0, .localGet b0 => decide (a0 = b0)
  | .localSet a0, .localSet b0 => decide (a0 = b0)
  | .localTee a0, .localTee b0 => decide (a0 = b0)
  | .globalGet a0, .globalGet b0 => decide (a0 = b0)
  | .globalSet a0, .globalSet b0 => decide (a0 = b0)
  | .tableGet a0, .tableGet b0 => decide (a0 = b0)
  | .tableSet a0, .tableSet b0 => decide (a0 = b0)
  | .tableSize a0, .tableSize b0 => decide (a0 = b0)
  | .tableGrow a0, .tableGrow b0 => decide (a0 = b0)
  | .tableFill a0, .tableFill b0 => decide (a0 = b0)
  | .tableCopy a0 a1, .tableCopy b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .tableInit a0 a1, .tableInit b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .elemDrop a0, .elemDrop b0 => decide (a0 = b0)
  | .intLoad a0 a1 a2 a3, .intLoad b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && decide (a3 = b3)
  | .floatLoad a0 a1 a2, .floatLoad b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .intStore a0 a1 a2 a3, .intStore b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && decide (a3 = b3)
  | .floatStore a0 a1 a2, .floatStore b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecLoad a0 a1 a2, .vecLoad b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecLoadLane a0 a1 a2 a3, .vecLoadLane b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && decide (a3 = b3)
  | .vecStore a0 a1, .vecStore b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecStoreLane a0 a1 a2 a3, .vecStoreLane b0 b1 b2 b3 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) && decide (a3 = b3)
  | .memorySize a0, .memorySize b0 => decide (a0 = b0)
  | .memoryGrow a0, .memoryGrow b0 => decide (a0 = b0)
  | .memoryFill a0, .memoryFill b0 => decide (a0 = b0)
  | .memoryCopy a0 a1, .memoryCopy b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .memoryInit a0 a1, .memoryInit b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .dataDrop a0, .dataDrop b0 => decide (a0 = b0)
  | .refNull a0, .refNull b0 => decide (a0 = b0)
  | .refIsNull, .refIsNull => true
  | .refAsNonNull, .refAsNonNull => true
  | .refEq, .refEq => true
  | .refTest a0, .refTest b0 => decide (a0 = b0)
  | .refCast a0, .refCast b0 => decide (a0 = b0)
  | .refFunc a0, .refFunc b0 => decide (a0 = b0)
  | .refI31, .refI31 => true
  | .i31Get a0, .i31Get b0 => decide (a0 = b0)
  | .structNew a0, .structNew b0 => decide (a0 = b0)
  | .structNewDefault a0, .structNewDefault b0 => decide (a0 = b0)
  | .structGet a0 a1 a2, .structGet b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .structSet a0 a1, .structSet b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayNew a0, .arrayNew b0 => decide (a0 = b0)
  | .arrayNewDefault a0, .arrayNewDefault b0 => decide (a0 = b0)
  | .arrayNewFixed a0 a1, .arrayNewFixed b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayNewData a0 a1, .arrayNewData b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayNewElem a0 a1, .arrayNewElem b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayGet a0 a1, .arrayGet b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arraySet a0, .arraySet b0 => decide (a0 = b0)
  | .arrayLen, .arrayLen => true
  | .arrayFill a0, .arrayFill b0 => decide (a0 = b0)
  | .arrayCopy a0 a1, .arrayCopy b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayInitData a0 a1, .arrayInitData b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .arrayInitElem a0 a1, .arrayInitElem b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .externConvertAny, .externConvertAny => true
  | .anyConvertExtern, .anyConvertExtern => true
  | .intConst a0 a1, .intConst b0 b1 => decide (a0 = b0) && (if h : a0 = b0 then decide (h ▸ a1 = b1) else false)
  | .floatConst a0 a1, .floatConst b0 b1 => decide (a0 = b0) && (if h : a0 = b0 then decide (h ▸ a1 = b1) else false)
  | .intUnOp a0 a1, .intUnOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .intBinOp a0 a1, .intBinOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .intTestOp a0 a1, .intTestOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .intRelOp a0 a1, .intRelOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .floatUnOp a0 a1, .floatUnOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .floatBinOp a0 a1, .floatBinOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .floatRelOp a0 a1, .floatRelOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .convert a0, .convert b0 => decide (a0 = b0)
  | .vecConst a0, .vecConst b0 => decide (a0 = b0)
  | .vecUnOp a0, .vecUnOp b0 => decide (a0 = b0)
  | .vecBinOp a0, .vecBinOp b0 => decide (a0 = b0)
  | .vecTernOp a0, .vecTernOp b0 => decide (a0 = b0)
  | .vecTestOp a0, .vecTestOp b0 => decide (a0 = b0)
  | .vecIntUnOp a0 a1, .vecIntUnOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecFloatUnOp a0 a1, .vecFloatUnOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecIntBinOp a0 a1, .vecIntBinOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecFloatBinOp a0 a1, .vecFloatBinOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecIntTernOp a0 a1, .vecIntTernOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecFloatTernOp a0 a1, .vecFloatTernOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecAllTrue a0, .vecAllTrue b0 => decide (a0 = b0)
  | .vecIntRelOp a0 a1, .vecIntRelOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecFloatRelOp a0 a1, .vecFloatRelOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecShiftOp a0 a1, .vecShiftOp b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | .vecBitmask a0, .vecBitmask b0 => decide (a0 = b0)
  | .vecSwizzle a0, .vecSwizzle b0 => decide (a0 = b0)
  | .vecShuffle a0, .vecShuffle b0 => decide (a0 = b0)
  | .vecExtUnOp a0 a1 a2, .vecExtUnOp b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecExtBinOp a0 a1 a2, .vecExtBinOp b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecExtTernOp a0 a1 a2, .vecExtTernOp b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecNarrow a0 a1 a2, .vecNarrow b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecConvert a0 a1 a2, .vecConvert b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecSplat a0, .vecSplat b0 => decide (a0 = b0)
  | .vecExtractLane a0 a1 a2, .vecExtractLane b0 b1 b2 => decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2)
  | .vecReplaceLane a0 a1, .vecReplaceLane b0 b1 => decide (a0 = b0) && decide (a1 = b1)
  | _, _ => false
termination_by structural a => a

def equalList : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => equal a b && equalList as bs
  | _, _ => false
termination_by structural as => as
end

end Silmaril.Wasm.Region.ByteMap.Equality
