module

public import Silmaril.Wasm.Profiles.ISA.Thms
public import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Proofs.Wasm.Profiles.ISABinary

@[expose] public section

namespace Silmaril.Wasm.Profiles.ISA

open Binary.Core.Decode

/-- Use the real reader, starting before the primary opcode. Covered
instructions have no nested bodies, so one unit of fuel suffices. -/
def readOne : DecodeM Instr := do
  let head ← readByte
  readInstr 1 head.toNat

theorem Flat.readOne_bytes (tag : Flat) :
    let bytes := tag.opcode.bytes.toByteArray
    readOne.run ⟨bytes, 0⟩ = .ok (tag.erase, ⟨bytes, bytes.size⟩) := Proofs.Wasm.Profiles.ISA.readOne_bytes tag

theorem Flat.encodes (tag : Flat) : Binary.Core.Instr .all tag.opcode.bytes tag.erase :=
  Proofs.Wasm.Profiles.ISA.encodes tag

end Silmaril.Wasm.Profiles.ISA
