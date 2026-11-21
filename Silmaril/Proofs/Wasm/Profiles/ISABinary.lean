module

public import Silmaril.Wasm.Profiles.ISA.Defs
public import Silmaril.Wasm.Binary.Core.Decode

public section

namespace Silmaril.Proofs.Wasm.Profiles.ISA

open Silmaril.Wasm Silmaril.Wasm.Profiles.ISA

private theorem subopcode0 : Tools.Meta.encU32 (UInt32.toNat 0) = [0] := by decide +kernel
private theorem subopcode1 : Tools.Meta.encU32 (UInt32.toNat 1) = [1] := by decide +kernel
private theorem subopcode28 : Tools.Meta.encU32 (UInt32.toNat 28) = [28] := by decide +kernel

theorem encodes (tag : Flat) : Binary.Core.Instr .all tag.opcode.bytes tag.erase := by
  cases tag with
  | add32 => exact .plain .rx6A
  | add64 => exact .plain .rx7C
  | divS32 => exact .plain .rx6D
  | divU32 => exact .plain .rx6E
  | divS64 => exact .plain .rx7F
  | divU64 => exact .plain .rx80
  | extend32S64 => exact .plain .rxC4
  | truncSatS32F32 =>
    apply Binary.Core.Instr.prefixFC .r0
    rw [subopcode0]
    exact Binary.UN.byte (N := 32) 0 (by decide) (by decide)
  | truncSatU32F32 =>
    apply Binary.Core.Instr.prefixFC .r1
    rw [subopcode1]
    exact Binary.UN.byte (N := 32) 1 (by decide) (by decide)
  | refI31 =>
    apply Binary.Core.Instr.prefixFB .r28
    rw [subopcode28]
    exact Binary.UN.byte (N := 32) 28 (by decide) (by decide)

open Binary.Core.Decode in
theorem readOne_bytes (tag : Flat) :
    let bytes := tag.opcode.bytes.toByteArray
    (do let head ← readByte; readInstr 1 head.toNat : DecodeM Instr).run ⟨bytes, 0⟩ =
      .ok (tag.erase, ⟨bytes, bytes.size⟩) := by
  cases tag <;> try rfl
  all_goals
    simp only [Flat.opcode, Opcode.bytes, Prefix.byte, subopcode0, subopcode1, subopcode28]
    rfl

end Silmaril.Proofs.Wasm.Profiles.ISA
