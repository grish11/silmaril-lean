module

public import Silmaril.WasmSpec.Abs.Defs
public import Silmaril.WasmSpec.Common.Thms
import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `Abs` v1, mode `tactic`

`spec_of_vc`: symbolic execution reduces `Spec` to the bit-vector identity
`VC` (`(x ^^^ x >>>ₛ 31) - x >>>ₛ 31 = absBV x`). `vc_tactic` proves it by
hand: case on the sign bit, where the arithmetic shift is `0` or all ones
(`sshiftRight_eq_of_msb_false/true`, `shr31`). `spec_tactic` combines them.
Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Abs

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core
  Silmaril.WasmSpec.Ops

/-- The verification condition: the computed value is the specified one. -/
def VC : Prop := ∀ x : BitVec 32, (x ^^^ x.sshiftRight 31) - x.sshiftRight 31 = absBV x

/-- The quoted body. -/
theorem absFunc_body : absFunc.body =
    [.localGet ⟨0⟩, .intConst .i32 31, .intBinOp .i32 (.shr .signed), .localSet ⟨1⟩,
      .localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .xor, .localGet ⟨1⟩, .intBinOp .i32 .sub] :=
  rfl

/-- One declared local, the sign mask. -/
theorem absFunc_locals : absFunc.locals = [.i32] := rfl

/-- **Reduction**: symbolic execution leaves exactly `VC`. -/
theorem spec_of_vc (h : VC) : Spec := by
  intro x H P host s m
  rw [absFunc_body, absFunc_locals]
  simp only [Frame.forCall, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one, shrS32, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  simp only [funcPost]
  exact ⟨rfl, trivial, by rw [h x]⟩

/-- A non-negative `i32` shifted right by `31` is `0`. -/
theorem shr31 {x : BitVec 32} (h : x.msb = false) : x >>> 31 = 0#32 := by
  have hx : 2 * x.toNat < 2 ^ 32 := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  omega

/-- `VC` by hand, on the sign bit. -/
theorem vc_tactic : VC := by
  intro x
  rw [absBV, BitVec.slt_zero_eq_msb]
  cases h : x.msb
  · rw [BitVec.sshiftRight_eq_of_msb_false h, shr31 h]
    simp
  · have hn : (~~~x).msb = false := by simp [BitVec.msb_not, h]
    rw [BitVec.sshiftRight_eq_of_msb_true h, shr31 hn, BitVec.not_zero, BitVec.xor_allOnes,
      ← BitVec.neg_one_eq_allOnes, BitVec.sub_eq_add_neg, BitVec.neg_neg, BitVec.neg_eq_not_add]
    rfl

/-- Mode `tactic`. -/
theorem spec_tactic : Spec := spec_of_vc vc_tactic

end Silmaril.WasmSpec.Abs
