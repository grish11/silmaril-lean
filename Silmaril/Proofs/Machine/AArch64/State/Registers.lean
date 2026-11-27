module

public import Silmaril.Machine.AArch64.State.Defs

/-!
# AArch64 register state: proofs

Proofs for `Silmaril.Machine.AArch64.State.Thms` that are longer than a few lines.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.State

open Silmaril.Machine Silmaril.Machine.AArch64

/-- A write to one register leaves every other register as it was, at any widths. -/
theorem readX_writeX_other (s : AArch64.State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeX w n v).readX w' m = s.readX w' m := by
  unfold AArch64.State.readX AArch64.State.writeX
  by_cases hn : n = 31#5
  · simp [hn]
  · have hidx (hm : m ≠ 31#5) : m.index hm ≠ n.index hn := by
      simp [Reg.index, Fin.ext_iff, BitVec.toNat_inj, h]
    by_cases hm : m = 31#5
    · simp [hm]
    · simp [hn, hm, hidx hm]

/-- A write through `writeXSP` leaves every other register number's `readXSP` unchanged. -/
theorem readXSP_writeXSP_other (s : AArch64.State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeXSP w n v).readXSP w' m = s.readXSP w' m := by
  unfold AArch64.State.readXSP AArch64.State.writeXSP
  by_cases hn : n = 31#5
  · have hm : m ≠ 31#5 := hn ▸ h
    simp only [hn, hm, ite_true, ite_false]
    rfl
  · by_cases hm : m = 31#5
    · simp only [hn, hm, ite_true, ite_false]
      unfold AArch64.State.readSP
      congr 1
      unfold AArch64.State.writeX; split <;> rfl
    · simp only [hn, hm, ite_false]
      exact readX_writeX_other s h w w' v

/-- The top 32 bits of a 32-bit value zero-extended to 64 bits are zero. -/
theorem setWidth_64_high (v : BitVec 32) : (v.setWidth 64).extractLsb' 32 32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

end Silmaril.Proofs.Machine.AArch64.State
