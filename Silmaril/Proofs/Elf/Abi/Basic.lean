module

public import Silmaril.Elf.Abi.Defs
import Silmaril.Elf.Index.Thms

/-! # ABI conformance of an ELF function: generic proofs -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi

open Silmaril.Elf
open Silmaril.X86.Link (Blob)

/-- A file maps at most one byte list of each length at an address. -/
theorem codeAt_unique {F : Blob} {v : Nat} {xs ys : List (BitVec 8)} (hx : CodeAt F v xs)
    (hy : CodeAt F v ys) (hl : xs.length = ys.length) : xs = ys := by
  obtain ⟨A, hA, ph, hf, hr⟩ := hx
  obtain ⟨B, hB, ph', hf', hr'⟩ := hy
  have : A = B := Option.some.inj (hA.symm.trans hB)
  subst this
  rw [← hl, hf] at hf'
  cases hf'
  rw [← hl, hr] at hr'
  exact Silmaril.Elf.valueLE_inj hl (Option.some.inj hr')

end Silmaril.Proofs.Elf.Abi

end
