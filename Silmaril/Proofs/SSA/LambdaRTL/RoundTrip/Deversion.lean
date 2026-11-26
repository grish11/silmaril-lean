module

public import Silmaril.SSA.LambdaRTL.RoundTrip.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.RoundTrip

open Silmaril.SSA.LambdaRTL.RoundTrip

universe w

variable {V : Type w} [DecidableEq V] [Infinite V]

private theorem deversion_nonzero (support : Finset (V × ℕ)) {name : V × ℕ}
    (member : name ∈ support) (nonzero : name.2 ≠ 0) :
    deversion support name = (freshNames support (support.equivFin ⟨name, member⟩)).val := by
  simp [deversion, nonzero, member]

theorem deversion_injOn (support : Finset (V × ℕ)) : Set.InjOn (deversion support) support := by
  intro x hx y hy same
  have fresh {z : V × ℕ} (hz : z ∈ support) (nonzero : z.2 ≠ 0) :
      deversion support z ∉ support.image Prod.fst := by
    rw [deversion_nonzero support hz nonzero]
    exact (freshNames support _).property
  have base {z : V × ℕ} (hz : z ∈ support) (zero : z.2 = 0) :
      deversion support z ∈ support.image Prod.fst := by
    simpa [deversion, zero] using Finset.mem_image_of_mem Prod.fst hz
  by_cases xzero : x.2 = 0 <;> by_cases yzero : y.2 = 0
  · exact Prod.ext (by simpa [deversion, xzero, yzero] using same) (xzero.trans yzero.symm)
  · exact False.elim (fresh hy yzero (same ▸ base hx xzero))
  · exact False.elim (fresh hx xzero (same.symm ▸ base hy yzero))
  · rw [deversion_nonzero support hx xzero, deversion_nonzero support hy yzero] at same
    have indices := (freshNames support).injective (Subtype.ext same)
    exact congrArg Subtype.val (support.equivFin.injective (Fin.ext indices))

end Silmaril.Proofs.SSA.LambdaRTL.RoundTrip
