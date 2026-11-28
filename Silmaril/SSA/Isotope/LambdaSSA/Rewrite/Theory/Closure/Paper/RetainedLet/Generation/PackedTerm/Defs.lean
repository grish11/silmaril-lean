module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Defs

/-! # The term counterpart of a packed singleton body -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody

open Silmaril.Isotope.LambdaSSA

universe v

/-- Open the packed input with the same constructor pair as `applyPacked`. -/
def applyPackedTerm {Φ : Type v} (t : Tm Φ) : Tm Φ :=
  t.subst (Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody
