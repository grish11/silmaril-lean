module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRestrictionCheck

/-! # Exact no-target certificate from a successful traversal -/

public section

universe u

namespace Silmaril.Isotope.LambdaSSA.Region

theorem checkFamily_some {α : Type u} {n : Nat} {f : Fin n → Option α} {g : Fin n → α}
    (h : checkFamily n f = some g) (i : Fin n) : f i = some (g i) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRestrictionCheck.family h i

/-- Every written transfer is in the smaller interface. Reembedding the
readback recovers the entire original syntax, including nested CFGs. -/
theorem restrictLabels?_sound {Φ : Type u} {r s : Region Φ} {bound : Nat} {ρ : Nat → Nat}
    (ok : r.restrictLabels? bound ρ = some s) :
    s.LabelsBound bound ∧ s.renameLabels ρ = r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRestrictionCheck.readback r ok

end Silmaril.Isotope.LambdaSSA.Region
