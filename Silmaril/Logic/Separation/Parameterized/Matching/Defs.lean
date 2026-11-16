module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Thms
public import Silmaril.Logic.Matching.GuardedLFP.Sentences

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized.Matching
open Silmaril.Logic.Institution.Examples

abbrev model {A : Signature} (M : Model A) :=
  Silmaril.Logic.Matching.GuardedLFP.expand (FirstOrder.model M).toStructure

/-- The native guarded matching compiler reuses the proved n-ary FO(LFP)
translation; the independent source interpretation contains neither compiler. -/
abbrev compile {A : Signature} {k l} {P : Fin 0 → Nat} {Γ : Fin l → FirstOrder.TargetSort}
    (p : Pattern A P k) (σ : Fin k → FirstOrder.TargetTerm A Γ .value)
    (h : FirstOrder.TargetTerm A Γ .heap) :=
  Silmaril.Logic.Matching.GuardedLFP.formula (FirstOrder.pattern p σ h)

/-- Exact native matching adequacy at all active object assignments and all
truth elements of the canonical padded model. Arbitrary source heaps and empty
value carriers are supported. Unrestricted raw matching models are not claimed. -/
theorem compile_correct {A : Signature} (M : Model A) {k l} {P : Fin 0 → Nat}
    {Γ : Fin l → FirstOrder.TargetSort} (p : Pattern A P k)
    (σ : Fin k → FirstOrder.TargetTerm A Γ .value) (h : FirstOrder.TargetTerm A Γ .heap)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (FirstOrder.model M) Γ)
    (w : (model M).base.carrier (.base .truth)) :
    w ∈ (compile p σ h).denote (model M).base (fun i => some (θ i)) (fun i => i.elim0) ↔
      ((fun i => (σ i).eval (FirstOrder.model M).toStructure.toAlgebra θ),
        h.eval (FirstOrder.model M).toStructure.toAlgebra θ) ∈ p.denote M (fun i => i.elim0) := by
  have he : FirstOrder.encodeRelEnv M (P := P) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  have hc := Silmaril.Logic.Matching.GuardedLFP.expanded_formula_denote (FirstOrder.model M)
    (FirstOrder.pattern p σ h) θ w
  rw [← he] at hc
  exact hc.trans (FirstOrder.pattern_correct M p (fun i => i.elim0) σ h θ)

end Silmaril.Logic.Separation.Parameterized.Matching
