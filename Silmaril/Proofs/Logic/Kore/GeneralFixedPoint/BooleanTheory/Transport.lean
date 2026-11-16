module

public import Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
open Predicates

/-- Whole-family satisfaction transport uses all native result sorts. The
reverse direction uses inhabitation only to extract the uniform truth value. -/
theorem Sentence.lower_satisfies {scope} (p : Sentence scope)
    (M : Matching.GeneralFixedPoint.Model scope.signature) :
    p.Satisfies M ↔ ∀ q ∈ p.lower,
      Matching.GeneralFixedPoint.Sentence.Satisfies (expand M) q := by
  cases p with
  | value objects sort p =>
      constructor
      · intro h q hq
        obtain rfl := Set.mem_singleton_iff.mp hq
        intro v η x
        have he : η = (fun i => i.elim0) := funext fun i => i.elim0
        subst η
        exact (Set.ext_iff.mp (p.denote_lower M v) x).mpr (h v x)
      · intro h v x
        have hh := h _ (Set.mem_singleton _)
        exact (Set.ext_iff.mp (p.denote_lower M v) x).mp
          (hh v (fun i => i.elim0) x)
  | scheme parameter objects p =>
      rw [Sentence.Satisfies, Predicate.satisfies_iff]
      constructor
      · intro h q hq
        obtain ⟨result, rfl⟩ := hq
        intro v η x
        have he : η = (fun i => i.elim0) := funext fun i => i.elim0
        subst η
        exact (p.lower_adequate M result v x).mpr (h v)
      · intro h v
        obtain ⟨x⟩ := M.nonempty ""
        exact (p.lower_adequate M "" v x).mp
          (h _ ⟨"", rfl⟩ v (fun i => i.elim0) x)

def Package.Satisfies (p : Package) (M : Model p) : Prop :=
  ∀ q ∈ p.axioms, q.checked.Satisfies M.base

def Package.nativeTheory (p : Package) :
    Set (Matching.GeneralFixedPoint.Sentence (Predicates.signature p.source.scope)) :=
  {q | ∃ source ∈ p.axioms, q ∈ source.checked.lower}

theorem Package.satisfies_native (p : Package) (M : Model p) :
    p.Satisfies M ↔ ∀ q ∈ p.nativeTheory,
      Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q := by
  constructor
  · intro h q ⟨source, hs, hq⟩
    exact (source.checked.lower_satisfies M.base).mp (h source hs) q hq
  · intro h source hs
    exact (source.checked.lower_satisfies M.base).mpr
      (fun q hq => h q ⟨source, hs, hq⟩)

end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
