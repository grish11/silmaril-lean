module

public import Silmaril.Logic.Inst.Satisfiability.Defs
public import Silmaril.Logic.Institution.Faithful

@[expose] public section
namespace Silmaril.Logic.Institution

universe w m₁ m₂ u₁ v₁ u₂ v₂

namespace Room
variable {R : Room.{w, m₁, m₂}} {Γ Δ : Set R.Sen}

theorem satisfiable_iff (R : Room.{w, m₁, m₂}) (Γ : Set R.Sen) :
    R.Satisfiable Γ ↔ ∃ M, ∀ φ ∈ Γ, R.Sat M φ := Iff.rfl

theorem unsatisfiable_iff (R : Room.{w, m₁, m₂}) (Γ : Set R.Sen) :
    R.Unsatisfiable Γ ↔ ∀ M, ¬ M ∈ R.modelsOf Γ := by
  simp only [Unsatisfiable, Satisfiable, not_exists]

/-- Removing assumptions preserves a SAT witness. -/
theorem Satisfiable.mono (sat : R.Satisfiable Δ) (h : Γ ⊆ Δ) :
    R.Satisfiable Γ := by
  obtain ⟨M, holds⟩ := sat
  exact ⟨M, fun φ hφ => holds φ (h hφ)⟩

/-- Adding assumptions preserves a refutation. -/
theorem Unsatisfiable.mono (unsat : R.Unsatisfiable Γ) (h : Γ ⊆ Δ) :
    R.Unsatisfiable Δ := fun sat => unsat (sat.mono h)

/-- The empty theory is SAT precisely when the room has a model. -/
theorem empty_satisfiable_iff (R : Room.{w, m₁, m₂}) :
    R.Satisfiable ∅ ↔ Nonempty R.Mod := by
  constructor
  · rintro ⟨M, _⟩
    exact ⟨M⟩
  · rintro ⟨M⟩
    exact ⟨M, fun _ h => h.elim⟩

/-- Refutation implies every semantic consequence, including in an empty room. -/
theorem Unsatisfiable.entails (h : R.Unsatisfiable Γ) (φ : R.Sen) :
    R.Entails Γ φ := fun M holds => (h ⟨M, holds⟩).elim

end Room

namespace Corridor
variable {R₁ R₂ : Room.{w, m₁, m₂}} (c : R₁ ⟶ R₂)

/-- A target witness reduces to one source model satisfying all original
sentences. Arbitrary symbol identifications are allowed in the corridor. -/
theorem satisfiable_of_map {Γ : Set R₁.Sen}
    (sat : R₂.Satisfiable (c.sen '' Γ)) : R₁.Satisfiable Γ := by
  obtain ⟨N, holds⟩ := sat
  exact ⟨c.mod.obj N, fun φ hφ => (c.sat N φ).mp (holds _ ⟨φ, hφ, rfl⟩)⟩

/-- Every corridor transports a source refutation to its translated theory. -/
theorem unsatisfiable_map {Γ : Set R₁.Sen}
    (unsat : R₁.Unsatisfiable Γ) : R₂.Unsatisfiable (c.sen '' Γ) :=
  fun sat => unsat (c.satisfiable_of_map sat)

/-- Sentence agreement with an expansion supplies the converse SAT direction.
Equality of the original model with the reduct is unnecessary. -/
theorem satisfiable_map_iff_of_elemExpansive (hc : c.ElemExpansive)
    (Γ : Set R₁.Sen) :
    R₁.Satisfiable Γ ↔ R₂.Satisfiable (c.sen '' Γ) := by
  constructor
  · rintro ⟨M, holds⟩
    obtain ⟨N, agrees⟩ := hc M
    refine ⟨N, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact (c.sat N φ).mpr ((agrees φ).mpr (holds φ hφ))
  · exact c.satisfiable_of_map

theorem unsatisfiable_map_iff_of_elemExpansive (hc : c.ElemExpansive)
    (Γ : Set R₁.Sen) :
    R₁.Unsatisfiable Γ ↔ R₂.Unsatisfiable (c.sen '' Γ) :=
  not_congr (c.satisfiable_map_iff_of_elemExpansive hc Γ)

end Corridor

namespace Inst.CoHom
variable {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}

theorem satisfiable_iff_of_elemExpansive (f : CoHom A B) (hf : f.ElemExpansive)
    (S : A.Sign) (Γ : Set (A.I.obj S).Sen) :
    (A.I.obj S).Satisfiable Γ ↔
      (B.I.obj (f.Φ.obj S)).Satisfiable ((f.ρ.app S).sen '' Γ) :=
  (f.ρ.app S).satisfiable_map_iff_of_elemExpansive (hf S) Γ

theorem unsatisfiable_iff_of_elemExpansive (f : CoHom A B) (hf : f.ElemExpansive)
    (S : A.Sign) (Γ : Set (A.I.obj S).Sen) :
    (A.I.obj S).Unsatisfiable Γ ↔
      (B.I.obj (f.Φ.obj S)).Unsatisfiable ((f.ρ.app S).sen '' Γ) :=
  (f.ρ.app S).unsatisfiable_map_iff_of_elemExpansive (hf S) Γ

end Inst.CoHom
end Silmaril.Logic.Institution
