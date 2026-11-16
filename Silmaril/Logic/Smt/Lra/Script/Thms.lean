module

public import Silmaril.Logic.Smt.Lra.Script.Defs
public import Silmaril.Logic.Smt.Lra.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Lra.Script
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

theorem holds_iff (s : Accepted) (M : Model) :
    s.Holds M ↔ s.sentence.assertions.Holds M := by
  simp [Accepted.Holds, TextHolds, s.parsed]

noncomputable def decodeCorridor : room ⟶ Lra.room where
  sen s := s.sentence.assertions
  mod := Disc.functor id
  sat M s := (holds_iff s M).symm

theorem decodeCorridor_modelExpansive : decodeCorridor.ModelExpansive :=
  fun M => ⟨M, rfl⟩

noncomputable def decodeComorphism : Comorphism institution Lra.institution :=
  Comorphism.ofPlain (𝟭 _) (fun _ s => s.sentence.assertions) (fun _ => id)
    (fun _ M s => (holds_iff s M).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem decodeComorphism_modelExpansive : ∀ S,
    Silmaril.Logic.Institution.Corridor.ModelExpansive (decodeComorphism.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

theorem sat_iff (s : Accepted) : s.Sat ↔ s.sentence.assertions.Sat := by
  simp only [Accepted.Sat, Problem.Sat, holds_iff]

theorem unsat_iff (s : Accepted) : s.Unsat ↔ s.sentence.assertions.Unsat :=
  not_congr (sat_iff s)

theorem entails_iff (s : Accepted) (p : Formula) :
    s.Entails p ↔ s.sentence.assertions.Entails p := by
  simp only [Accepted.Entails, Problem.Entails, holds_iff]

theorem source_sat_of_witness (s : Accepted) (M : Model)
    (h : s.sentence.assertions.Holds M) : s.Sat :=
  (sat_iff s).mpr ⟨M, h⟩

theorem source_unsat_of_refutation (s : Accepted)
    (h : ∀ M, s.sentence.assertions.Holds M → False) : s.Unsat :=
  (unsat_iff s).mpr (by rintro ⟨M, hM⟩; exact h M hM)

/-- An abstract semantic consequence can be applied directly to source models. -/
theorem source_consequence (s : Accepted) (p : Formula)
    (h : s.sentence.assertions.Entails p) (M : Model) (hM : s.Holds M) : p.Holds M :=
  h M ((holds_iff s M).mp hM)
end Silmaril.Logic.Smt.Lra.Script
