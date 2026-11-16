module

public import Silmaril.Logic.Smt.Uflia.Script.Defs

/-! Checked script decoding preserves and reflects satisfaction, SAT and UNSAT.
The sentence map extracts the parser result; the model map is the identity. -/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.Script

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution

theorem holds_iff (s : Accepted) (M : Packaged.GlobalModel) :
    s.Holds M ↔ s.sentence.Holds M := by
  simp [Accepted.Holds, TextHolds, s.parsed]

noncomputable def decodeCorridor : room ⟶ Packaged.concreteRoom where
  sen := Accepted.sentence
  mod := Disc.functor id
  sat M s := (holds_iff s M).symm

theorem decodeCorridor_modelExpansive : decodeCorridor.ModelExpansive :=
  fun M => ⟨M, rfl⟩

noncomputable def decodeComorphism :
    Comorphism institution Packaged.concreteInstitution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => Accepted.sentence) (fun _ => id)
    (fun _ M s => (holds_iff s M).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem decodeComorphism_modelExpansive : ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (decodeComorphism.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

theorem sat_iff (s : Accepted) : s.Sat ↔ s.sentence.Sat := by
  simp only [Accepted.Sat, Packaged.ConcreteSentence.Sat, holds_iff]

theorem unsat_iff (s : Accepted) : s.Unsat ↔ s.sentence.Unsat :=
  not_congr (sat_iff s)

theorem sat_iff_abstract (s : Accepted) : s.Sat ↔ s.sentence.toAbstract.Sat :=
  (sat_iff s).trans (Packaged.concrete_sat_iff s.sentence)

theorem unsat_iff_abstract (s : Accepted) : s.Unsat ↔ s.sentence.toAbstract.Unsat :=
  not_congr (sat_iff_abstract s)

theorem sat_iff_fixed (s : Accepted) :
    s.Sat ↔ Problem.Sat (s.sentence.assertions.map SExpr.Assertion.formula) :=
  (sat_iff s).trans (Packaged.concrete_sat_iff_fixed s.sentence)

theorem unsat_iff_fixed (s : Accepted) :
    s.Unsat ↔ Problem.Unsat (s.sentence.assertions.map SExpr.Assertion.formula) :=
  not_congr (sat_iff_fixed s)

end Silmaril.Logic.Smt.Uflia.Script
