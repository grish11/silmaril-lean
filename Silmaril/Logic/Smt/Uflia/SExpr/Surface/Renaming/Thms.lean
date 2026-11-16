module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming
open SExpr.Renaming

/-- This is fixed-signature comparison expansion, not expansion along arbitrary
symbol-identifying name maps. -/
theorem comparison_modelExpansive : ∀ S,
    Silmaril.Logic.Institution.Corridor.ModelExpansive (comparison.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

theorem comparisonReverse_modelExpansive : ∀ S,
    Silmaril.Logic.Institution.Corridor.ModelExpansive (comparisonReverse.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

theorem decodeComorphism_modelExpansive : ∀ S,
    Silmaril.Logic.Institution.Corridor.ModelExpansive (decodeComorphism.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

/-- Comparison changes neither models nor sentences, hence preserves SAT exactly. -/
theorem sat_iff (checked : DeclarationPrefix) (s : Concrete.Sentence checked.environment) :
    (∃ M, Holds checked M s) ↔ ∃ M, Concrete.Holds M s :=
  exists_congr (fun M => holds_iff checked M s)

theorem unsat_iff (checked : DeclarationPrefix) (s : Concrete.Sentence checked.environment) :
    (¬ ∃ M, Holds checked M s) ↔ ¬ ∃ M, Concrete.Holds M s :=
  not_congr (sat_iff checked s)

/-- UNSAT travels along every coherent name map. SAT in the reverse direction
follows by reduct; SAT forward would require a separate model-expansion proof. -/
theorem unsat_map {S T : PrefixSignature} (f : S ⟶ T)
    (s : Concrete.Sentence S.prefix.environment)
    (h : ¬ ∃ M, Holds S.prefix M s) :
    ¬ ∃ M, Holds T.prefix M (Concrete.Sentence.map f s) := by
  rintro ⟨M, hM⟩
  exact h ⟨Uflia.Model.reduct f.abstract M, (holds_map f M s).mp hM⟩

/-- Finite theories use one model for all direct sentences. -/
def TheoryHolds (checked : DeclarationPrefix)
    (M : Uflia.Model checked.environment.signature)
    (sentences : List (Concrete.Sentence checked.environment)) : Prop :=
  ∀ s ∈ sentences, Holds checked M s

/-- Actual solver refutations of decoded theories transport through arbitrary
name maps without translating or trusting the solver proof syntax again. -/
theorem theory_unsat_map {S T : PrefixSignature} (f : S ⟶ T)
    (sentences : List (Concrete.Sentence S.prefix.environment))
    (h : ¬ ∃ M, TheoryHolds S.prefix M sentences) :
    ¬ ∃ M, TheoryHolds T.prefix M (sentences.map (Concrete.Sentence.map f)) := by
  rintro ⟨M, hM⟩
  apply h
  refine ⟨Uflia.Model.reduct f.abstract M, ?_⟩
  intro s hs
  exact (holds_map f M s).mp (hM _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

end Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming
