module

public import Silmaril.Logic.Matching.SortMaps.Thms
public import Silmaril.Logic.FirstOrderLFP.Reachability.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps.Examples
open CategoryTheory

inductive SourceOp : (n : Nat) → (Fin n → Bool) → Bool → Type where
  | step : SourceOp 1 (fun _ => false) true

abbrev source : Signature := ⟨Bool, ⟨SourceOp⟩⟩
abbrev target : Signature := ⟨Unit, ⟨fun _ _ _ => Unit⟩⟩
/-- Sort identification is allowed; no injectivity assumption is hidden. -/
def collapse : source ⟶ target := ⟨fun _ => (), fun _ => ()⟩

abbrev targetModel : FirstOrder.Model target.symbols where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation _ _ := {true}

/-- A source-sort binder feeds an operation whose output is a different sort. -/
def boundStep : FirstOrder.Pattern source.symbols (k := 0) Fin.elim0 true :=
  .ex false (.app .step (fun _ => .var 0))

theorem boundStep_true : true ∈ targetModel.denote (fun i => i.elim0) (Hom.pattern collapse boundStep) := by
  rw [Hom.denote_pattern collapse targetModel boundStep]
  exact ⟨false, fun _ => false, (fun _ => rfl), rfl⟩

theorem boundStep_false : false ∉ targetModel.denote (fun i => i.elim0) (Hom.pattern collapse boundStep) := by
  rw [Hom.denote_pattern collapse targetModel boundStep]
  intro ⟨_, _, _, h⟩
  exact Bool.false_ne_true h

/-- Object and set contexts are both nonempty; sort identification crosses μ/ν. -/
def nested : FixedPoint.Pattern source.symbols (fun _ : Fin 1 => false) (fun _ : Fin 1 => true) true :=
  .mu (P' := Fin.cases true (fun _ : Fin 1 => false))
    (.all false (.disj (.setvar 0)
      (.nu (Γ := Fin.cases false (fun _ : Fin 1 => true)) (P' := Fin.cases true (Fin.cases true (fun _ : Fin 1 => false)))
        (.ex true (.base (.var 0))))))

theorem nested_sort_change (v : ∀ _ : Fin 1, targetModel.carrier ())
    (η : ∀ _ : Fin 1, Set (targetModel.carrier ())) :
    (Hom.fixedPattern collapse nested).denote targetModel v η =
      nested.denote (Hom.reduct collapse targetModel) v η :=
  congrArg (fun F => F η) (Hom.denote_fixedPattern collapse targetModel nested v)

theorem nested_composition :
    Hom.fixedPattern (collapse ≫ 𝟙 target) nested =
      Hom.fixedPattern (𝟙 target) (Hom.fixedPattern collapse nested) :=
  Hom.fixedPattern_comp _ _ _

/-- All existing matching carriers are nonempty: an unchanged empty FOL sort
cannot be expanded, even after arbitrary changes of signature. -/
theorem no_empty_carrier_equivalence (A : Signature) (M : FirstOrder.Model A.symbols)
    (s : A.sorts) : ¬ Nonempty (M.carrier s ≃ Empty) := by
  rintro ⟨e⟩
  obtain ⟨x⟩ := M.nonempty s
  exact (e x).elim

open FirstOrderLFP FirstOrderLFP.Reachability
/-- The source really admits an empty sort, with false existential truth. -/
theorem source_empty_exists_false :
    (fun i => i.elim0) ∉
      (Formula.ex (Δ := context 1) (.base .tt) : Formula signature emptyProfiles (context 0)).denote
        (model Empty (fun _ _ => False)) (fun i => i.elim0) :=
  fun ⟨x, _⟩ => x.elim

/-- Unguarded existential top is true at every world of every matching model.
Thus simply padding the empty source sort changes this formula's truth. -/
theorem target_exists_top (A : Signature) (M : FirstOrder.Model A.symbols)
    (bound : A.sorts) (x : M.carrier bound) :
    x ∈ M.denote (fun i => i.elim0)
      (.ex bound (.neg (.conj (.var 0) (.neg (.var 0)))) : FirstOrder.Pattern A.symbols Fin.elim0 bound) := by
  obtain ⟨value⟩ := M.nonempty bound
  exact ⟨value, fun h => h.2 h.1⟩

end Silmaril.Logic.Matching.SortMaps.Examples

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps.Examples
open FirstOrderLFP FirstOrderLFP.Reachability

/-- A nullary recursive relation has a singleton tuple domain even when all
object carriers are empty; its truth value must not be discarded. -/
theorem empty_nullary_tuple : Nonempty (Tuple (model Empty (fun _ _ => False)) ⟨0, context 0⟩) :=
  ⟨fun i => i.elim0⟩

/-- Binary tuple domains can be empty, so they also need guards in a padded target. -/
theorem empty_binary_tuple : ¬ Nonempty (Tuple (model Empty (fun _ _ => False)) ⟨2, context 2⟩) :=
  fun ⟨x⟩ => (x 0).elim

/-- There are sixteen binary relations on Bool and only four unary subsets.
Encoding all recursive relations in the original unary carrier loses information. -/
theorem no_binary_relations_in_same_unary_carrier :
    ¬ ∃ encode : Set (Fin 2 → Bool) → Set Bool, Function.Injective encode := by
  classical
  rintro ⟨encode, hinj⟩
  have hcard := Fintype.card_le_of_injective encode hinj
  norm_num [Fintype.card_pi_const] at hcard
end Silmaril.Logic.Matching.SortMaps.Examples

/-- info: 'Silmaril.Logic.Matching.SortMaps.Hom.denote_pattern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Hom.denote_pattern
/-- info: 'Silmaril.Logic.Matching.SortMaps.Hom.denote_fixedPattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Hom.denote_fixedPattern
/-- info: 'Silmaril.Logic.Matching.SortMaps.Hom.pattern_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Hom.pattern_comp
/-- info: 'Silmaril.Logic.Matching.SortMaps.Hom.fixedPattern_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Hom.fixedPattern_comp
/-- info: 'Silmaril.Logic.Matching.SortMaps.fixedInstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.fixedInstitution
/-- info: 'Silmaril.Logic.Matching.SortMaps.firstOrderToFixedPoint_modelExpansive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.firstOrderToFixedPoint_modelExpansive
/-- info: 'Silmaril.Logic.Matching.SortMaps.Examples.no_empty_carrier_equivalence' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Examples.no_empty_carrier_equivalence
/-- info: 'Silmaril.Logic.Matching.SortMaps.Examples.source_empty_exists_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Examples.source_empty_exists_false
/-- info: 'Silmaril.Logic.Matching.SortMaps.Examples.no_binary_relations_in_same_unary_carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.SortMaps.Examples.no_binary_relations_in_same_unary_carrier
