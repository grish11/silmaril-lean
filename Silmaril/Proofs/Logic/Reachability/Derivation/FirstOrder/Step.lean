module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Step.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder.Step
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables Silmaril.Logic.FirstOrder.FiniteConnectives
variable {Sg : FOL.Signature} (M : FOL.Structure Sg)

theorem implies_holds {k : Nat} {Γ : Fin k → Sg.S}
    (p q : FOL.Formula Sg Γ) (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (implies p q) a ↔
      (FOL.Formula.Holds M p a → FOL.Formula.Holds M q a) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨hp, hq⟩
  · intro h bad
    exact bad.2 (h bad.1)

/-- A genuine variable-to-variable snapshot reads the chosen source, not outcome. -/
theorem snapshot_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (p : Pattern Sg cfg Γ) (v w : M.carrier cfg)
    (a : (i : Fin k) → M.carrier (Γ i)) :
    Pattern.localHolds (snapshot cfg Γ p) M (consAssignment M cfg Γ w a) v ↔
      Pattern.localHolds p M a w := by
  exact holds_rename M p (Δ := Fin.cases cfg (Fin.cases cfg Γ)) Fin.succ
    (fun _ => rfl) (consAssignment M cfg (Fin.cases cfg Γ) v (consAssignment M cfg Γ w a))

/-- Every assignment is reconstructed from its two projections; no nonemptiness
hypothesis or bundled-valuation object-language sort is involved. -/
theorem join_projections {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (d : (i : Fin (blockSize xs k)) → M.carrier (blockContext Γ xs i)) :
    joinAssignment M (outerAssignment M Γ xs d) xs (blockAssignment M Γ xs d) = d := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => d j.succ)) j

theorem outer_join {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (a : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    outerAssignment M Γ xs (joinAssignment M a xs b) = a := by
  induction xs with
  | nil => rfl
  | cons s xs ih => exact ih b.2

theorem block_join {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (a : (i : Fin k) → M.carrier (Γ i)) (b : BlockAssignment M xs) :
    blockAssignment M Γ xs (joinAssignment M a xs b) = b := by
  induction xs with
  | nil => cases b; rfl
  | cons s xs ih => exact congrArg (fun tail => (b.1, tail)) (ih b.2)

theorem coverage_holds {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P : Pattern Sg cfg Γ)
    (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier cfg) :
    Pattern.localHolds (coverageFormula rules P) M a w ↔
      (Pattern.localHolds P M a w →
        ∃ i b, (schemes M rules i).lhs b w) := by
  unfold coverageFormula Pattern.localHolds
  rw [implies_holds, finiteOr_holds]
  constructor
  · intro h hp
    obtain ⟨p, hpList, hp⟩ := h hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpList
    obtain ⟨b, hb⟩ := (existsBlock_holds M cfg Γ (rules i).telescope _ w a).mp hp
    exact ⟨i, b, (liftRule_holds M cfg Γ (rules i).telescope (rules i).lhs w a b).mp hb⟩
  · intro h hp
    obtain ⟨i, b, hb⟩ := h hp
    refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    apply (existsBlock_holds M cfg Γ (rules i).telescope _ w a).mpr
    exact ⟨b, (liftRule_holds M cfg Γ (rules i).telescope (rules i).lhs w a b).mpr hb⟩

theorem snapshotSource_holds {cfg : Sg.S} {k : Nat} (Γ : Fin k → Sg.S)
    (xs : List Sg.S) (P : Pattern Sg cfg Γ) (lhs : RulePattern cfg xs)
    (a : (j : Fin k) → M.carrier (Γ j)) (b : BlockAssignment M xs)
    (v : M.carrier cfg) :
    Pattern.localHolds (snapshotSource Γ xs P lhs) M (joinAssignment M a xs b) v ↔
      ∃ w, Pattern.localHolds P M a w ∧
        Pattern.localHolds lhs M
          (joinAssignment M (Γ := emptyContext) (fun i => i.elim0) xs b) w := by
  refine (existsCaptured_holds M cfg cfg (blockContext Γ xs)
    (snapshot cfg (blockContext Γ xs)
      (.and (weakenBlock cfg Γ xs P) (liftRule cfg Γ xs lhs)))
    v (joinAssignment M a xs b)).trans ?_
  apply exists_congr
  intro w
  change Pattern.localHolds (snapshot cfg (blockContext Γ xs)
    (.and (weakenBlock cfg Γ xs P) (liftRule cfg Γ xs lhs))) M
    (consAssignment M cfg (blockContext Γ xs) w (joinAssignment M a xs b)) v ↔ _
  rw [snapshot_holds]
  change (FOL.Formula.Holds M (weakenBlock cfg Γ xs P) _ ∧
    FOL.Formula.Holds M (liftRule cfg Γ xs lhs) _) ↔ _
  exact and_congr (weakenBlock_holds M cfg Γ xs P w a b)
    (liftRule_holds M cfg Γ xs lhs w a b)

theorem successors_holds {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (i : Fin r) (P Q : Pattern Sg cfg Γ)
    (a : (j : Fin k) → M.carrier (Γ j)) (b : BlockAssignment M (rules i).telescope)
    (v : M.carrier cfg) :
    Pattern.localHolds (successorsFormula rules i P Q) M
      (joinAssignment M a (rules i).telescope b) v ↔
    ((∃ w, Pattern.localHolds P M a w ∧ (schemes M rules i).lhs b w) →
      (schemes M rules i).rhs b v → Pattern.localHolds Q M a v) := by
  unfold successorsFormula
  change FOL.Formula.Holds M (implies _ _)
    (consAssignment M cfg _ v (joinAssignment M a (rules i).telescope b)) ↔ _
  rw [implies_holds]
  change ((Pattern.localHolds (snapshotSource Γ (rules i).telescope P (rules i).lhs)
      M (joinAssignment M a (rules i).telescope b) v ∧
    Pattern.localHolds (liftRule cfg Γ (rules i).telescope (rules i).rhs)
      M (joinAssignment M a (rules i).telescope b) v) →
    Pattern.localHolds (weakenBlock cfg Γ (rules i).telescope Q)
      M (joinAssignment M a (rules i).telescope b) v) ↔ _
  rw [snapshotSource_holds]
  change (((∃ w, Pattern.localHolds P M a w ∧ (schemes M rules i).lhs b w) ∧
    FOL.Formula.Holds M (liftRule cfg Γ (rules i).telescope (rules i).rhs) _) →
    FOL.Formula.Holds M (weakenBlock cfg Γ (rules i).telescope Q) _) ↔ _
  rw [liftRule_holds, weakenBlock_holds]
  constructor
  · intro h hex hr
    exact h ⟨hex, hr⟩
  · intro h pair
    exact h pair.1 pair.2

theorem coverage_valid_iff {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P : Pattern Sg cfg Γ) :
    (∀ a w, Pattern.localHolds (coverageFormula rules P) M a w) ↔
      ∀ a, RuleSystem.Covers (schemes M rules) (Pattern.localHolds P M a) := by
  simp only [coverage_holds, RuleSystem.Covers]

theorem successors_valid_iff {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P Q : Pattern Sg cfg Γ) :
    (∀ i (d : (j : Fin (blockSize (rules i).telescope k)) →
        M.carrier (blockContext Γ (rules i).telescope j)) v,
      Pattern.localHolds (successorsFormula rules i P Q) M d v) ↔
      ∀ a, RuleSystem.SuccessorsIn (schemes M rules)
        (Pattern.localHolds P M a) (Pattern.localHolds Q M a) := by
  constructor
  · intro h a i b w v hp hl hr
    exact (successors_holds M rules i P Q a b v).mp
      (h i (joinAssignment M a (rules i).telescope b) v) ⟨w, hp, hl⟩ hr
  · intro h i d v
    rw [← join_projections M Γ (rules i).telescope d]
    apply (successors_holds M rules i P Q _ _ v).mpr
    rintro ⟨w, hp, hl⟩ hr
    exact h _ i _ w v hp hl hr

/-- Exact correspondence of the two Step premises, not a converse theorem
about arbitrary derivability by other constructors. -/
theorem premises_iff {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P Q : Pattern Sg cfg Γ) :
    ((∀ a w, Pattern.localHolds (coverageFormula rules P) M a w) ∧
      (∀ i d v, Pattern.localHolds (successorsFormula rules i P Q) M d v)) ↔
    ((∀ a, RuleSystem.Covers (schemes M rules) (Pattern.localHolds P M a)) ∧
      (∀ a, RuleSystem.SuccessorsIn (schemes M rules)
        (Pattern.localHolds P M a) (Pattern.localHolds Q M a))) :=
  and_congr (coverage_valid_iff M rules P) (successors_valid_iff M rules P Q)

/-- Construct the actual calculus Step from validity of actual formulas. -/
def step_of_formulas {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P Q : Pattern Sg cfg Γ)
    {E C : Set (Claim Sg cfg Γ)}
    (cover : ∀ a w, Pattern.localHolds (coverageFormula rules P) M a w)
    (succ : ∀ i d v, Pattern.localHolds (successorsFormula rules i P Q) M d v) :
    Derives M (schemes M rules) E C ⟨P, Q⟩ :=
  .step ((coverage_valid_iff M rules P).mp cover)
    ((successors_valid_iff M rules P Q).mp succ)

/-- Empty rule families really have a false coverage consequent. -/
theorem coverage_empty {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin 0 → FormulaRule cfg) (P : Pattern Sg cfg Γ)
    (a : (j : Fin k) → M.carrier (Γ j)) (w : M.carrier cfg) :
    Pattern.localHolds (coverageFormula rules P) M a w ↔ ¬ Pattern.localHolds P M a w := by
  rw [coverage_holds]
  constructor
  · intro h hp
    obtain ⟨i, _⟩ := h hp
    exact i.elim0
  · intro h hp
    exact False.elim (h hp)

end Silmaril.Logic.Reachability.Derivation.FirstOrder.Step
