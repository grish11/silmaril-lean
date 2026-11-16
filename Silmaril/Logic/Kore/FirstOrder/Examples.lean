module

public import Silmaril.Logic.Kore.FirstOrder.Thms
public import Silmaril.Logic.Matching.FirstOrder.Examples

@[expose] public section
namespace Silmaril.Logic.Kore.FirstOrder.Examples
open Matching.FirstOrder.Examples (Symbol signature transitions)

/-- These are source-fragment ASTs, not aliases of matching patterns. -/
def initial : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := Fin.elim0) Symbol.initial (fun i : Fin 0 => nomatch i)
def step : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := fun _ => PUnit.unit) Symbol.step (fun _ => initial)
def stuck : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := Fin.elim0) Symbol.stuck (fun i : Fin 0 => nomatch i)

theorem lower_initial : initial.lower = Matching.FirstOrder.Examples.initial := by
  unfold initial Pattern.lower Matching.FirstOrder.Examples.initial
  apply congrArg (Matching.FirstOrder.Pattern.app (A := signature) (Γ := Fin.elim0)
    (inputs := Fin.elim0) (output := PUnit.unit) Symbol.initial)
  funext i; exact Fin.elim0 i
theorem lower_step : step.lower = Matching.FirstOrder.Examples.afterOneStep := by
  unfold step Matching.FirstOrder.Examples.afterOneStep
  simp only [Pattern.lower, lower_initial]
theorem lower_stuck : stuck.lower = Matching.FirstOrder.Examples.stuck := by
  unfold stuck Pattern.lower Matching.FirstOrder.Examples.stuck
  apply congrArg (Matching.FirstOrder.Pattern.app (A := signature) (Γ := Fin.elim0)
    (inputs := Fin.elim0) (output := PUnit.unit) Symbol.stuck)
  funext i; exact Fin.elim0 i

theorem initial_denotation :
    denote signature transitions (fun i : Fin 0 => nomatch i) initial = {false} := by
  rw [← denote_lower, lower_initial]
  exact Matching.FirstOrder.Examples.initial_denotation
theorem step_denotation :
    denote signature transitions (fun i : Fin 0 => nomatch i) step = Set.univ := by
  rw [← denote_lower, lower_step]
  exact Matching.FirstOrder.Examples.afterOneStep_denotation
theorem stuck_denotation :
    denote signature transitions (fun i : Fin 0 => nomatch i) stuck = ∅ := by
  rw [← denote_lower, lower_stuck]
  exact Matching.FirstOrder.Examples.stuck_denotation

/-- A logical filter keeps exactly the successor distinct from the initial state. -/
def otherSuccessor : Pattern signature Fin.elim0 PUnit.unit := .and step (.not initial)
theorem otherSuccessor_denotation :
    denote signature transitions (fun i : Fin 0 => nomatch i) otherSuccessor = {true} := by
  ext result
  change Bool at result
  change (result ∈ denote signature transitions _ step ∧
    result ∉ denote signature transitions _ initial) ↔ result = true
  rw [step_denotation, initial_denotation]
  change (True ∧ ¬ result = false) ↔ result = true
  cases result <;> decide

/-- Existential element binding can also describe a successor different from its input. -/
def changesState : Pattern signature Fin.elim0 PUnit.unit :=
  .exists PUnit.unit (.and
    (.app (inputs := fun _ => PUnit.unit) Symbol.step (fun _ => .evar 0))
    (.not (.evar 0)))

theorem changesState_denotation :
    denote signature transitions (fun i : Fin 0 => nomatch i) changesState = {true} := by
  ext result
  change (∃ value : Bool, (∃ values : Fin 1 → Bool,
    (∀ i, values i = value) ∧ result ∈ transitions.operation Symbol.step values) ∧
      ¬ result = value) ↔ result = true
  constructor
  · rintro ⟨value, ⟨values, hvalues, hresult⟩, hne⟩
    cases value with
    | false =>
        cases result with
        | false => exact False.elim (hne rfl)
        | true => rfl
    | true =>
        change result ∈ (if values 0 = false then Set.univ else ∅) at hresult
        rw [hvalues 0] at hresult
        exact False.elim hresult
  · intro hresult
    subst result
    exact ⟨false, ⟨fun _ => false, fun _ => rfl, by change true ∈ Set.univ; trivial⟩,
      Bool.false_ne_true.symm⟩

/-- Both distinct results match step(initial), and stuck matches neither result. -/
theorem nonvacuous :
    false ∈ denote signature transitions (fun i : Fin 0 => nomatch i) step ∧
    true ∈ denote signature transitions (fun i : Fin 0 => nomatch i) step ∧
    false ≠ true ∧
    false ∉ denote signature transitions (fun i : Fin 0 => nomatch i) stuck := by
  rw [step_denotation, stuck_denotation]
  exact ⟨trivial, trivial, Bool.false_ne_true, id⟩

def stepSentence : Sentence signature := ⟨0, Fin.elim0, PUnit.unit, step⟩
theorem step_satisfied : Sentence.Satisfies transitions stepSentence := by
  unfold Sentence.Satisfies stepSentence
  dsimp only
  intro v result
  have same : v = (fun i : Fin 0 => nomatch i) := by funext i; exact Fin.elim0 i
  change result ∈ denote signature transitions v step
  rw [same, step_denotation]
  trivial

def stuckSentence : Sentence signature := ⟨0, Fin.elim0, PUnit.unit, stuck⟩
theorem stuck_not_satisfied : ¬ Sentence.Satisfies transitions stuckSentence := by
  intro h
  have member := h (fun i : Fin 0 => nomatch i) false
  change false ∈ denote signature transitions (fun i : Fin 0 => nomatch i) stuck at member
  rw [stuck_denotation] at member
  exact member

/-- A binder formula is inhabited without being globally valid. -/
def changesSentence : Sentence signature := ⟨0, Fin.elim0, PUnit.unit, changesState⟩
theorem changes_not_satisfied : ¬ Sentence.Satisfies transitions changesSentence := by
  intro h
  have member := h (fun i : Fin 0 => nomatch i) false
  change false ∈ denote signature transitions (fun i : Fin 0 => nomatch i) changesState at member
  rw [changesState_denotation] at member
  exact Bool.false_ne_true member
end Silmaril.Logic.Kore.FirstOrder.Examples
