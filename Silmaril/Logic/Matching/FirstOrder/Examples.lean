module

public import Silmaril.Logic.Matching.FirstOrder.Thms
public import Silmaril.Logic.Algebraic.ManySorted.SingleSorted

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.Examples

inductive Symbol : Nat → Type where
  | initial : Symbol 0
  | step : Symbol 1
  | stuck : Symbol 0

def signature := Algebraic.SingleSorted.ofArity Symbol

/-- A finite transition system: false has both successors; true has none. -/
def transitions : Model signature where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation op args := match op with
    | .initial => {false}
    | .step => if args 0 = false then Set.univ else ∅
    | .stuck => ∅

def initial : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := Fin.elim0) Symbol.initial (fun i : Fin 0 => nomatch i)

def afterOneStep : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := fun _ => PUnit.unit) Symbol.step (fun _ => initial)

def stuck : Pattern signature Fin.elim0 PUnit.unit :=
  .app (inputs := Fin.elim0) Symbol.stuck (fun i : Fin 0 => nomatch i)

theorem initial_denotation :
    transitions.denote (fun i : Fin 0 => nomatch i) initial = {false} := by
  exact transitions.denote_nullary _ Symbol.initial

theorem stuck_denotation :
    transitions.denote (fun i : Fin 0 => nomatch i) stuck = ∅ := by
  exact transitions.denote_nullary _ Symbol.stuck

/-- Both distinct states match the one-step pattern; this is nondeterministic. -/
theorem afterOneStep_denotation :
    transitions.denote (fun i : Fin 0 => nomatch i) afterOneStep = Set.univ := by
  ext result
  constructor
  · intro _; trivial
  · intro _
    change ∃ values : Fin 1 → Bool,
      (∀ i, values i ∈ transitions.denote (fun j : Fin 0 => nomatch j) initial) ∧
        result ∈ transitions.operation Symbol.step values
    refine ⟨fun _ => false, ?_, ?_⟩
    · intro i
      rw [initial_denotation]
      rfl
    · change result ∈ (if false = false then Set.univ else ∅)
      simp

theorem two_distinct_outputs :
    false ∈ transitions.denote (fun i : Fin 0 => nomatch i) afterOneStep ∧
    true ∈ transitions.denote (fun i : Fin 0 => nomatch i) afterOneStep ∧ false ≠ true := by
  rw [afterOneStep_denotation]
  exact ⟨trivial, trivial, Bool.false_ne_true⟩

/-- The nondeterministic image covers all states, so it is globally satisfied. -/
def oneStepSentence : Sentence signature := ⟨0, Fin.elim0, PUnit.unit, afterOneStep⟩
theorem oneStep_satisfied : Sentence.Satisfies transitions oneStepSentence := by
  unfold Sentence.Satisfies oneStepSentence
  dsimp only
  intro v result
  have same : v = (fun i : Fin 0 => nomatch i) := by funext i; exact Fin.elim0 i
  change result ∈ transitions.denote v afterOneStep
  rw [same, afterOneStep_denotation]
  trivial

/-- The empty interpretation gives an explicit counterexample to satisfaction. -/
def stuckSentence : Sentence signature := ⟨0, Fin.elim0, PUnit.unit, stuck⟩
theorem stuck_not_satisfied : ¬ Sentence.Satisfies transitions stuckSentence := by
  intro h
  have member := h (fun i : Fin 0 => nomatch i) false
  change false ∈ transitions.denote (fun i : Fin 0 => nomatch i) stuck at member
  rw [stuck_denotation] at member
  exact member
end Silmaril.Logic.Matching.FirstOrder.Examples
