module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Base.Thms
public import Silmaril.Logic.Temporal.Buchi.Automaton.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Base.Examples
open ModalMu

/-- The existing genuinely nondeterministic symbolic example now runs on Nat,
not on a world/state product. Every world has infinitely many successors. -/
theorem infinite_branching : Sat Automaton.Examples.branchingModel
    (formula Automaton.Examples.guardedChoice ()) :=
  (formula_correct _ _ _ emptyEnv _).mpr Automaton.Examples.symbolic_infinite_branching

/-- Any accepting state still needs a first graph edge. -/
theorem deadlock {S : Signature} {n : Nat} (A : Symbolic S.Atom n) (M : Model S)
    (a : S.Action) (dead : ∀ v, ¬ M.step a M.point v) : ¬ Sat M (formula A a) := by
  intro h
  exact not_acceptsPath_of_deadlock A.automaton _ _ M.point dead
    ((formula_correct A a M emptyEnv M.point).mp h)

theorem zero_states {S : Signature} (A : Symbolic S.Atom 0) (a : S.Action) :
    formula A a = .bot := rfl

def requiresAtom : Symbolic Unit 1 where
  initial := Set.univ
  guard _ _ := .pos ()
  accepting := Set.univ

def sourceModel : Model Automaton.Examples.demoSignature where
  World := Nat
  step _ w v := v = w+1
  valuation _ := {w | 0 < w}
  point := 0

/-- Replacing source guards by successor guards would wrongly accept this model. -/
theorem source_guard_rejected : ¬ Sat sourceModel (formula requiresAtom ()) := by
  intro h
  obtain ⟨p, ⟨h0, _⟩, r, _, hr, _⟩ :=
    (formula_correct (S := Automaton.Examples.demoSignature) requiresAtom () sourceModel emptyEnv sourceModel.point).mp h
  delta sourceModel at p h0 hr
  have hp : 0 < (p 0 : Nat) := hr 0
  change (p 0 : Nat) = 0 at h0
  rw [h0] at hp
  exact Nat.lt_irrefl 0 hp

/-- Three states: arbitrarily late single visits cannot form one recurrent run. -/
def oneVisit : Symbolic Unit 3 where
  initial := {0}
  guard q r := if q = 0 ∨ r = 2 then .top else .bot
  accepting := {1}

theorem incoherent_visits_rejected (M : Model Automaton.Examples.demoSignature) :
    ¬ Sat M (formula oneVisit ()) := by
  classical
  intro h
  obtain ⟨p, _, r, hi, hr, hf⟩ := (formula_correct (S := Automaton.Examples.demoSignature) oneVisit () M emptyEnv M.point).mp h
  apply Automaton.Examples.oneVisit_not_accepts
  refine ⟨r, hi, ?_, hf⟩
  intro k
  have hs := hr k
  change r k = 0 ∨ r (k+1) = 2
  by_cases he : r k = 0 ∨ r (k+1) = 2
  · exact he
  · simp [oneVisit, Symbolic.automaton, he, Guard.Holds] at hs

end Silmaril.Logic.Temporal.Buchi.Automaton.Base.Examples
