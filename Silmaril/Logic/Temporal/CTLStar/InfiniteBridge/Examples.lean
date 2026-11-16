module

public import Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Thms
public import Silmaril.Logic.Temporal.LTL.Tableau.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Examples
open Buchi.Automaton

theorem weakNext_false_rejects (word : Nat → Unit → Prop) :
    ¬ (automaton (.weakNext .bot)).Accepts word := by
  rw [accepts_iff]
  exact fun h => h trivial

theorem strongNext_true_accepts (word : Nat → Unit → Prop) :
    (automaton (.strongNext .top)).Accepts word := by
  rw [accepts_iff]
  exact ⟨trivial, trivial⟩

theorem weakNext_true_accepts (word : Nat → Unit → Prop) :
    (automaton (.weakNext .top)).Accepts word := by
  rw [accepts_iff]
  exact fun _ => trivial

theorem next_agrees {A : Type} (p : NNF.Formula A) (word : Nat → A → Prop) :
    (automaton (.strongNext p)).Accepts word ↔ (automaton (.weakNext p)).Accepts word := by
  rfl

theorem postponed_until_rejects (word : Nat → Unit → Prop) :
    ¬ (automaton (.until .top .bot)).Accepts word := by
  rw [accepts_iff]
  rintro ⟨d, _, hd, _⟩
  exact hd

/-- The actual reused transition equations allow postponement; Büchi
recurrence rejects it, which is essential on an infinite run. -/
theorem postponing_local (letter : Unit → Prop) :
    LTL.Tableau.Local (NNF.Formula.until (.top : NNF.Formula Unit) .bot).toInfinite
      letter LTL.Tableau.Examples.postponing LTL.Tableau.Examples.postponing :=
  LTL.Tableau.Examples.postponing_local letter

theorem postponing_not_fair :
    ¬ LTL.Tableau.Fair (NNF.Formula.until (.top : NNF.Formula Unit) .bot).toInfinite
      (fun _ => LTL.Tableau.Examples.postponing) :=
  LTL.Tableau.Examples.postponing_not_fair

theorem release_forever_accepts (word : Nat → Unit → Prop) :
    (automaton (.release .bot .top)).Accepts word := by
  rw [accepts_iff]
  intro d _
  exact Or.inl trivial

theorem release_false_rejects (word : Nat → Unit → Prop) :
    ¬ (automaton (.release .bot .bot)).Accepts word := by
  rw [accepts_iff]
  intro h
  rcases h 0 trivial with hf | ⟨j, hj, _⟩
  · exact hf
  · omega

theorem distinct_atoms_accept :
    (automaton (.conj (.pos true) (.neg false))).Accepts (fun _ a => a = true) := by
  rw [accepts_iff]
  exact ⟨rfl, Bool.noConfusion⟩

theorem atom_collapse (word : Nat → Unit → Prop) :
    ¬ (automaton ((.conj (.pos true) (.neg false) : NNF.Formula Bool).map (fun _ => ()))).Accepts word := by
  rw [accepts_iff]
  exact fun h => h.2 h.1

def sig : ModalMu.Signature := ⟨Unit, Unit⟩

def singleton : ModalMu.Model sig where
  World := Unit
  step _ _ _ := False
  valuation _ := Set.univ
  point := ()

theorem deadlock_no_infinite : ¬ ModalMu.Sat singleton (formula .top ()) := by
  intro h
  obtain ⟨path, ⟨_, edges⟩, _⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  exact edges 0

def loop : ModalMu.Model sig where
  World := Unit
  step _ _ _ := True
  valuation _ := Set.univ
  point := ()

theorem loop_true_accepts : ModalMu.Sat loop (formula .top ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  exact ⟨fun _ => (), ⟨rfl, fun _ => trivial⟩, trivial⟩

theorem loop_postponed_until_rejects : ¬ ModalMu.Sat loop (formula (.until .top .bot) ()) := by
  intro h
  obtain ⟨path, _, d, _, hd, _⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  exact hd

def branchSig : ModalMu.Signature := ⟨Bool, Unit⟩

/-- Two disjoint looping successors; the initial world chooses one branch. -/
def branch : ModalMu.Model branchSig where
  World := Option Bool
  step _ w v := (w = none ∧ ∃ b, v = some b) ∨ (w = v ∧ w ≠ none)
  valuation b := {w | w = some b}
  point := none

theorem branch_each (b : Bool) : ModalMu.Sat branch (formula (.strongNext (.pos b)) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  refine ⟨fun t => if t = 0 then none else some b, ⟨rfl, ?_⟩, trivial, rfl⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact Or.inl ⟨rfl, b, rfl⟩
  · have hn : i+1 ≠ 0 := by omega
    exact Or.inr ⟨by simp only [hi, hn, ↓reduceIte], by simp [hi]⟩

/-- One coherent path cannot satisfy constraints from two distinct successors. -/
theorem branch_collision :
    ¬ ModalMu.Sat branch
      (formula (.conj (.strongNext (.pos false)) (.strongNext (.pos true))) ()) := by
  intro h
  obtain ⟨path, _, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  have hf : path 1 = some false := hp.1.2
  have ht : path 1 = some true := hp.2.2
  cases hf.symm.trans ht

/-- The source world is read before taking any transition. -/
theorem source_timing_rejects :
    ¬ ModalMu.Sat branch (formula (.conj (.pos true) (.strongNext (.pos true))) ()) := by
  intro h
  obtain ⟨path, ⟨h0, _⟩, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  have hs : path 0 = some true := hp.1
  cases h0.symm.trans hs

end Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Examples
