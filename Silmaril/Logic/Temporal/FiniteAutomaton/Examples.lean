module

public import Silmaril.Logic.Temporal.FiniteAutomaton.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.FiniteAutomaton.Examples
open ModalMu Buchi.Automaton

def single {A : Type} (edge endpoint : Guard A) : Symbolic A 1 where
  initial := Set.univ
  guard _ _ := edge
  terminal _ := endpoint

def sig : Signature := ⟨Unit, Unit⟩

def singleton : Model sig where
  World := Unit
  step _ _ _ := False
  valuation _ := Set.univ
  point := ()

/-- The endpoint consumes the initial letter and needs no additional edge. -/
theorem singleton_zero_edge : Sat singleton (formula (single .bot .top) ()) := by
  apply (formula_iff_run _ _ _ emptyEnv _).mpr
  exact ⟨0, trivial, .terminal trivial (fun _ h => h)⟩

theorem singleton_false_terminal : ¬ Sat singleton (formula (single .top .bot) ()) := by
  intro h
  obtain ⟨q, _, hr⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  obtain ⟨v, r, ht, _⟩ := run_has_terminal _ _ _ hr
  exact ht

def chain : Model sig where
  World := Bool
  step _ w v := w = false ∧ v = true
  valuation _ := {w | w = true}
  point := false

theorem one_edge : Sat chain (formula (single .top (.pos ())) ()) := by
  apply (formula_iff_run _ _ _ emptyEnv _).mpr
  refine ⟨0, trivial, RunFrom.step (r := 0) trivial ⟨rfl, rfl⟩ (.terminal rfl ?_)⟩
  intro v hv
  exact Bool.noConfusion hv.1

/-- A true terminal label at the successor cannot satisfy the source edge guard. -/
theorem source_guard_timing : ¬ Sat chain (formula (single (.pos ()) (.pos ())) ()) := by
  intro h
  obtain ⟨q, _, hr⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  cases hr with
  | terminal ht _ => exact Bool.noConfusion ht
  | step hg _ _ => exact Bool.noConfusion hg

def loop : Model sig where
  World := Unit
  step _ _ _ := True
  valuation _ := Set.univ
  point := ()

/-- Even an enabled endpoint guard cannot stop at a nondeadlocked world. -/
theorem nondeadlock_rejected : ¬ Sat loop (formula (single .bot .top) ()) := by
  intro h
  obtain ⟨q, _, hr⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  exact no_run_of_serial _ _ _ (fun _ => ⟨(), trivial⟩) _ q hr

/-- Cycling transitions do not create a finite accepting path. -/
theorem endless_cycle_rejected : ¬ Sat loop (formula (single .top .top) ()) := by
  intro h
  obtain ⟨q, _, hr⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  exact no_run_of_serial _ _ _ (fun _ => ⟨(), trivial⟩) _ q hr

def branchSig : Signature := ⟨Bool, Unit⟩
def branch : Model branchSig where
  World := Option Bool
  step _ w v := w = none ∧ ∃ b, v = some b
  valuation b := {w | w = some b}
  point := none

theorem branch_each (b : Bool) : Sat branch (formula (single .top (.pos b)) ()) := by
  apply (formula_iff_run _ _ _ emptyEnv _).mpr
  refine ⟨0, trivial, RunFrom.step (r := 0) trivial ⟨rfl, b, rfl⟩ (.terminal rfl ?_)⟩
  intro v hv
  cases hv.1

/-- Different terminal branches cannot be combined into one accepting path. -/
theorem branch_no_combined_witness :
    ¬ Sat branch (formula (single .top (.conj (.pos false) (.pos true))) ()) := by
  intro h
  obtain ⟨q, _, hr⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  obtain ⟨v, r, ht, _⟩ := run_has_terminal _ _ _ hr
  have hbad : (some false : Option Bool) = some true := ht.1.symm.trans ht.2
  cases hbad

def emptyAutomaton : Symbolic Unit 0 where
  initial := ∅
  guard q := q.elim0
  terminal q := q.elim0

theorem zero_states_rejected : ¬ Sat singleton (formula emptyAutomaton ()) := by
  intro h
  obtain ⟨q, _, _⟩ := (formula_iff_run _ _ _ emptyEnv _).mp h
  exact q.elim0

end Silmaril.Logic.Temporal.FiniteAutomaton.Examples
