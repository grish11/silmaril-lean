module

public import Silmaril.Logic.ModalMu.Reachability.Thms
public import Silmaril.Logic.ModalMu.K.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu.Examples

def signature : Signature := ⟨Unit, Unit⟩

/-- Entry reaches a labelled exit in one step, then deadlocks. -/
def chain : Model signature where
  World := Bool
  step _ w v := w = false ∧ v = true
  valuation _ := {w | w = true}
  point := false

theorem chain_reaches : Sat chain (reach () ()) := by
  apply (reach_iff chain () () false).mpr
  exact .next ⟨rfl, rfl⟩ (.here rfl)

theorem exit_deadlocks : true ∉ (forever ()).denote chain emptyEnv := by
  apply not_forever_of_deadlock
  intro v hv
  exact Bool.noConfusion hv.1

theorem entry_not_forever : ¬ Sat chain (forever ()) := by
  intro h
  change false ∈ (Formula.nu (.diamond () (.var 0))).denote chain emptyEnv at h
  rw [Formula.nu_unfold] at h
  obtain ⟨v, hv, hforever⟩ := h
  rw [hv.2] at hforever
  exact exit_deadlocks hforever

/-- A genuine two-state cycle; each state has a different successor. -/
def cycle : Model signature where
  World := Bool
  step _ w v := v = !w
  valuation _ := ∅
  point := false

theorem cycle_forever : Sat cycle (forever ()) := by
  apply forever_of_postfixed cycle () Set.univ
  · intro w _
    exact ⟨!w, rfl, Set.mem_univ _⟩
  · exact Set.mem_univ _

theorem cycle_never_reaches : ¬ Sat cycle (reach () ()) := by
  intro h
  have hr := (reach_iff cycle () () false).mp h
  have no : ∀ w, ¬ FiniteReach (cycle.step ()) (cycle.valuation ()) w := by
    intro w hpath
    induction hpath with
    | here h => exact h
    | next _ _ ih => exact ih
  exact no false hr

/-- Deadlocked entry has neither a finite route to the distinct target nor ν◇. -/
def dead : Model signature where
  World := Bool
  step _ _ _ := False
  valuation _ := {w | w = true}
  point := false

theorem dead_not_reach : ¬ Sat dead (reach () ()) := by
  intro h
  have hr := (reach_iff dead () () false).mp h
  cases hr with
  | here h => exact Bool.noConfusion h
  | next h _ => exact h

theorem dead_not_forever : ¬ Sat dead (forever ()) :=
  not_forever_of_deadlock dead () false (fun _ h => h)

/-- info: 'Silmaril.Logic.ModalMu.Formula.denote_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Formula.denote_dual
/-- info: 'Silmaril.Logic.ModalMu.reach_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reach_iff
/-- info: 'Silmaril.Logic.ModalMu.kToMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kToMu

end Silmaril.Logic.ModalMu.Examples
