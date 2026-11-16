module

public import Silmaril.Logic.Temporal.LTL.Thms

@[expose] public section

namespace Silmaril.Logic.Temporal.LTL.Examples

inductive Atom where
  | done | running

def done : Formula Atom := .atom .done
def running : Formula Atom := .atom .running

/-- A trace reaches its completed state at time two and stays there. -/
def completes : Model Atom := ULift.up fun n a =>
  match a with
  | .done => 2 ≤ n
  | .running => n < 2

/-- A trace that runs forever. -/
def loops : Model Atom := ULift.up fun _ a =>
  match a with
  | .done => False
  | .running => True

theorem completes_strong_until : Sat completes (.until running done) := by
  refine ⟨2, ?_, ?_⟩
  · change 2 ≤ 0 + 2
    decide
  · intro i hi
    change 0 + i < 2
    simpa only [Nat.zero_add] using hi

theorem completes_eventually_done : Sat completes (Formula.eventually done) :=
  Formula.until_eventually completes running done 0 completes_strong_until

theorem completes_not_done_initially : ¬ Sat completes done := by
  change ¬ 2 ≤ 0
  decide

theorem completes_not_next_done : ¬ Sat completes (.next done) := by
  change ¬ 2 ≤ 1
  decide

theorem completes_next_next_done : Sat completes (.next (.next done)) := by
  change 2 ≤ 2
  decide

theorem completes_stays_done : (Formula.always done).Holds completes 2 := by
  apply (Formula.always_iff completes done 2).mpr
  intro d
  exact Nat.le_add_right 2 d

theorem loops_always_running : Sat loops (Formula.always running) := by
  apply (Formula.always_iff loops running 0).mpr
  intro d
  trivial

theorem loops_not_eventually_done : ¬ Sat loops (Formula.eventually done) := by
  intro h
  obtain ⟨d, hd⟩ := (Formula.eventually_iff loops done 0).mp h
  exact hd

theorem loops_not_strong_until : ¬ Sat loops (.until running done) :=
  fun h => loops_not_eventually_done (Formula.until_eventually loops running done 0 h)

theorem loops_weak_until : Sat loops (Formula.weakUntil running done) :=
  Or.inr loops_always_running

/-- info: 'Silmaril.Logic.Temporal.LTL.Examples.completes_eventually_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completes_eventually_done
/-- info: 'Silmaril.Logic.Temporal.LTL.Examples.loops_not_eventually_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loops_not_eventually_done

end Silmaril.Logic.Temporal.LTL.Examples
