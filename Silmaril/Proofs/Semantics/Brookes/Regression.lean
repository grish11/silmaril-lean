module

import Silmaril.Semantics.Brookes.Thms

namespace Silmaril.Semantics.Brookes

private def step (before after : Nat) : Command Nat :=
  Behavior.atomic fun s t _ => s = before ∧ t = after

private theorem accepts_step (s t : Nat) : (step s t).accepts [(s, t)] () :=
  Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩

-- A matching boundary mumbles, including across a sequential join.
example : (Command.seq (step 0 1) (step 1 2)).completes 0 2 () :=
  Behavior.bind_accepts_iff.mpr
    ⟨[(0, 1)], [(1, 2)], (), accepts_step 0 1, accepts_step 1 2,
      .tail (.refl _) (Rewrite.mumble [] [] 0 1 2)⟩

-- An unmatched boundary is still admitted by sequential composition.
example : (Command.seq (step 0 1) (step 2 3)).accepts [(0, 1), (2, 3)] () :=
  Behavior.bind_accepts_iff.mpr
    ⟨[(0, 1)], [(2, 3)], (), accepts_step 0 1, accepts_step 2 3, .refl _⟩

private def gapped : Command Nat :=
  Behavior.generate fun trace _ => trace = [(0, 1), (2, 3)]

private theorem no_gap_run {s t : Nat} (h : Runs s [(0, 1), (2, 3)] t) : False := by
  cases h with
  | cons rest => cases rest

-- The two store requirements in the word are real even after saturation.
example : ¬gapped.completes 0 3 () := by
  intro h
  obtain ⟨_, _, eq, run⟩ := Behavior.completes_generate_iff.mp h
  exact no_gap_run (eq ▸ run)

-- A second component can supply the missing store transition between the steps.
example : (Command.parallel gapped (step 1 2)).completes 0 3 () := by
  apply Command.parallel_completes_iff.mpr
  exact ⟨[(0, 1), (2, 3)], [(1, 2)], [(0, 1), (1, 2), (2, 3)],
    Behavior.generate_accepts (by simp) rfl, accepts_step 1 2,
    .left (0, 1) (.right (1, 2) (.left (2, 3) .nil)),
    .cons (.cons (.cons (.nil 3)))⟩

example : ¬(Command.seq gapped (step 1 2)).completes 0 3 () := by
  intro h
  obtain ⟨left, _, _, hLeft, _, hSeq⟩ := Behavior.bind_accepts_iff.mp h
  obtain ⟨_, run, _⟩ := Runs.append_iff.mp (Runs.of_reduces hSeq (.cons (.nil 3)))
  obtain ⟨_, ⟨_, eq⟩, hDeduction⟩ := hLeft
  exact no_gap_run (eq ▸ Runs.of_reduces hDeduction run)

-- Return can insert an identity at an arbitrary store, including a mismatched one.
example : (Behavior.ret (Store := Nat) true).accepts [(0, 0), (1, 1)] true :=
  Behavior.ret_accepts_iff.mpr ⟨0, rfl,
    .tail (.refl _) (Rewrite.stutter [(0, 0)] [] 1)⟩

example : ¬Reduces (Store := Nat) [(0, 0), (1, 1)] [(0, 0)] := by
  intro h
  have run := Runs.of_reduces h (.cons (.nil 0))
  cases run with
  | cons rest => cases rest

example : (Behavior.ret ()).bind (fun _ => gapped) = gapped :=
  Behavior.ret_bind () (fun _ => gapped)

example : gapped.bind Behavior.ret = gapped :=
  Behavior.bind_ret gapped

private def select : Behavior Nat Bool :=
  Behavior.atomic fun s t result => s = 0 ∧ t = 1 ∧ result = true

private def continuation (selected : Bool) : Behavior Nat Nat :=
  Behavior.ret (if selected then 7 else 9)

-- The terminal result determines which continuation contributes traces.
private theorem select_completes : (select.bind continuation).completes 0 1 7 :=
  Behavior.bind_accepts_iff.mpr
    ⟨[(0, 1)], [(1, 1)], true, Behavior.atomic_completes_iff.mpr ⟨rfl, rfl, rfl⟩,
      Behavior.ret_accepts_iff.mpr ⟨1, rfl, .refl _⟩,
      .tail (.refl _) (Rewrite.mumble [] [] 0 1 1)⟩

example : ¬(select.bind continuation).completes 0 1 9 := by
  intro h
  obtain ⟨_, _, _, hSelect, hNext, _⟩ := Behavior.bind_accepts_iff.mp h
  obtain ⟨_, _, ⟨_, _, rfl⟩, _⟩ := Behavior.atomic_accepts_iff.mp hSelect
  obtain ⟨_, hResult, _⟩ := Behavior.ret_accepts_iff.mp hNext
  contradiction

example : (select.bind continuation).forget.completes 0 1 () :=
  ⟨7, select_completes⟩

end Silmaril.Semantics.Brookes
