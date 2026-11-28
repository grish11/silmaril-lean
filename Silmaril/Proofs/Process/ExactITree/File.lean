module

public import Silmaril.Process.ExactITree.Defs
import Silmaril.Semantics.ExactITree.Thms

public section

namespace Silmaril.Process.ExactITree.File.Proofs

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Exact

private abbrev State := Config profile target ReadPair

private def initial : State := ((sentence.lower lowering).test, 0)

private def afterPread (wrong : Bool) : State :=
  (vis (ABIEvent.read 3 4096) fun r => ret (some (if wrong then 0x41 else 0x42), r.byte),
    if wrong then 1 else 0)

private def result (wrong : Bool) : ReadPair :=
  if wrong then (some 0x41, some 0x42) else (some 0x42, some 0x41)

private def afterRead (wrong : Bool) : State :=
  (ret (result wrong), if wrong then 2 else 1)

private theorem pread_step (wrong : Bool) (batch : List UInt8) (t : State) :
    Step (kernel wrong) contents initial batch t ↔ batch = [] ∧ t = afterPread wrong := by
  cases wrong <;> rcases t with ⟨tree, cursor⟩ <;>
    simp [initial, afterPread, Sentence.lower, sentence, lowering, Step, kernel, complete, contents,
      readAt, readCursor] <;> grind

private theorem read_step (wrong : Bool) (batch : List UInt8) (t : State) :
    Step (kernel wrong) contents (afterPread wrong) batch t ↔ batch = [] ∧ t = afterRead wrong := by
  cases wrong <;> rcases t with ⟨tree, cursor⟩ <;>
    simp [afterPread, afterRead, result, Step, kernel, complete, contents, readAt, readCursor] <;> grind

private theorem pread_not_finished (wrong : Bool) (batch : List UInt8) (last : End profile ReadPair) :
    ¬ Finish (kernel wrong) contents initial batch last := by
  cases wrong <;> simp [initial, Sentence.lower, sentence, lowering, Finish, kernel, complete,
    contents, readAt, readCursor]

private theorem read_not_finished (wrong : Bool) (batch : List UInt8) (last : End profile ReadPair) :
    ¬ Finish (kernel wrong) contents (afterPread wrong) batch last := by
  cases wrong <;> simp [afterPread, Finish, kernel, complete, contents, readAt, readCursor]

private theorem return_no_step (wrong : Bool) (batch : List UInt8) (t : State) :
    ¬ Step (kernel wrong) contents (afterRead wrong) batch t := by
  simp [afterRead, Step]

/-- An obligated, unique and silent reply can be consumed before checking a finite endpoint. -/
private theorem finished_after {P : Profile} {S : Signature} {A : Type} {K : Kernel P S}
    {env : P.Env} {s next : Config P S A} {log : List P.Output} {last : End P A}
    (step : ∀ batch t, Step K env s batch t ↔ batch = [] ∧ t = next)
    (unfinished : ∀ batch last, ¬ Finish K env s batch last) :
    Observes K env s (.finished log last) ↔ Observes K env next (.finished log last) := by
  constructor
  · rintro ⟨word, t, batch, path, done, eq⟩
    cases path with
    | nil => exact (unfinished _ _ done).elim
    | cons first tail =>
      obtain ⟨rfl, rfl⟩ := (step _ _).mp first
      exact ⟨_, _, batch, tail, done, eq⟩
  · rintro ⟨word, t, batch, path, done, eq⟩
    exact ⟨word, t, batch, .cons ((step [] next).mpr ⟨rfl, rfl⟩) path, done, eq⟩

private theorem finished (wrong : Bool) (log : List UInt8) (last : End profile ReadPair) :
    Observes (kernel wrong) contents initial (.finished log last) ↔
      log = [] ∧ last = .returned (result wrong) (if wrong then 2 else 1) := by
  rw [finished_after (pread_step wrong) (pread_not_finished wrong),
    finished_after (read_step wrong) (read_not_finished wrong)]
  constructor
  · rintro ⟨word, t, batch, path, done, eq⟩
    cases path with
    | nil =>
      simp [Finish, afterRead] at done
      simpa [done.1, eq] using done.2
    | cons first _ => exact (return_no_step wrong _ _ first).elim
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], afterRead wrong, [], .nil _, by simp [Finish, afterRead], rfl⟩

private theorem no_infinite (wrong : Bool) (log : Set (List UInt8)) :
    ¬ Observes (kernel wrong) contents initial (.infinite log) := by
  rintro ⟨batches, ⟨states, start, step⟩, _⟩
  have s1 : states 1 = afterPread wrong :=
    ((pread_step wrong _ _).mp (start ▸ step 0)).2
  have s2 : states 2 = afterRead wrong :=
    ((read_step wrong _ _).mp (s1 ▸ step 1)).2
  exact return_no_step wrong _ _ (s2 ▸ step 2)

theorem correct_finished (log : List UInt8) (last : End profile ReadPair) :
    Observes (kernel false) contents ((sentence.lower lowering).test, 0) (.finished log last) ↔
      log = [] ∧ last = .returned (some 0x42, some 0x41) 1 :=
  finished false log last

theorem swapped_finished (log : List UInt8) (last : End profile ReadPair) :
    Observes (kernel true) contents ((sentence.lower lowering).test, 0) (.finished log last) ↔
      log = [] ∧ last = .returned (some 0x41, some 0x42) 2 :=
  finished true log last

theorem correct_target : Satisfies (kernel false) (sentence.lower lowering) := by
  rintro file cursor ⟨rfl, rfl⟩ obs h
  cases obs with
  | «prefix» => trivial
  | finished log last =>
    obtain ⟨_, rfl⟩ := (finished false log last).mp h
    rfl
  | infinite log => exact (no_infinite false log h).elim

theorem swapped_target : ¬ Satisfies (kernel true) (sentence.lower lowering) := by
  intro h
  have bad := h contents 0 ⟨rfl, rfl⟩ (.finished [] (.returned (result true) 2))
    ((finished true _ _).mpr ⟨rfl, rfl⟩)
  exact (by decide : result true ≠ (some 0x42, some 0x41)) bad

end Silmaril.Process.ExactITree.File.Proofs
