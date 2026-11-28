module

public import Silmaril.Machine.MulticoreVM.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM

open Silmaril.Machine.MulticoreVM
open Silmaril.Semantics.ConcurrentTrace (Word Equivalent ofWord_eq_iff)

universe u

variable {State Thread Choice Event : Type u}
variable {step : Transition State Thread Choice Event}

private theorem mem_run_zero {initial final : State} {word : Word Thread Event} :
    (final, word) ∈ namedOutcomes (run step 0) initial ↔ final = initial ∧ word = [] := by
  change ((PUnit.unit, final), word) ∈
    ({((PUnit.unit, initial), [])} : Set ((PUnit × State) × Word Thread Event)) ↔ _
  simp

private theorem mem_run_succ (n : Nat) {initial final : State} {word : Word Thread Event} :
    (final, word) ∈ namedOutcomes (run step (n + 1)) initial ↔
      ∃ next head tail, machineStep step initial head next ∧
        (final, tail) ∈ namedOutcomes (run step n) next ∧ word = head ++ tail := by
  change ((⟨⟩, final), word) ∈
    (⋃ p ∈ { p : (PUnit × State) × Word Thread Event | machineStep step initial p.2 p.1.2 },
      (fun q : (PUnit × State) × Word Thread Event => (q.1, p.2 ++ q.2)) ''
        (((run step n).run p.1.2).run).run) ↔ _
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨⟨_, next⟩, head⟩, first, ⟨⟨⟨⟨⟩, last⟩, tail⟩, rest, equality⟩⟩
    cases equality
    exact ⟨next, head, tail, first, rest, rfl⟩
  · rintro ⟨next, head, tail, first, rest, rfl⟩
    exact ⟨((⟨⟩, next), head), first, ((⟨⟩, final), tail), rest, rfl⟩

theorem mem_run_iff_exists_schedule (n : Nat) {initial final : State} {word : Word Thread Event} :
    (final, word) ∈ namedOutcomes (run step n) initial ↔
      ∃ schedule : Schedule Thread Choice, schedule.length = n ∧
        Scheduled step schedule initial word final := by
  induction n generalizing initial word final with
  | zero =>
    rw [mem_run_zero]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], rfl, .nil _⟩
    · rintro ⟨schedule, len, path⟩
      cases List.length_eq_zero_iff.mp len
      cases path
      exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [mem_run_succ]
    constructor
    · rintro ⟨next, _, tail, ⟨thread, choice, fragment, first, rfl⟩, rest, rfl⟩
      obtain ⟨schedule, len, path⟩ := ih.mp rest
      exact ⟨⟨thread, choice⟩ :: schedule, congrArg Nat.succ len, .cons first path⟩
    · rintro ⟨schedule, len, path⟩
      cases path with
      | nil => simp at len
      | cons first rest =>
        exact ⟨_, _, _, ⟨_, _, _, first, rfl⟩, ih.mpr ⟨_, Nat.succ.inj len, rest⟩, rfl⟩

theorem run_eq_iUnion_scheduled (n : Nat) (initial : State) :
    namedOutcomes (run step n) initial =
      ⋃ schedule : {s : Schedule Thread Choice // s.length = n},
        scheduledOutcomes step schedule.val initial := by
  ext ⟨final, word⟩
  rw [Set.mem_iUnion, mem_run_iff_exists_schedule]
  exact ⟨fun ⟨s, h, path⟩ => ⟨⟨s, h⟩, path⟩, fun ⟨s, path⟩ => ⟨s.val, s.property, path⟩⟩

theorem mem_quotient_iff (n : Nat) (initial final : State)
    (word : Word Thread Event) :
    observeQuotient (final, word) ∈ observeQuotient '' namedOutcomes (run step n) initial ↔
      ∃ schedule : Schedule Thread Choice, schedule.length = n ∧
        ∃ actual, Scheduled step schedule initial actual final ∧ Equivalent actual word := by
  constructor
  · rintro ⟨⟨target, actual⟩, member, equality⟩
    have sameState : target = final := congrArg Prod.fst equality
    subst target
    obtain ⟨schedule, len, path⟩ := (mem_run_iff_exists_schedule n).mp member
    exact ⟨schedule, len, actual, path, (ofWord_eq_iff _ _).mp (congrArg Prod.snd equality)⟩
  · rintro ⟨schedule, len, actual, path, equivalent⟩
    exact ⟨(final, actual), (mem_run_iff_exists_schedule n).mpr ⟨schedule, len, path⟩,
      Prod.ext rfl ((ofWord_eq_iff _ _).mpr equivalent)⟩

theorem machineRuns_iff_exists_schedule {initial final : State} {word : Word Thread Event} :
    Silmaril.Machine.Trace.Runs (machineStep step) initial word final ↔
      ∃ schedule, Scheduled step schedule initial word final := by
  constructor
  · intro run
    induction run with
    | refl state => exact ⟨[], .nil state⟩
    | cons first _ ih =>
      obtain ⟨thread, choice, fragment, transition, rfl⟩ := first
      obtain ⟨schedule, path⟩ := ih
      exact ⟨⟨thread, choice⟩ :: schedule, .cons transition path⟩
  · rintro ⟨schedule, path⟩
    induction path with
    | nil state => exact .refl state
    | cons first _ ih => exact .cons ⟨_, _, _, first, rfl⟩ ih

theorem execute_iff_scheduled
    (exec : Thread → Choice → State → Option (State × Fragment Thread Event))
    (schedule : Schedule Thread Choice) {initial final : State} {word : Word Thread Event} :
    execute exec schedule initial = some (final, word) ↔
      Scheduled (ofExecutor exec) schedule initial word final := by
  induction schedule generalizing initial final word with
  | nil =>
    constructor
    · intro h
      cases Option.some.inj h
      exact .nil _
    · intro h
      cases h
      rfl
  | cons decision schedule ih =>
    constructor
    · intro h
      cases first : exec decision.thread decision.choice initial with
      | none => simp [execute, first] at h
      | some result =>
        obtain ⟨next, fragment⟩ := result
        cases rest : execute exec schedule next with
        | none => simp [execute, first, rest] at h
        | some outcome =>
          obtain ⟨last, tail⟩ := outcome
          have equality : (last, nameFragment decision.thread fragment ++ tail) = (final, word) := by
            simpa [execute, first, rest] using h
          cases equality
          exact .cons first (ih.mp rest)
    · intro path
      cases path with
      | cons first rest =>
        rw [ofExecutor] at first
        simp [execute, first, ih.mpr rest]

end Silmaril.Proofs.Machine.MulticoreVM
