module

public import Silmaril.Semantics.Accept.IO.Thms
public import Silmaril.Semantics.Accept.Rel.Thms

/-! # Relational I/O acceptance: worked examples and regression tests

Small traces over natural numbers, checked by `decide` when the library builds:

* a nested (reentrant) call whose output is not attributed to the outer scope;
* outputs before the first input of a scope, and after its exit, trigger nothing;
* a trapped run: its outputs are triggered, but it has no episode, so `triggers` is not the
  projection of `retTriggers` (`image_retTriggers_eq` needs every run to return);
* two interleaved scopes with explicit call IDs: temporal order across scopes relates nothing,
  and the interleaving has the same runs as the sequential trace;
* several inputs in one scope (one window each) and the entry reading (`returns`);
* the successful-value projection of a `result`-valued return (WIT `result` as `Sum`).
-/

@[expose] public section

namespace Silmaril.Accept.IOExamples

open Silmaril.Accept Silmaril.Accept.IO
open scoped Silmaril.Accept

/-- Tags with unit entries and natural inputs, outputs and results. -/
abbrev T := Tag Unit ℕ ℕ ℕ

/-- An export call reads input `1`, makes a reentrant call that outputs `9`, outputs `2` and
`3` and returns `7`; a second call reads `4`, outputs `5` and traps. -/
def nested : List T :=
  [.enter (some ()), .inp 1, .enter none, .out 9, .exit none, .out 2, .out 3, .exit (some 7),
   .enter (some ()), .inp 4, .out 5, .exit none]

/-- The nested call's output `9` belongs to its own scope. -/
example : inputRuns (bracket nested) = [⟨1, [2, 3], some 7⟩, ⟨4, [5], none⟩] := by decide

/-- The entry reading: the observed export calls; the nested one is unobserved. -/
example : entryRuns (bracket nested) = [⟨(), [2, 3], some 7⟩, ⟨(), [5], none⟩] := by decide

/-- The runs of the one-trace model. -/
abbrev S := inputRunsOf {bracket nested}

theorem mem_S {r : Run ℕ ℕ ℕ} (h : r ∈ inputRuns (bracket nested)) : r ∈ S := ⟨_, rfl, h⟩

example : (1, 2) ∈ triggers S :=
  mem_triggers_of_run (r := ⟨1, [2, 3], some 7⟩) (mem_S (by decide)) (by decide)
example : (1, ([2, 3], 7)) ∈ episodes S := mem_S (by decide)
example : (1, 3, 7) ∈ retTriggers S := ⟨[2, 3], mem_S (by decide), by decide⟩
example : (1, 7) ∈ returns S := ⟨[2, 3], mem_S (by decide)⟩

/-- The trapped run still triggers `5`... -/
example : (4, 5) ∈ triggers S :=
  mem_triggers_of_run (r := ⟨4, [5], none⟩) (mem_S (by decide)) (by decide)

/-- ...but has no episode, and the nested output `9` is triggered by nothing. -/
theorem not_returns_four (c : ℕ) : (4, c) ∉ returns S := by
  rintro ⟨bs, t, rfl, h⟩
  have : (⟨4, bs, some c⟩ : Run ℕ ℕ ℕ) ∈ inputRuns (bracket nested) := h
  revert this
  simp [inputRuns, scopes, localView, bracket, assign, nested, Ev.at, Ev.scope, Ev.loc,
    windows, collect]

theorem not_triggers_nine (a : ℕ) : (a, 9) ∉ triggers S := by
  rintro ⟨r, ⟨t, rfl, h⟩, -, hb⟩
  rw [show inputRuns (bracket nested) = [⟨1, [2, 3], some 7⟩, ⟨4, [5], none⟩] by decide] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> simp at hb

/-- `triggers` is not the projection of `retTriggers` when a run traps. -/
example : (fun p => (p.1, p.2.1)) '' retTriggers S ≠ triggers S := by
  intro h
  have : ((4 : ℕ), (5 : ℕ)) ∈ (fun p => (p.1, p.2.1)) '' retTriggers S :=
    h ▸ mem_triggers_of_run (r := ⟨4, [5], none⟩) (mem_S (by decide)) (by decide)
  obtain ⟨⟨a, b, c⟩, hm, he⟩ := this
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact not_returns_four c (returns_of_mem_retTriggers hm)

/-- Outputs before the first input and after the exit trigger nothing. -/
example : inputRuns (bracket
    ([.enter none, .out 8, .inp 1, .out 2, .exit (some 0), .out 3] : List T)) =
    [⟨1, [2], some 0⟩] := by decide

/-- Several inputs in one scope: one window each; the result belongs to the last window. -/
example : inputRuns (bracket ([.enter none, .inp 1, .out 2, .inp 3, .out 4, .out 5,
    .exit (some 6)] : List T)) = [⟨1, [2], none⟩, ⟨3, [4, 5], some 6⟩] := by decide

/-! ## Interleaved scopes with explicit call IDs -/

/-- Events with explicit scope IDs. -/
abbrev E := Ev ℕ Unit ℕ ℕ ℕ

/-- Two calls run one after the other. -/
def sequential : List E :=
  [.inp 0 1, .out 0 10, .exit 0 (some 0), .inp 1 2, .out 1 20, .exit 1 (some 0)]

/-- The same calls interleaved: call `1`'s input is read before call `0`'s output. -/
def interleaved : List E :=
  [.inp 0 1, .inp 1 2, .out 0 10, .out 1 20, .exit 1 (some 0), .exit 0 (some 0)]

example : inputRuns interleaved = [⟨1, [10], some 0⟩, ⟨2, [20], some 0⟩] := by decide

/-- Same local views, so the same runs, though the traces differ. -/
example (r : Run ℕ ℕ ℕ) : r ∈ inputRuns interleaved ↔ r ∈ inputRuns sequential :=
  inputRuns_congr (t := interleaved) (t' := sequential) (fun k => by
    match k with
    | 0 | 1 => decide
    | k + 2 => simp [localView, interleaved, sequential, Ev.at, Ev.scope]) r

/-- Input `2` precedes output `10` in the interleaved trace, but does not trigger it. -/
example : ∀ r ∈ inputRuns interleaved, r.input = 2 → (10 : ℕ) ∉ r.outputs := by decide

/-! ## Successful-value projection of a `Result`-like return -/

/-- An export `f(x) -> result<nat>`: `f(1)` returns `ok(5)` (`inl 5`), `f(2)` returns
`error` (`inr ()`). -/
def results : List (Tag ℕ Unit Unit (ℕ ⊕ Unit)) :=
  [.enter (some 1), .exit (some (.inl 5)), .enter (some 2), .exit (some (.inr ()))]

/-- The classic input/return relation of the entry reading, restricted to successful values. -/
abbrev okReturns : ℕ -|> ℕ :=
  SetRel.comp (returns (entryRunsOf {bracket results})) (ofPartial Sum.getLeft?)

example : (1, 5) ∈ okReturns :=
  ⟨.inl 5, ⟨[], ⟨_, rfl, by decide⟩⟩, rfl⟩

example (b : ℕ) : (2, b) ∉ okReturns := by
  rintro ⟨c, ⟨bs, t, rfl, h⟩, hc⟩
  have h' : (⟨2, bs, some c⟩ : Run ℕ Unit (ℕ ⊕ Unit)) ∈ entryRuns (bracket results) := h
  rw [show entryRuns (bracket results) =
    [⟨1, [], some (.inl 5)⟩, ⟨2, [], some (.inr ())⟩] by decide] at h'
  simp only [List.mem_cons, List.not_mem_nil, or_false, Run.mk.injEq] at h'
  rcases h' with ⟨h, -⟩ | ⟨-, -, h⟩
  · cases h
  · cases h
    cases hc

end Silmaril.Accept.IOExamples
