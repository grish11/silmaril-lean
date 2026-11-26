module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

theorem run_eq_some_iff_returnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Heap cells) (word : Word) (final : Heap cells) :
    run graph input budget ⟨initial⟩ = some (word, Buffer.mk final) ↔
      ∃ count ≤ budget, graph.ReturnsAfter input initial count word final := by
  rw [run_eq_some_iff]
  simp only [← returnsAfter_iff_runAfter]

private theorem cfg_run_at_budget (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Heap cells) (word : Word) (final : Heap cells) :
    (lower cells graph).run (evalBody input) (budget + 3) .nil ⟨initial⟩ =
        (some (.cons word .nil), Buffer.mk final) ↔
      run graph input budget ⟨initial⟩ = some (word, Buffer.mk final) := by
  unfold run
  cases (lower cells graph).run (evalBody input) (budget + 3) .nil ⟨initial⟩ with
  | mk result buffer =>
    cases result with
    | none => constructor <;> intro same <;> cases same
    | some values =>
      cases values with
      | cons value rest =>
        cases rest
        change (some (Env.cons (w := wordWidth) value .nil), buffer) =
            (some (Env.cons (w := wordWidth) word .nil), Buffer.mk final) ↔
          some (value, buffer) = some (word, Buffer.mk final)
        constructor
        · rintro ⟨⟩
          rfl
        · intro same
          cases Option.some.inj same
          rfl

private theorem cfg_run_short (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) (short : fuel < 3) :
    ((lower cells graph).run (evalBody input) fuel .nil initial).1 = none := by
  have choices : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · rfl
  · rfl
  · let stepped := Block.eval (evalBody input) ((lower cells graph).block Label.header) .nil initial
    change (let (outcome, _) := stepped
      match outcome with
      | .inl _ => none
      | .inr returned => some returned) = none
    rw [show stepped = _ from header_transition graph input initial]
    cases observeActivation graph input initial <;> rfl

theorem cfg_run_eq_some_iff_returnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Heap cells) (word : Word) (final : Heap cells) :
    (lower cells graph).run (evalBody input) fuel .nil ⟨initial⟩ =
        (some (.cons word .nil), Buffer.mk final) ↔
      ∃ count, count + 3 ≤ fuel ∧ graph.ReturnsAfter input initial count word final := by
  by_cases enough : 3 ≤ fuel
  · obtain ⟨budget, rfl⟩ : ∃ budget : Nat, fuel = budget + 3 := ⟨fuel - 3, by omega⟩
    rw [cfg_run_at_budget, run_eq_some_iff_returnsAfter]
    simp only [Nat.add_le_add_iff_right]
  · have absent := cfg_run_short graph input fuel ⟨initial⟩ (by omega)
    constructor
    · intro returned
      rw [returned] at absent
      cases absent
    · rintro ⟨count, bounded, _⟩
      omega

theorem run_eq_none_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Heap cells) :
    run graph input budget ⟨initial⟩ = none ↔
      ∀ count ≤ budget, graph.evalAfter input initial count = none := by
  constructor
  · intro absent count bounded
    cases evaluated : graph.evalAfter input initial count with
    | none => rfl
    | some result =>
      obtain ⟨word, final⟩ := result
      have native := (graph.returnsAfter_iff_evalAfter input initial count word final).mpr evaluated
      have observed := (run_eq_some_iff_returnsAfter graph input budget initial word final).mpr
        ⟨count, bounded, native⟩
      rw [absent] at observed
      cases observed
  · intro exhausted
    cases evaluated : run graph input budget ⟨initial⟩ with
    | none => rfl
    | some result =>
      obtain ⟨word, ⟨final⟩⟩ := result
      obtain ⟨count, bounded, returned⟩ :=
        (run_eq_some_iff_returnsAfter graph input budget initial word final).mp evaluated
      have native := (graph.returnsAfter_iff_evalAfter input initial count word final).mp returned
      rw [exhausted count bounded] at native
      cases native

theorem exists_run_eq_some_iff_mem_denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    (∃ budget, run graph input budget ⟨initial⟩ = some (word, Buffer.mk final)) ↔
      (word, final) ∈ graph.denote input initial := by
  rw [← graph.returns_iff_mem_denote, Graph.Returns]
  constructor
  · rintro ⟨budget, returned⟩
    obtain ⟨count, _, native⟩ :=
      (run_eq_some_iff_returnsAfter graph input budget initial word final).mp returned
    exact ⟨count, native⟩
  · rintro ⟨count, native⟩
    exact ⟨count, (run_eq_some_iff_returnsAfter graph input count initial word final).mpr
      ⟨count, Nat.le_refl _, native⟩⟩

theorem forall_run_eq_none_iff_denote_eq_none (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) :
    (∀ budget, run graph input budget ⟨initial⟩ = none) ↔ graph.denote input initial = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · rintro exhausted ⟨word, final⟩ member
    obtain ⟨budget, observed⟩ := (exists_run_eq_some_iff_mem_denote graph input initial word final).mpr member
    rw [exhausted budget] at observed
    cases observed
  · intro absent budget
    cases evaluated : run graph input budget ⟨initial⟩ with
    | none => rfl
    | some result =>
      obtain ⟨word, ⟨final⟩⟩ := result
      exact (absent (word, final)
        ((exists_run_eq_some_iff_mem_denote graph input initial word final).mp ⟨budget, evaluated⟩)).elim

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Proofs
