module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Proofs

open RVSDG (Tuple)
open Silmaril.Elgot.Part (Runs mem_run_iff)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}

theorem runAfter_eq_evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (count : Nat) (initial : Buffer cells) :
    runAfter graph input count initial = (graph.evalAfter input initial.cell count).map
      (fun result => (result.1, Buffer.mk result.2)) := by
  unfold Graph.evalAfter
  induction count generalizing initial with
  | zero =>
    simp only [runAfter, observeActivation_eq_step, Graph.evalFrom]
    cases graph.step input initial.cell <;> rfl
  | succ count ih =>
    simp only [runAfter, observeActivation_eq_step, Graph.evalFrom]
    cases graph.step input initial.cell with
    | inl _ => rfl
    | inr next => exact ih (Buffer.mk next)

theorem returnsAfter_iff_runAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (count : Nat) (initial : Buffer cells) (word : Word) (final : Buffer cells) :
    graph.ReturnsAfter input initial.cell count word final.cell ↔
      runAfter graph input count initial = some (word, final) := by
  rw [graph.returnsAfter_iff_evalAfter, runAfter_eq_evalAfter]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    simpa using congrArg (Option.map fun result => (result.1, result.2.cell)) h

theorem mem_observe_iff_exists_runAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) (result : Word × Buffer cells) :
    result ∈ observe graph input initial ↔
      ∃ count, runAfter graph input count initial = some result := by
  rw [observe, mem_run_iff]
  constructor
  · intro run
    induction run with
    | @done buffer _ exits =>
      have step := (Part.mem_some_iff.mp exits).symm
      exact ⟨0, by simp [runAfter, step]⟩
    | @more buffer next _ backedge _ ih =>
      have step := (Part.mem_some_iff.mp backedge).symm
      obtain ⟨count, evaluated⟩ := ih
      exact ⟨count + 1, by simp [runAfter, step, evaluated]⟩
  · rintro ⟨count, evaluated⟩
    induction count generalizing initial with
    | zero =>
      cases step : observeActivation graph input initial with
      | inl observed =>
        have eq : observed = result := by simpa [runAfter, step] using evaluated
        exact .done (Part.mem_some_iff.mpr (step.trans (congrArg Sum.inl eq)).symm)
      | inr _ => simp [runAfter, step] at evaluated
    | succ count ih =>
      cases step : observeActivation graph input initial with
      | inl _ => simp [runAfter, step] at evaluated
      | inr next =>
        exact .more (Part.mem_some_iff.mpr step.symm) (ih next (by
          simpa [runAfter, step] using evaluated))

theorem observe_eq_none_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) :
    observe graph input initial = Part.none ↔
      ∀ count, runAfter graph input count initial = none := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent count
    cases evaluated : runAfter graph input count initial with
    | none => rfl
    | some result =>
      exact (absent result
        ((mem_observe_iff_exists_runAfter graph input initial result).mpr ⟨count, evaluated⟩)).elim
  · intro exhausted result member
    obtain ⟨count, evaluated⟩ := (mem_observe_iff_exists_runAfter graph input initial result).mp member
    rw [exhausted count] at evaluated
    contradiction

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Proofs
