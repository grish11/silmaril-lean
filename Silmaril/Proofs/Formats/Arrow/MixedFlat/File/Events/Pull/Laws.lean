module

public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Pull

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.File.Events MixedFlat.File.Events.Pull

private theorem step_stops {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {n rows : Nat} {block : FileBlock} {error : MixedFlat.File.Events.Error}
    (failed : readStep limits input fields n rows block = .error error) :
    StopsAt limits input fields n rows block error := by
  unfold readStep at failed
  split at failed
  · rename_i cause strict
    cases failed
    exact .inl ⟨cause, strict, rfl⟩
  · rename_i observed strict
    cases budget : Body.checkBudget limits.observation fields.length (rows + observed.rowCount) with
    | error cause =>
      simp [budget, bind, Except.bind, Except.mapError] at failed
      exact .inr ⟨observed, cause, strict, budget, failed.symm⟩
    | ok _ => simp [budget, bind, Except.bind, Except.mapError, pure, Except.pure] at failed

private theorem pull_drain (limits : MixedFlat.Limits) (input : KBytes)
    (fields : List MixedFlat.Field) (blocks : List FileBlock) (n rows : Nat)
    (acc : List (Batch (schema fields))) :
    let trace := Arrow.Events.BatchReader.read.pull (reader limits) (schema fields)
      (blocks.length + 1) (.at input fields blocks n rows) acc
    match read.drain limits input fields n rows blocks with
    | .ok batches => trace = ⟨acc.reverse ++ batches, .eos⟩
    | .error error =>
      ∃ (completed : List FileBlock) (block : FileBlock) (rest : List FileBlock)
          (observed : List MixedFlat.Observed) (batches : List (Batch (schema fields))),
        blocks = completed ++ block :: rest ∧
        completed.mapM (MixedFlat.File.readRecord limits input fields) = .ok observed ∧
        List.Forall₂ (Agrees (schema fields)) observed batches ∧
        StopsAt limits input fields (n + completed.length)
          (rows + (observed.map MixedFlat.Observed.rowCount).sum) block error ∧
        trace = ⟨acc.reverse ++ batches, .readError error⟩ := by
  induction blocks generalizing n rows acc with
  | nil => simp [read.drain, Arrow.Events.BatchReader.read.pull, reader]
  | cons block rest ih =>
    cases step : readStep limits input fields n rows block with
    | error cause =>
      simp only [read.drain, step, bind, Except.bind]
      refine ⟨[], block, rest, [], [], rfl, rfl, .nil, ?_, ?_⟩
      · simpa using step_stops step
      · simp [Arrow.Events.BatchReader.read.pull, reader, step, Except.map]
    | ok entry =>
      obtain ⟨total, batch⟩ := entry
      have tail := ih (n + 1) total (batch :: acc)
      cases remaining : read.drain limits input fields (n + 1) total rest with
      | ok tailBatches =>
        simp only [read.drain, step, remaining, bind, Except.bind, pure, Except.pure]
        rw [remaining] at tail
        simpa [Arrow.Events.BatchReader.read.pull, reader, step, Except.map, List.reverse_cons,
          List.append_assoc] using tail
      | error cause =>
        simp only [read.drain, step, remaining, bind, Except.bind]
        rw [remaining] at tail
        obtain ⟨completed, failed, remainingBlocks, observed, batches, split, parsed, align, stop, trace⟩ := tail
        obtain ⟨first, strict, count, headAligned⟩ := MixedFlat.File.Events.readStep_exact step
        refine ⟨block :: completed, failed, remainingBlocks, first :: observed, batch :: batches, ?_, ?_,
          .cons headAligned align, ?_, ?_⟩
        · simpa using congrArg (List.cons block) split
        · simp [List.mapM_cons, strict, parsed, bind, Except.bind, pure, Except.pure]
        · simpa [count, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stop
        · simpa [Arrow.Events.BatchReader.read.pull, reader, step, Except.map, List.reverse_cons,
            List.append_assoc] using trace

private theorem readAll_of_open {limits : MixedFlat.Limits} {input : KBytes}
    {index : MixedFlat.File.Index input}
    (opened : MixedFlat.File.readIndex limits.observation.ipc input = .ok index) :
    readAll limits input = .ok ⟨schema index.footer.fields,
      Arrow.Events.BatchReader.read.pull (reader limits) (schema index.footer.fields)
        (index.footer.blocks.length + 1)
        (.at input index.footer.fields index.footer.blocks 0 0) []⟩ := by
  simp [readAll, reader, opened, Except.mapError, Except.map, Cursor.callCount]

theorem readAll_eager {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature} :
    (readAll limits input = .ok source ∧ source.2.termination = .eos) ↔
      MixedFlat.File.Events.read limits input = .ok source := by
  cases opened : MixedFlat.File.readIndex limits.observation.ipc input with
  | error =>
    simp [readAll, reader, MixedFlat.File.Events.read, opened, bind, Except.bind,
      Except.mapError, Except.map]
  | ok index =>
    have checked := pull_drain limits input index.footer.fields index.footer.blocks 0 0 []
    cases remaining : MixedFlat.File.Events.read.drain limits input index.footer.fields 0 0 index.footer.blocks with
    | ok batches =>
      rw [remaining] at checked
      simp only [List.reverse_nil, List.nil_append] at checked
      rw [readAll_of_open opened, checked]
      simp [MixedFlat.File.Events.read, opened, remaining, bind, Except.bind, Except.mapError,
        pure, Except.pure]
      intro same
      cases same
      rfl
    | error cause =>
      rw [remaining] at checked
      obtain ⟨_, _, _, _, batches, _, _, _, _, trace⟩ := checked
      rw [readAll_of_open opened, trace]
      simp [MixedFlat.File.Events.read, opened, remaining, bind, Except.bind, Except.mapError]
      intro same
      cases same
      simp

theorem readAll_failure_exact {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature} {error : MixedFlat.File.Events.Error}
    (read : readAll limits input = .ok source) (failed : source.2.termination = .readError error) :
    ∃ index : MixedFlat.File.Index input,
      MixedFlat.File.readIndex limits.observation.ipc input = .ok index ∧
      source.1 = schema index.footer.fields ∧
      ∃ completed block rest observed,
        index.footer.blocks = completed ++ block :: rest ∧
        completed.mapM (MixedFlat.File.readRecord limits input index.footer.fields) = .ok observed ∧
        List.Forall₂ (Agrees source.1) observed source.2.batches ∧
        StopsAt limits input index.footer.fields completed.length
          (observed.map MixedFlat.Observed.rowCount).sum block error ∧
        MixedFlat.File.Events.read limits input = .error error := by
  cases opened : MixedFlat.File.readIndex limits.observation.ipc input with
  | error =>
    simp [readAll, reader, opened, Except.mapError, Except.map] at read
  | ok index =>
    have checked := pull_drain limits input index.footer.fields index.footer.blocks 0 0 []
    cases remaining : MixedFlat.File.Events.read.drain limits input index.footer.fields 0 0 index.footer.blocks with
    | ok batches =>
      rw [remaining] at checked
      simp only [List.reverse_nil, List.nil_append] at checked
      rw [readAll_of_open opened, checked] at read
      cases read
      contradiction
    | error cause =>
      rw [remaining] at checked
      obtain ⟨completed, block, rest, observed, batches, split, parsed, aligned, stop, trace⟩ := checked
      rw [readAll_of_open opened, trace] at read
      cases read
      simp at failed
      subst error
      refine ⟨index, rfl, rfl, completed, block, rest, observed, split, parsed,
        by simpa using aligned, by simpa using stop, ?_⟩
      simp [MixedFlat.File.Events.read, opened, remaining, bind, Except.bind, Except.mapError]

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Pull
