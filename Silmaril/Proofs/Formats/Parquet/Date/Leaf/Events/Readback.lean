module

public import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.DateStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Events

open Silmaril.Formats Parquet Date.Leaf Date.Leaf.Events
open Silmaril.Relational

private theorem denote_prefix {limits : Date.Limits} {bound : Bound} {indices : List Nat}
    {groups : List Slots} (decoded : indices.mapM (readGroup limits bound) = .ok groups)
    (rest : List Nat) :
    Reader.denoteGroups (rowsAt limits bound) (indices ++ rest) =
      let tail := Reader.denoteGroups (rowsAt limits bound) rest
      (groups.map (rows bound) ++ tail.1, tail.2) := by
  induction indices generalizing groups with
  | nil =>
    simp [Pure.pure, Except.pure] at decoded
    subst groups
    rfl
  | cons index indices ih =>
    cases first : readGroup limits bound index with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at decoded
    | ok slots =>
      cases more : indices.mapM (readGroup limits bound) with
      | error cause => simp [List.mapM_cons, first, more, Bind.bind, Except.bind] at decoded
      | ok tail =>
        have same : slots :: tail = groups := by
          simpa [List.mapM_cons, first, more, Bind.bind, Except.bind, Pure.pure, Except.pure] using decoded
        subst groups
        simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, ih more]

private theorem mapM_of_eof (limits : Date.Limits) (bound : Bound) (indices : List Nat)
    (eof : (Reader.denoteGroups (rowsAt limits bound) indices).2 = .eos) :
    ∃ groups, indices.mapM (readGroup limits bound) = .ok groups := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index indices ih =>
    cases first : readGroup limits bound index with
    | error cause =>
      simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] at eof
    | ok slots =>
      have following : (Reader.denoteGroups (rowsAt limits bound) indices).2 = .eos := by
        simpa [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] using eof
      obtain ⟨groups, tail⟩ := ih following
      exact ⟨slots :: groups, by simp [List.mapM_cons, first, tail, Bind.bind, Except.bind,
        Pure.pure, Except.pure]⟩

theorem readAll_reference {limits : Date.Limits} {ordinal : Nat} {input : Bytes} {bound : Bound}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound) :
    readAll limits ordinal input = .ok ⟨schema bound, trace limits bound⟩ := by
  unfold readAll
  have ready : openSource limits ordinal input = .ok ⟨schema bound, source limits bound⟩ := by
    simp [openSource, opened, Except.mapError, Except.map]
  rw [ready, Reader.readAll_opened]
  rfl

theorem trace_firstError {limits : Date.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    trace limits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩ := by
  simp [trace, split, denote_prefix earlier, Reader.denoteGroups, rowsAt, failed,
    Except.map, Except.mapError, List.map_map]

theorem toIpc_firstError {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc limits output ordinal input = .error (.source (.groupFailure index cause)) := by
  simp [toIpc, opened, emit, trace_firstError split earlier failed, Except.mapError,
    Bind.bind, Except.bind]

theorem toIpc_readback {limits : Date.Limits} {output : Arrow.ObservationLimits} {ordinal : Nat}
    {input : Bytes} {wire : KBytes} (written : toIpc limits output ordinal input = .ok wire) :
    ∃ bound groups, openLeaf limits.snapshot input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      readAll limits ordinal input = .ok ⟨schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩⟩ ∧
      Arrow.DateStream.read output.ipc wire =
        .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) := by
  cases opened : openLeaf limits.snapshot input ordinal with
  | error cause => simp [toIpc, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    cases ended : (trace limits bound).termination with
    | closed => simp [toIpc, opened, emit, ended, Except.mapError, Bind.bind, Except.bind] at written
    | closeError cause =>
      simp [toIpc, opened, emit, ended, Except.mapError, Bind.bind, Except.bind] at written
    | readError cause =>
      simp [toIpc, opened, emit, ended, Except.mapError, Bind.bind, Except.bind] at written
    | eos =>
      obtain ⟨groups, decoded⟩ := mapM_of_eof limits bound _ ended
      have ordered := denote_prefix decoded []
      rw [List.append_nil] at ordered
      have sameTrace : trace limits bound =
          ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩ := by
        simp [trace, ordered, Reader.denoteGroups, List.map_map]
      refine ⟨bound, groups, rfl, decoded, (readAll_reference opened).trans ?_, ?_⟩
      · rw [sameTrace]
      · let batches := (trace limits bound).batches.map fun batch => batch.values ⟨0, Nat.zero_lt_succ 0⟩
        have exactRows : batches = groups := by
          simp [batches, sameTrace, rows, AlignedColumns.ofRows, Function.comp_def, List.map_map]
        have emitted : Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable batches =
            .ok wire := by
          have mapped : (Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable
              batches).mapError IpcError.writer = .ok wire := by
            simpa [toIpc, opened, emit, ended, batches, Except.mapError, Bind.bind, Except.bind]
              using written
          cases wrote : Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable batches with
          | error cause => simp [wrote, Except.mapError] at mapped
          | ok wire' => simpa [wrote, Except.mapError] using mapped
        rw [exactRows] at emitted
        exact Arrow.DateStream.Writer.emit_readback emitted

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Events
