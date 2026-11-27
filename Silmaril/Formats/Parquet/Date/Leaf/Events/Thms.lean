module

public import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Events.Readback

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Events

open Silmaril.Relational

/-- The event source enumerates original footer indices and retains successful
batches before the first typed group failure. -/
theorem readAll_reference {limits : Date.Limits} {ordinal : Nat} {input : Bytes} {bound : Bound}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound) :
    readAll limits ordinal input = .ok ⟨schema bound, trace limits bound⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Events.readAll_reference opened

/-- A late failure retains exactly the preceding complete groups and reports the
original footer index and cause. -/
theorem readAll_firstError {limits : Date.Limits} {ordinal : Nat} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll limits ordinal input = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  rw [readAll_reference opened, Proofs.Formats.Parquet.Date.Leaf.Events.trace_firstError split earlier failed]

/-- The first selected group failure precedes native IPC writer checks. -/
theorem toIpc_firstError {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc limits output ordinal input = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Events.toIpc_firstError opened split earlier failed

/-- Native readback preserves the selected leaf descriptor and every complete group in order. -/
theorem toIpc_readback {limits : Date.Limits} {output : Arrow.ObservationLimits} {ordinal : Nat}
    {input : Bytes} {wire : KBytes} (written : toIpc limits output ordinal input = .ok wire) :
    ∃ bound groups, openLeaf limits.snapshot input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      readAll limits ordinal input = .ok ⟨schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩⟩ ∧
      Arrow.DateStream.read output.ipc wire =
        .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) :=
  Proofs.Formats.Parquet.Date.Leaf.Events.toIpc_readback written

/-- Original open failures are returned before any groups or writer checks. -/
theorem toIpc_openError {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {input : Bytes} {cause : Date.Leaf.Error}
    (failed : openLeaf limits.snapshot input ordinal = .error cause) :
    toIpc limits output ordinal input = .error (.source (.openFailure cause)) := by
  simp [toIpc, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Events
