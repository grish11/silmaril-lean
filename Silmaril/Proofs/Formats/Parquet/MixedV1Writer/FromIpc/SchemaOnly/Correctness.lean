module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly

open Silmaril.Formats.Parquet
open MixedV1Writer.FromIpc (field physicalOrder)
open MixedV1Writer.FromIpc.SchemaOnly
open Silmaril.Formats.Relational.NamedTable

theorem emit_checked {limits : MixedV1Writer.Multi.Limits} {descriptor : MixedIpc.Descriptor}
    {output : MixedV1Writer.Multi.Encoded} (written : emit limits descriptor = .ok output) :
    output.groups = [] ∧ output.footer.start = 4 ∧
    Footer.readFooter limits.writer.footer output.bytes = .ok (output.footer, metadata descriptor) ∧
    ∃ checked : Int32ByteArrayGroup.Checked (field descriptor.integer) (field descriptor.binary),
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes
        (field descriptor.integer) (field descriptor.binary) = .ok checked ∧
      checked.snapshot.groupCount = 0 := by
  cases assembled : MixedV1Writer.Multi.assembleOrdered (physicalOrder descriptor) limits (plan descriptor) with
  | error cause => simp [emit, assembled, Bind.bind, Except.bind] at written
  | ok candidate =>
    by_cases exactFile : candidate.CheckedOrdered (physicalOrder descriptor) limits (plan descriptor)
    · cases certified : MixedV1Writer.Multi.certify limits (plan descriptor) candidate with
      | error cause => simp [emit, assembled, exactFile, certified, Bind.bind, Except.bind, Except.map] at written
      | ok result =>
        simp [emit, assembled, exactFile, certified, Bind.bind, Except.bind, Except.map] at written
        subst output
        obtain ⟨_, _, dimensions, extent, footer, _⟩ := exactFile
        have empty : candidate.groups = [] := by simpa [plan] using dimensions
        rw [empty] at extent footer
        refine ⟨empty, extent.symm, footer, ?_⟩
        unfold MixedV1Writer.Multi.certify at certified
        cases opened : Int32ByteArrayGroup.openFile limits.writer.readback candidate.bytes
            (field descriptor.integer) (field descriptor.binary) with
        | error cause => simp [plan, opened, Except.mapError, Bind.bind, Except.bind] at certified
        | ok checked =>
          by_cases groupCount : checked.snapshot.groupCount = 0
          · exact ⟨checked, rfl, groupCount⟩
          · simp [plan, opened, groupCount, Except.mapError, Bind.bind, Except.bind] at certified
    · simp [emit, assembled, exactFile, Bind.bind, Except.bind] at written

theorem convert_checked {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {input : KBytes} {output : MixedV1Writer.Multi.Encoded}
    (written : convert source sink input = .ok output) :
    ∃ descriptor, MixedIpc.read source input = .ok ⟨descriptor, []⟩ ∧
      emit sink descriptor = .ok output := by
  cases read : MixedIpc.read source input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok observed =>
    rcases observed with ⟨descriptor, batches⟩
    cases batches with
    | nil =>
      cases emitted : emit sink descriptor with
      | error cause => simp [convert, read, emitted, Except.mapError, Bind.bind, Except.bind] at written
      | ok candidate =>
        simp [convert, read, emitted, Except.mapError, Bind.bind, Except.bind] at written
        exact ⟨descriptor, rfl, written ▸ emitted⟩
    | cons batch tail => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written

theorem convert_batchCount {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {input : KBytes} {observed : MixedIpc.Prepared}
    (read : MixedIpc.read source input = .ok observed) (nonempty : observed.batches ≠ []) :
    convert source sink input = .error (.batchCount observed.batches.length) := by
  cases batches : observed.batches with
  | nil => exact (nonempty batches).elim
  | cons batch tail => simp [convert, read, batches, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly
