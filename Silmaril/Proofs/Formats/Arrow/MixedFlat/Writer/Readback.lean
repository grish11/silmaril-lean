module

public import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Arrow.MixedFlat.Writer

theorem emit_checked {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    serialize limits input = .ok output ∧
      MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
        input.fields output.metadataBytes = .ok output.metadata ∧
      ∃ values, MixedFlat.readParsed limits input.fields output.metadata output.body = .ok values ∧
        values.rowCount = input.rowCount ∧ observeColumns values.columns = some input.observe := by
  cases serialized : serialize limits input with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases metadataRead : MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers
        limits.totalDataBuffers input.fields actual.metadataBytes with
    | error =>
      simp [emit, serialized, metadataRead, Bind.bind, Except.bind, Except.mapError] at written
    | ok metadata =>
      by_cases same : metadata = actual.metadata
      · subst metadata
        cases valuesRead : MixedFlat.readParsed limits input.fields actual.metadata actual.body with
        | error =>
          simp [emit, serialized, metadataRead, valuesRead, Bind.bind, Except.bind,
            Except.mapError] at written
        | ok values =>
          by_cases agrees : values.rowCount = input.rowCount ∧
              observeColumns values.columns = some input.observe
          · have sameOutput : actual = output := by
              simpa [emit, serialized, metadataRead, valuesRead, agrees, Bind.bind, Except.bind,
                Except.mapError, Pure.pure, Except.pure] using written
            subst output
            exact ⟨rfl, metadataRead, values, valuesRead, agrees⟩
          · simp [emit, serialized, metadataRead, valuesRead, agrees, Bind.bind, Except.bind,
              Except.mapError] at written
      · simp [emit, serialized, metadataRead, same, Bind.bind, Except.bind, Except.mapError] at written

theorem emit_readback {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
      input.fields output.metadataBytes = .ok output.metadata ∧
    ∃ values, MixedFlat.readParsed limits input.fields output.metadata output.body = .ok values ∧
      values.rowCount = input.rowCount ∧ observeColumns values.columns = some input.observe :=
  (emit_checked written).2

theorem emit_assignment {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    ∃ plan, MixedFlat.bindBatch limits input.fields output.metadata output.body = .ok plan ∧
      plan.assignment.groups.map Group.field = input.fields ∧
      plan.assignment.groups.map Group.node = output.metadata.batch.nodes ∧
      plan.assignment.groups.filterMap Group.count = output.metadata.counts ∧
      plan.assignment.groups.flatMap Group.buffers = output.metadata.batch.buffers := by
  obtain ⟨values, read, _⟩ := (emit_readback written).2
  cases bound : MixedFlat.bindBatch limits input.fields output.metadata output.body with
  | error => simp [MixedFlat.readParsed, bound, Bind.bind, Except.bind] at read
  | ok plan => exact ⟨plan, rfl, plan.assignment.fieldsExact, plan.assignment.nodesExact,
      plan.assignment.countsExact, plan.assignment.buffersExact⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer
