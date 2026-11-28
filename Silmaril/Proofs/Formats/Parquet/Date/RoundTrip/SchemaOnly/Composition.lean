module

public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
public import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Defs
import Silmaril.Formats.Parquet.Date.RoundTrip.Thms
import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.RoundTrip

private theorem ipc_empty {field : Arrow.DateStream.Field} (day : field.unit = .day) :
    (⟨field.name, field.nullable, []⟩ : Observation).ipc = ⟨field, []⟩ := by
  cases field
  cases day
  rfl

theorem zero_group_readback {limits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {wire : Bytes} {ipc : KBytes} {checked : Date.Checked}
    (opened : Date.openChecked limits wire = .ok checked)
    (zero : checked.snapshot.groupCount = 0)
    (written : Date.Events.ToIpc.convert limits ipcLimits wire = .ok ipc) :
    Arrow.DateStream.read ipcLimits.ipc ipc =
      .ok ⟨⟨checked.binding.leaf.name, checked.binding.leaf.repetition == some .optional, .day⟩, []⟩ := by
  obtain ⟨observed, readParquet, readIpc⟩ := Date.RoundTrip.forward_observes written
  let expected : Observation := ⟨checked.binding.leaf.name,
    checked.binding.leaf.repetition == some .optional, []⟩
  have empty : ParquetObserves limits wire expected :=
    ⟨checked, [], opened, by simp [zero, Pure.pure, Except.pure], rfl⟩
  change Arrow.DateStream.read ipcLimits.ipc ipc = .ok expected.ipc
  rwa [empty.unique readParquet]

theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {parquetLimits : Date.Limits} {writerLimits : Date.FromIpc.SchemaOnly.Limits}
    {input output : KBytes} {middle : Bytes}
    (toParquet : Date.FromIpc.SchemaOnly.convert inputLimits writerLimits parquetLimits input = .ok middle)
    (toIpc : Date.Events.ToIpc.convert parquetLimits outputLimits middle = .ok output) :
    ∃ field, field.unit = .day ∧ Arrow.DateStream.read inputLimits input = .ok ⟨field, []⟩ ∧
      ParquetObserves parquetLimits middle ⟨field.name, field.nullable, []⟩ ∧
      Arrow.DateStream.read outputLimits.ipc output = .ok ⟨field, []⟩ := by
  obtain ⟨field, _, readInput, day, _, _, _, readParquet, _⟩ :=
    Date.FromIpc.SchemaOnly.convert_readback toParquet
  obtain ⟨_, readMiddle, readOutput⟩ := Date.RoundTrip.forward_observes toIpc
  rw [← readParquet.unique readMiddle, ipc_empty day] at readOutput
  exact ⟨field, day, readInput, readParquet, readOutput⟩

theorem parquet_roundtrip {inputLimits outputLimits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {writerLimits : Date.FromIpc.SchemaOnly.Limits} {input output : Bytes} {middle : KBytes}
    (toIpc : Date.Events.ToIpc.convert inputLimits ipcLimits input = .ok middle)
    (toParquet : Date.FromIpc.SchemaOnly.convert ipcLimits.ipc writerLimits outputLimits middle = .ok output) :
    ∃ field, field.unit = .day ∧
      ParquetObserves inputLimits input ⟨field.name, field.nullable, []⟩ ∧
      Arrow.DateStream.read ipcLimits.ipc middle = .ok ⟨field, []⟩ ∧
      ParquetObserves outputLimits output ⟨field.name, field.nullable, []⟩ := by
  obtain ⟨_, readInput, readMiddle⟩ := Date.RoundTrip.forward_observes toIpc
  obtain ⟨field, _, rereadMiddle, day, _, _, _, readOutput, _⟩ :=
    Date.FromIpc.SchemaOnly.convert_readback toParquet
  have normalized := rereadMiddle.trans (congrArg Except.ok (ipc_empty day).symm)
  have same := Observation.ipc_injective (Except.ok.inj (readMiddle.symm.trans normalized))
  rw [same] at readInput
  exact ⟨field, day, readInput, rereadMiddle, readOutput⟩

end Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly
