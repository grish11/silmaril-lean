module

public import Silmaril.Formats.Parquet.Date.RoundTrip.Thms
public import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Thms
import Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly.Composition

public section

namespace Silmaril.Formats.Parquet.Date.RoundTrip.SchemaOnly

/-- The existing forward converter writes the exact Date32 descriptor and
no record batch for a checked DATE file with zero footer groups. -/
theorem zero_group_readback {limits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {wire : Bytes} {ipc : KBytes} {checked : Date.Checked}
    (opened : Date.openChecked limits wire = .ok checked)
    (zero : checked.snapshot.groupCount = 0)
    (written : Date.Events.ToIpc.convert limits ipcLimits wire = .ok ipc) :
    Arrow.DateStream.read ipcLimits.ipc ipc =
      .ok ⟨⟨checked.binding.leaf.name, checked.binding.leaf.repetition == some .optional, .day⟩, []⟩ :=
  Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly.zero_group_readback opened zero written

/-- The two successful legs share Parquet limits on the intermediate file
and preserve the full Date32 descriptor and zero-batch IPC observation. -/
theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {parquetLimits : Date.Limits} {writerLimits : Date.FromIpc.SchemaOnly.Limits}
    {input output : KBytes} {middle : Bytes}
    (toParquet : Date.FromIpc.SchemaOnly.convert inputLimits writerLimits parquetLimits input = .ok middle)
    (toIpc : Date.Events.ToIpc.convert parquetLimits outputLimits middle = .ok output) :
    ∃ field, field.unit = .day ∧ Arrow.DateStream.read inputLimits input = .ok ⟨field, []⟩ ∧
      ParquetObserves parquetLimits middle ⟨field.name, field.nullable, []⟩ ∧
      Arrow.DateStream.read outputLimits.ipc output = .ok ⟨field, []⟩ :=
  Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly.ipc_roundtrip toParquet toIpc

/-- Both successful legs use the same intermediate IPC readback limits.
The original and returned Parquet files have the same logical descriptor
and zero groups, as the zero-batch intermediate certifies. -/
theorem parquet_roundtrip {inputLimits outputLimits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {writerLimits : Date.FromIpc.SchemaOnly.Limits} {input output : Bytes} {middle : KBytes}
    (toIpc : Date.Events.ToIpc.convert inputLimits ipcLimits input = .ok middle)
    (toParquet : Date.FromIpc.SchemaOnly.convert ipcLimits.ipc writerLimits outputLimits middle = .ok output) :
    ∃ field, field.unit = .day ∧
      ParquetObserves inputLimits input ⟨field.name, field.nullable, []⟩ ∧
      Arrow.DateStream.read ipcLimits.ipc middle = .ok ⟨field, []⟩ ∧
      ParquetObserves outputLimits output ⟨field.name, field.nullable, []⟩ :=
  Proofs.Formats.Parquet.Date.RoundTrip.SchemaOnly.parquet_roundtrip toIpc toParquet

end Silmaril.Formats.Parquet.Date.RoundTrip.SchemaOnly
