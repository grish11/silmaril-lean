module

public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.Composition

public section

namespace Silmaril.Formats.Parquet.Date.RoundTrip

/-- Each observed batch index is the original checked footer index, including
the exact number of slots when the group is empty. -/
theorem parquet_at {limits : Date.Limits} {wire : Bytes} {observation : Observation}
    (observed : ParquetObserves limits wire observation) :
    ∃ checked, Date.openChecked limits wire = .ok checked ∧
      checked.snapshot.groupCount = observation.batches.length ∧
      ∀ index : Fin observation.batches.length, ∃ group,
        Date.readGroup limits wire index.val = .ok group ∧
        group.date32Slots = observation.batches[index.val] ∧
        group.rowCount = observation.batches[index.val].length :=
  Proofs.Formats.Parquet.Date.RoundTrip.parquet_at observed

/-- Both successful legs use the same Parquet limits at the intermediate
file. The two checked IPC observations share one Date32 descriptor and the
same positive number of explicit batches, including every empty batch. -/
theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {parquetLimits : Date.Limits} {writerLimits : Date.FromIpc.Multi.Limits}
    {input output : KBytes} {middle : Bytes}
    (toParquet : Date.FromIpc.Multi.convert inputLimits writerLimits parquetLimits input = .ok middle)
    (toIpc : Date.Events.ToIpc.convert parquetLimits outputLimits middle = .ok output) :
    ∃ observation, observation.batches ≠ [] ∧
      Arrow.DateStream.read inputLimits input = .ok observation.ipc ∧
      ParquetObserves parquetLimits middle observation ∧
      Arrow.DateStream.read outputLimits.ipc output = .ok observation.ipc :=
  Proofs.Formats.Parquet.Date.RoundTrip.ipc_roundtrip toParquet toIpc

/-- Both successful legs use the IPC writer's checked readback limits to
read the intermediate stream. The endpoints share a checked logical DATE
descriptor and all indexed signed nullable slots. -/
theorem parquet_roundtrip {inputLimits outputLimits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {writerLimits : Date.FromIpc.Multi.Limits} {input output : Bytes} {middle : KBytes}
    (toIpc : Date.Events.ToIpc.convert inputLimits ipcLimits input = .ok middle)
    (toParquet : Date.FromIpc.Multi.convert ipcLimits.ipc writerLimits outputLimits middle = .ok output) :
    ∃ observation, observation.batches ≠ [] ∧ ParquetObserves inputLimits input observation ∧
      Arrow.DateStream.read ipcLimits.ipc middle = .ok observation.ipc ∧
      ParquetObserves outputLimits output observation :=
  Proofs.Formats.Parquet.Date.RoundTrip.parquet_roundtrip toIpc toParquet

end Silmaril.Formats.Parquet.Date.RoundTrip
