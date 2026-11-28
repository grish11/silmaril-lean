module

public import Silmaril.Formats.Parquet.Date.FromCsv.Defs
import Silmaril.Proofs.Formats.Parquet.Date.FromCsv.Readback

public section

namespace Silmaril.Formats.Parquet.Date.FromCsv

/-- The same intermediate IPC limits connect the two successful legs. CSV
input caps, Parquet output limits and checked readback limits are independent. -/
theorem convert_eq_ok_iff {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {ipc : Arrow.ObservationLimits} {writer : FlatInt32Writer.Limits} {readback : Date.Limits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {output : Bytes} :
    convert csv ipc writer readback name nullable input = .ok output ↔
      ∃ intermediate, Arrow.DateStream.FromCsv.convert ipc csv name nullable input = .ok intermediate ∧
        FromIpc.convert ipc.ipc writer readback intermediate = .ok output :=
  Proofs.Formats.Parquet.Date.FromCsv.convert_eq_ok_iff

/-- A successful result has the exact flat INT32 DATE leaf and both
annotations, with one group of the same ordered nullable signed days as the
typed CSV table. An empty typed table still has a group at index zero. -/
theorem convert_readback {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {ipc : Arrow.ObservationLimits} {writer : FlatInt32Writer.Limits} {readback : Date.Limits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {output : Bytes}
    (written : convert csv ipc writer readback name nullable input = .ok output) :
    ∃ table checked group,
      Csv.Typed.Codecs.Date32.decode (Arrow.DateStream.FromCsv.schema name nullable) id input = .ok table ∧
      Date.openChecked readback output = .ok checked ∧ Date.readGroup readback output 0 = .ok group ∧
      checked.snapshot.groupCount = 1 ∧
      group.binding.leaf = FromIpc.leaf ⟨name, nullable, .day⟩ ∧
      group.binding.annotation = .logicalAndConverted ∧
      group.rowCount = table.length ∧ group.date32Slots = Arrow.DateStream.FromCsv.slots table :=
  Proofs.Formats.Parquet.Date.FromCsv.convert_readback written

/-- CSV-stage errors are returned before attempting to emit Parquet bytes. -/
theorem convert_csvToIpc_error {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {ipc : Arrow.ObservationLimits} {writer : FlatInt32Writer.Limits} {readback : Date.Limits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {cause : Arrow.DateStream.FromCsv.Error}
    (failed : Arrow.DateStream.FromCsv.convert ipc csv name nullable input = .error cause) :
    convert csv ipc writer readback name nullable input = .error (.csvToIpc cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.FromCsv
