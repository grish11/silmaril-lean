module

public import Silmaril.Formats.Parquet.Date.ToCsv.Defs
public import Silmaril.Formats.Parquet.Date.FromCsv.Defs

/-! # Checked Parquet DATE normalization through typed calendar CSV -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv

structure Limits where
  source : Date.Limits
  exportCsv : Arrow.DateStream.FromCsv.CsvLimits
  importCsv : Arrow.DateStream.FromCsv.CsvLimits
  ipc : Arrow.ObservationLimits
  writer : FlatInt32Writer.Limits
  readback : Date.Limits

inductive Error where
  | toCsv (cause : Date.ToCsv.Error)
  | fromCsv (cause : Date.FromCsv.Error)
  deriving DecidableEq, Repr

/-- Read the original file to EOF and pass the canonical CSV to the checked
single-group writer. The export and import CSV caps are independent. -/
def convert (limits : Limits) (name : String) (nullable : Bool) (input : Bytes) :
    Except Error Bytes := do
  let csv ← (Date.ToCsv.convert limits.source limits.exportCsv name nullable input).mapError .toCsv
  (Date.FromCsv.convert limits.importCsv limits.ipc limits.writer limits.readback name nullable csv)
    |>.mapError .fromCsv

end Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv
