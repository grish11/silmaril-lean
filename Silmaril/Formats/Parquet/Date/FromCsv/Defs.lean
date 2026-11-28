module

public import Silmaril.Formats.Arrow.DateStream.FromCsv.Defs
public import Silmaril.Formats.Parquet.Date.FromIpc.Defs

/-! # Typed civil-date CSV to a checked single-group Parquet DATE file -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.FromCsv

inductive Error where
  | csvToIpc (cause : Arrow.DateStream.FromCsv.Error)
  | ipcToParquet (cause : FromIpc.Error)
  deriving DecidableEq, Repr

/-- Bound the typed CSV and make one checked Date32 batch. Use the same IPC
readback limits in the Parquet leg, which returns only a certified DATE file.
A header-only CSV supplies one explicit zero-row batch and row group. -/
def convert (csv : Arrow.DateStream.FromCsv.CsvLimits) (ipc : Arrow.ObservationLimits)
    (writer : FlatInt32Writer.Limits) (readback : Date.Limits) (name : String) (nullable : Bool)
    (input : Csv.Bytes) : Except Error Bytes := do
  let intermediate ← (Arrow.DateStream.FromCsv.convert ipc csv name nullable input).mapError .csvToIpc
  (FromIpc.convert ipc.ipc writer readback intermediate).mapError .ipcToParquet

end Silmaril.Formats.Parquet.Date.FromCsv
