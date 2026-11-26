module

meta import Silmaril.Formats.Arrow.DateStream.ToCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow

private meta def bounds : DateStream.FromCsv.CsvLimits := ⟨1024, 16⟩

private meta def bytes (value : String) : Csv.Bytes := value.toUTF8.data.toList

private meta def rejects (wire : KBytes) (cause : DateStream.ToCsv.Error) (name : String := "日付")
    (nullable : Bool := true) : Bool :=
  match DateStream.ToCsv.convert {} bounds name nullable wire with
  | .error actual => actual == cause
  | .ok _ => false

private meta def toCsv (csv : DateStream.FromCsv.CsvLimits) (name : String) (nullable : Bool)
    (wire : KBytes) : IO Csv.Bytes :=
  match DateStream.ToCsv.convert {} csv name nullable wire with
  | .ok output => pure output
  | .error cause => throw (IO.userError (reprStr cause))

private meta def toIpc (csv : DateStream.FromCsv.CsvLimits) (name : String) (nullable : Bool)
    (input : Csv.Bytes) : IO KBytes :=
  match DateStream.FromCsv.convert {} csv name nullable input with
  | .ok output => pure output
  | .error cause => throw (IO.userError (reprStr cause))

private meta def cycles (directory : System.FilePath) (name : String) (nullable : Bool)
    (source : KBytes) (minimal canonical : Csv.Bytes) : IO Unit := do
  let csv ← toCsv bounds name nullable source
  if csv != canonical then throw (IO.userError "IPC export did not match canonical CSV")
  let returned ← toIpc bounds name nullable csv
  let wire ← toIpc bounds name nullable minimal
  let normalized ← toCsv bounds name nullable wire
  if normalized != canonical || Csv.Utf8.decode normalized != Csv.Utf8.decode minimal then
    throw (IO.userError "CSV round trip did not normalize exact lexical rows")
  let fixed ← toIpc bounds name nullable canonical
  if (← toCsv bounds name nullable fixed) != canonical then
    throw (IO.userError "Canonical CSV bytes changed")
  IO.FS.writeBinFile (directory / "from-ipc.csv") ⟨csv.toArray⟩
  IO.FS.writeBinFile (directory / "ipc-cycle.arrow") returned.toByteArray
  IO.FS.writeBinFile (directory / "from-csv.arrow") wire.toByteArray
  IO.FS.writeBinFile (directory / "csv-cycle.csv") ⟨normalized.toArray⟩

-- A valid unquoted CSV input can fit while its canonical export exceeds the same byte cap.
#guard Id.run do
  let input := bytes "x\r\nN\r\n"
  let cap := ⟨input.length, 1⟩
  let .ok wire := DateStream.FromCsv.convert {} cap "x" true input | return false
  return DateStream.ToCsv.convert {} cap "x" true wire == .error (.csvByteLimit 10 6) &&
    DateStream.ToCsv.convert {} ⟨0, 0⟩ "x" true wire == .error (.csvRowLimit 1 0)
