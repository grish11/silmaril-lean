module

meta import Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow

private meta def label : String := "日付"

private meta def bounds : DateStream.FromCsv.CsvLimits := ⟨1024, 16⟩

private meta def rejects (wire : KBytes) (cause : DateStream.ToCsv.Error)
    (csv : DateStream.FromCsv.CsvLimits := bounds) (ipc : Limits := {}) : Bool :=
  match DateStream.ToCsv.RowObservational.exportRows ipc csv label true wire with
  | .error actual => actual == cause
  | .ok _ => false

private meta def cycle (directory : System.FilePath) (source : KBytes) : IO Unit := do
  let .ok csv := DateStream.ToCsv.RowObservational.exportRows { rows := 2 } bounds label true source
    | throw (IO.userError "row-observational CSV export failed")
  let .ok output := DateStream.FromCsv.convert {} bounds label true csv
    | throw (IO.userError "canonical CSV reimport failed")
  IO.FS.writeBinFile (directory / "export.csv") ⟨csv.toArray⟩
  IO.FS.writeBinFile (directory / "normalized.arrow") output.toByteArray

#guard rejects (KBytes.leaf 0 0) (.reader (.schemaEnvelope (.malformed .truncated)))
