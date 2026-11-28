module

meta import Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def limits : Date.RoundTrip.ViaCsv.Limits :=
  ⟨{}, ⟨4096, 16⟩, ⟨1024, 8⟩, {},
    ⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, {}⟩

private meta def cycle (directory : System.FilePath) (source : Bytes) : IO Unit := do
  let csv ← match Date.ToCsv.convert limits.source limits.exportCsv "日付" true source with
    | .ok csv => pure csv
    | .error error => throw (IO.userError (reprStr error))
  let .ok output := Date.RoundTrip.ViaCsv.convert limits "日付" true source
    | throw (IO.userError "Parquet DATE CSV cycle failed")
  IO.FS.writeBinFile (directory / "export.csv") ⟨csv.toArray⟩
  IO.FS.writeBinFile (directory / "normalized.parquet") output.data

private meta def rejects (source : Bytes) (cause : Date.RoundTrip.ViaCsv.Error)
    (bounds : Date.RoundTrip.ViaCsv.Limits := limits) (name : String := "日付") : Bool :=
  match Date.RoundTrip.ViaCsv.convert bounds name true source with
  | .error actual => actual == cause
  | .ok _ => false

#guard rejects (Bytes.ofList []) (.toCsv (.source (.openFailure (.snapshot (.footer
  (.framing .shortFile))))))
