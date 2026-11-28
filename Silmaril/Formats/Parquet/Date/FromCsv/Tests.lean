module

meta import Silmaril.Formats.Parquet.Date.FromCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def csvBounds : Arrow.DateStream.FromCsv.CsvLimits := ⟨1024, 16⟩

private meta def writerBounds : FlatInt32Writer.Limits :=
  ⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩

private meta def bytes (value : String) : Csv.Bytes := value.toUTF8.data.toList

private meta def rejects (input : Csv.Bytes) (nullable : Bool) (cause : Date.FromCsv.Error)
    (csv : Arrow.DateStream.FromCsv.CsvLimits := csvBounds) (ipc : Arrow.ObservationLimits := {})
    (writer : FlatInt32Writer.Limits := writerBounds) (readback : Date.Limits := {}) : Bool :=
  match Date.FromCsv.convert csv ipc writer readback "日付" nullable input with
  | .error actual => actual == cause
  | .ok _ => false

private meta def emitFixture (path : System.FilePath) (name : String) (nullable : Bool)
    (input : Csv.Bytes) : IO Unit :=
  match Date.FromCsv.convert csvBounds {} writerBounds {} name nullable input with
  | .ok wire => IO.FS.writeBinFile path wire.data
  | .error cause => throw (IO.userError (reprStr cause))

#guard rejects (bytes "x") true (.csvToIpc (.csvByteLimit 1 0)) ⟨0, 0⟩
#guard rejects (bytes "日付\r\nN\r\n") true (.csvToIpc (.csvRowLimit 1 0)) ⟨1024, 0⟩
#guard rejects (bytes "日付\r\n") true (.csvToIpc (.writer (.writer (.limit .batches))))
  csvBounds { ipc := { batches := 0 } }
#guard rejects (bytes "日付\r\n") true (.ipcToParquet (.writer .fileLimit))
  csvBounds {} { writerBounds with maxFileBytes := 0 }
#guard rejects (bytes "日付\r\n") true (.ipcToParquet (.readback (.snapshot (.footer (.framing .footerLimit)))))
  csvBounds {} writerBounds { snapshot := { footer := { maxFooterBytes := 0 } } }
#guard rejects [] true (.csvToIpc (.csv (.csv .missingHeader)))
  csvBounds {} { writerBounds with maxFileBytes := 0 }
