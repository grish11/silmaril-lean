module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Defs

/-! Convert one explicitly selected uncompressed PLAIN BYTE_ARRAY leaf to a
complete Arrow BinaryView IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc

open Arrow.BinaryView

inductive Error where
  | source (cause : SourceError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

/-- Fully exhaust the selected column before writing the exact BinaryView
field and one record per footer group. Only a complete stream is returned. -/
def convert (parquet : File.Limits) (ipc : Arrow.Limits) (view : Column.Limits)
    (input : Bytes) (name : String) (layout : FlatColumn.Layout) : Except Error KBytes := do
  let source ← (readSource parquet input name layout).mapError .source
  (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
