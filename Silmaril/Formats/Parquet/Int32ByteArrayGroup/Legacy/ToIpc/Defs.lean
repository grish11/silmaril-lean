module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

/-! Convert the checked paired legacy source to a native INT32/BinaryView IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc

open Arrow.MixedFlat

inductive Error where
  | source (cause : Legacy.Error)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

def writerSchema (int32Name byteArrayName : String) : StreamWriter.Schema :=
  Int32ByteArrayGroup.ToIpc.writerSchema
    (Prepare.Schema.ofSelection ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩)

def writerBatch (int32Name byteArrayName : String) (rows : Reader.RowGroup (schema int32Name byteArrayName) Value) :
    StreamWriter.BatchInput :=
  Int32ByteArrayGroup.ToIpc.writerBatch (Prepare.Batch.ofRows ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ rows)

/-- Finish the checked source before invoking the native writer. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Except Error KBytes := do
  let checked ← (openFile parquet input int32Name byteArrayName).mapError .source
  let source := Legacy.source checked
  let batches ← (source.groups.mapM source.readGroup).mapError .source
  (StreamWriter.emit ipc (writerSchema int32Name byteArrayName)
    (batches.map (writerBatch int32Name byteArrayName))).mapError .writer

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc
