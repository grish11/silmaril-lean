module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Defs

/-! Convert the selected checked PLAIN INT32 and BYTE_ARRAY leaves to a
complete INT32-first BinaryView IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc

open Arrow.MixedFlat

inductive Error where
  | source (cause : File.Error)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

def writerSchema (schema : Prepare.Schema) : StreamWriter.Schema :=
  ⟨.intFirst, schema.intName, schema.intNullable, schema.viewName, schema.viewNullable⟩

def writerBatch (batch : Prepare.Batch) : StreamWriter.BatchInput :=
  ⟨batch.rowCount, batch.intValues, batch.viewValues⟩

/-- The exact observations of a source group in the mixed stream reader's
carriers, with the two slots paired at their original row position. -/
def groupObservation (int32 byteArray : Field) (rows : List Row) : StreamWriter.BatchObservation :=
  (rows.length, some [
    (⟨int32.name, decide (int32.layout = .optional), .primitive .int32⟩,
      .int32 (rows.map fun pair => pair.1.map Arrow.Value.int32)),
    (⟨byteArray.name, decide (byteArray.layout = .optional), .view .binary⟩,
      .binaryView (rows.map fun pair => pair.2.map Bytes.toList))])

/-- Exhaust the checked source before invoking the native writer. Only a
complete stream is returned, with the original failure tagged by stage. -/
def convert (parquet : File.Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes) (int32 byteArray : Field) :
    Except Error KBytes := do
  let prepared ← (Prepare.prepare parquet input int32 byteArray).mapError .source
  (StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch)).mapError .writer

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc
