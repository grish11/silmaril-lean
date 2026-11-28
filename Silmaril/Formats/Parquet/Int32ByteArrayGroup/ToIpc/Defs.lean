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

def writerSchemaOrdered (order : Writer.Order) (schema : Prepare.Schema) : StreamWriter.Schema :=
  ⟨order, schema.intName, schema.intNullable, schema.viewName, schema.viewNullable⟩

def writerSchema (schema : Prepare.Schema) : StreamWriter.Schema :=
  writerSchemaOrdered .intFirst schema

/-- Relative order of the two selected leaves in the checked flat footer. -/
def selectedOrder {int32 byteArray : Field} (projection : Checked int32 byteArray) : Writer.Order :=
  if projection.byteArrayBinding.columnOrdinal < projection.int32Binding.columnOrdinal then
    .viewFirst
  else .intFirst

def writerBatch (batch : Prepare.Batch) : StreamWriter.BatchInput :=
  ⟨batch.rowCount, batch.intValues, batch.viewValues⟩

/-- Observe both slots at their original row positions in the chosen field order. -/
def groupObservationOrdered (order : Writer.Order) (int32 byteArray : Field) (rows : List Row) :
    StreamWriter.BatchObservation :=
  (rows.length, some (order.pair
    (⟨int32.name, decide (int32.layout = .optional), .primitive .int32⟩,
      .int32 (rows.map fun pair => pair.1.map Arrow.Value.int32))
    (⟨byteArray.name, decide (byteArray.layout = .optional), .view .binary⟩,
      .binaryView (rows.map fun pair => pair.2.map Bytes.toList))))

def groupObservation (int32 byteArray : Field) (rows : List Row) : StreamWriter.BatchObservation :=
  groupObservationOrdered .intFirst int32 byteArray rows

/-- Preserve the selected leaves' physical order and emit one batch per footer group. -/
def convertOrdered (parquet : File.Limits) (ipc : Arrow.MixedFlat.Limits)
    (input : Bytes) (int32 byteArray : Field) : Except Error KBytes := do
  let checked ← (File.openFile parquet input int32 byteArray).mapError .source
  let prepared ← (Prepare.prepareChecked checked).mapError .source
  (StreamWriter.emit ipc (writerSchemaOrdered (selectedOrder checked.projection) prepared.schema)
    (prepared.batches.map writerBatch)).mapError .writer

/-- Exhaust the checked source before invoking the native writer. Only a
complete stream is returned, with the original failure tagged by stage. -/
def convert (parquet : File.Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes) (int32 byteArray : Field) :
    Except Error KBytes := do
  let prepared ← (Prepare.prepare parquet input int32 byteArray).mapError .source
  (StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch)).mapError .writer

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc
