module

public import Silmaril.Formats.Arrow.TimestampBatch.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampBatch.Binding

/-! Checked schema binding, body layout, and ordered nullable observations. -/

public section

namespace Silmaril.Formats.Arrow.TimestampBatch

/-- A binding comes from one normalized little-endian Timestamp field. -/
theorem bindSchema_iff {schema : SchemaReader.Schema} {binding : Binding} :
    bindSchema schema = .ok binding ↔
      ∃ name nullable unit timezone,
        schema = ⟨.little, [⟨name, nullable, .timestamp unit timezone⟩]⟩ ∧
        binding = ⟨name, nullable, ⟨tickUnit unit, timezone⟩⟩ :=
  Proofs.Formats.Arrow.TimestampBatch.bindSchema_iff

/-- The two checked descriptors locate the bitmap and the logical value bytes. -/
theorem batchView_layout {limits : Limits} {binding : Binding} {message : Message}
    {body : KBytes} {view : View} (checked : batchView limits binding message body = .ok view) :
    message.bodyLength = body.len ∧ body.len % 8 = 0 ∧
      ∃ batch node bitmap data,
        message.header = .recordBatch batch ∧ batch.nodes = [node] ∧ batch.buffers = [bitmap, data] ∧
        node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] ∧
        node.nullCount ≤ node.length ∧ (binding.nullable = false → node.nullCount = 0) ∧
        Body.BitmapExtent (Body.sliceBuffer body bitmap) node.length ∧ 8 * node.length ≤ data.length ∧
        view = ⟨node, Body.sliceBuffer body bitmap, ⟨(body.slice data.offset (8 * node.length)).toByteArray⟩⟩ :=
  Proofs.Formats.Arrow.TimestampBatch.batchView_layout checked

/-- Every slot observes the corresponding validity bit and exact Timestamp word. -/
theorem decodeBatch_sound {limits : Limits} {binding : Binding} {message : Message}
    {body : KBytes} {slots : Column binding} (read : decodeBatch limits binding message body = .ok slots) :
    ∃ view ticks, batchView limits binding message body = .ok view ∧
      binding.metadata.decodeBufferLE view.node.length view.values = .ok ticks ∧
      List.Forall₂ (SlotWire view.validity) ticks.zipIdx slots ∧
      slots.length = view.node.length ∧ slots.countP Option.isNone = view.node.nullCount :=
  Proofs.Formats.Arrow.TimestampBatch.decodeBatch_sound read

/-- Successful standalone decoding uses the supplied Schema and RecordBatch metadata. -/
theorem readBatch_binds {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {observation : Observation} (read : readBatch limits schemaMetadata recordMetadata body = .ok observation) :
    ∃ schema message,
      SchemaReader.readMessage limits schemaMetadata = .ok schema ∧
      bindSchema schema = .ok observation.binding ∧
      Arrow.readMessage limits recordMetadata = .ok message ∧
      decodeBatch limits observation.binding message body = .ok observation.slots :=
  Proofs.Formats.Arrow.TimestampBatch.readBatch_binds read

end Silmaril.Formats.Arrow.TimestampBatch
