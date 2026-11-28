module

public import Silmaril.Formats.Arrow.TimestampBatch.Defs
import Silmaril.Formats.ColumnarTimestamp.Wire.Thms

namespace Silmaril.Proofs.Formats.Arrow.TimestampBatch

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Arrow.TimestampBatch

public theorem bindSchema_iff {schema : SchemaReader.Schema} {binding : Binding} :
    bindSchema schema = .ok binding ↔
      ∃ name nullable unit timezone,
        schema = ⟨.little, [⟨name, nullable, .timestamp unit timezone⟩]⟩ ∧
        binding = ⟨name, nullable, ⟨tickUnit unit, timezone⟩⟩ := by
  obtain ⟨endian, fields⟩ := schema
  cases endian with
  | big => simp [bindSchema]
  | little =>
    cases fields with
    | nil => simp [bindSchema]
    | cons field rest =>
      cases rest with
      | cons next rest => simp [bindSchema]
      | nil =>
        obtain ⟨name, nullable, kind⟩ := field
        cases kind <;> simp [-Bool.exists_bool, bindSchema, eq_comm (a := binding)]

public theorem batchView_layout {limits : Limits} {binding : Binding} {message : Message}
    {body : KBytes} {view : View} (checked : batchView limits binding message body = .ok view) :
    message.bodyLength = body.len ∧ body.len % 8 = 0 ∧
      ∃ batch node bitmap data,
        message.header = .recordBatch batch ∧ batch.nodes = [node] ∧ batch.buffers = [bitmap, data] ∧
        node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] ∧
        node.nullCount ≤ node.length ∧ (binding.nullable = false → node.nullCount = 0) ∧
        Body.BitmapExtent (Body.sliceBuffer body bitmap) node.length ∧ 8 * node.length ≤ data.length ∧
        view = ⟨node, Body.sliceBuffer body bitmap, ⟨(body.slice data.offset (8 * node.length)).toByteArray⟩⟩ := by
  unfold batchView at checked
  split at checked
  · contradiction
  split at checked
  · contradiction
  rename_i extent
  have ⟨length, aligned⟩ := not_or.mp extent
  split at checked
  · contradiction
  split at checked
  · contradiction
  split at checked
  · contradiction
  · rename_i batch kind
    split at checked
    · contradiction
    split at checked
    · rename_i node bitmap data nodes buffers
      split at checked
      · rename_i layout
        dsimp only at checked
        split at checked
        · rename_i bitmapOk
          split at checked
          · rename_i values
            cases checked
            exact ⟨not_not.mp length, not_not.mp aligned, batch, node, bitmap, data, kind, nodes,
              buffers, layout.1, layout.2, bitmapOk.1, bitmapOk.2.1, bitmapOk.2.2, values, rfl⟩
          · contradiction
        · contradiction
      · contradiction
    · contradiction

private theorem place_iff {binding : Binding} (bitmap : KBytes) (entry : Value binding × Nat)
    (value : Option (Value binding)) : place bitmap entry = .ok value ↔ SlotWire bitmap entry value := by
  cases bit : Body.validAt bitmap entry.2 <;> simp [place, SlotWire, bit, pure, Except.pure, eq_comm]

private theorem placeSlots_iff {binding : Binding} (bitmap : KBytes)
    (entries : List (Value binding × Nat)) (slots : Column binding) :
    entries.mapM (place bitmap) = .ok slots ↔ List.Forall₂ (SlotWire bitmap) entries slots := by
  induction entries generalizing slots with
  | nil => cases slots <;> simp [pure, Except.pure]
  | cons entry rest ih =>
    rw [List.mapM_cons]
    cases first : place bitmap entry <;> cases remaining : rest.mapM (place bitmap) <;>
      cases slots <;> simp [first, remaining, ← place_iff, ← ih, bind, Except.bind, pure, Except.pure]

public theorem decodeBatch_sound {limits : Limits} {binding : Binding} {message : Message}
    {body : KBytes} {slots : Column binding} (read : decodeBatch limits binding message body = .ok slots) :
    ∃ view ticks, batchView limits binding message body = .ok view ∧
      binding.metadata.decodeBufferLE view.node.length view.values = .ok ticks ∧
      List.Forall₂ (SlotWire view.validity) ticks.zipIdx slots ∧
      slots.length = view.node.length ∧ slots.countP Option.isNone = view.node.nullCount := by
  cases arranged : batchView limits binding message body with
  | error e => simp [TimestampBatch.decodeBatch, arranged, bind, Except.bind] at read
  | ok view =>
    cases words : binding.metadata.decodeBufferLE view.node.length view.values with
    | error e => simp [TimestampBatch.decodeBatch, arranged, words, Except.mapError, bind, Except.bind] at read
    | ok ticks =>
      cases observed : ticks.zipIdx.mapM (place view.validity) with
      | error e => simp [TimestampBatch.decodeBatch, arranged, words, observed, Except.mapError, bind, Except.bind] at read
      | ok values =>
        by_cases nulls : values.countP Option.isNone = view.node.nullCount
        · simp only [TimestampBatch.decodeBatch, arranged, words, observed, nulls, Except.mapError, bind, Except.bind,
            pure, Except.pure, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq] at read
          subst slots
          have wire := (placeSlots_iff view.validity _ _).mp observed
          have length := (ColumnarTimestamp.Wire.encodeLE_decodeLE words).1
          exact ⟨view, ticks, rfl, words, wire, (by simpa using wire.length_eq.symm.trans (List.length_zipIdx.trans length)), nulls⟩
        · simp [TimestampBatch.decodeBatch, arranged, words, observed, nulls, Except.mapError, bind, Except.bind] at read

public theorem readBatch_binds {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {observation : Observation} (read : readBatch limits schemaMetadata recordMetadata body = .ok observation) :
    ∃ schema message,
      SchemaReader.readMessage limits schemaMetadata = .ok schema ∧
      bindSchema schema = .ok observation.binding ∧
      Arrow.readMessage limits recordMetadata = .ok message ∧
      decodeBatch limits observation.binding message body = .ok observation.slots := by
  cases schemaRead : SchemaReader.readMessage limits schemaMetadata with
  | error e => simp [readBatch, schemaRead, bind, Except.bind] at read
  | ok schema =>
    cases bindRead : bindSchema schema with
    | error e => simp [readBatch, schemaRead, bindRead, bind, Except.bind] at read
    | ok binding =>
      cases recordRead : Arrow.readMessage limits recordMetadata with
      | error e => simp [readBatch, schemaRead, bindRead, recordRead, bind, Except.bind] at read
      | ok message =>
        cases values : decodeBatch limits binding message body with
        | error e => simp [readBatch, schemaRead, bindRead, recordRead, values, bind, Except.bind] at read
        | ok slots =>
          simp only [readBatch, schemaRead, bindRead, recordRead, values, bind, Except.bind,
            pure, Except.pure, Except.ok.injEq] at read
          subst observation
          exact ⟨schema, message, rfl, bindRead, rfl, values⟩

end Silmaril.Proofs.Formats.Arrow.TimestampBatch
