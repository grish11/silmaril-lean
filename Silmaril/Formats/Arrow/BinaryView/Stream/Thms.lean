module

public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Stream

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Stream

/-- The first envelope admits exactly the field declared in its metadata slice. -/
theorem readSchema_iff (ipc : Arrow.Limits) (input : KBytes) (field : Schema.Field) (next : Nat) :
    readSchema ipc input = .ok (field, next) ↔
      ∃ size, readEnvelope ipc input 0 = .ok (.metadata size) ∧
        Schema.readMessage ipc (input.slice 8 size) = .ok field ∧ next = 8 + size :=
  Proofs.Formats.Arrow.BinaryView.Stream.readSchema_iff ipc input field next

/-- Framed admission agrees with the standalone field observation on the
declared, checked body window. -/
theorem readBatch_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (offset size : Nat) (values : Schema.Values field.kind) (next : Nat) :
    readBatch ipc limits input field offset size = .ok (values, next) ↔
      BatchWire ipc limits input field offset size values next :=
  Proofs.Formats.Arrow.BinaryView.Stream.readBatch_iff ipc limits input field offset size values next

/-- A suffix succeeds exactly when the ordered records consume the carrier
through an explicit final EOS within the batch budget. -/
theorem readBatches_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (remaining index offset : Nat) (batches : List (Schema.Values field.kind)) :
    readBatches ipc limits input field remaining index offset = .ok batches ↔
      BatchesWire ipc limits input field remaining offset batches :=
  Proofs.Formats.Arrow.BinaryView.Stream.readBatches_iff ipc limits input field remaining index offset batches

/-- The exact declared field governs the ordered batch observations. -/
theorem read_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes) (result : Observed) :
    read ipc limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema ipc input = .ok (result.field, start) ∧
          BatchesWire ipc limits input result.field ipc.batches start result.batches :=
  Proofs.Formats.Arrow.BinaryView.Stream.read_iff ipc limits input result

/-- Each observed batch, including an empty batch, consumes one unit of fuel. -/
theorem batches_length_le {ipc : Arrow.Limits} {limits : Column.Limits} {input : KBytes}
    {field : Schema.Field} {remaining offset : Nat} {batches : List (Schema.Values field.kind)}
    (wire : BatchesWire ipc limits input field remaining offset batches) : batches.length ≤ remaining :=
  Proofs.Formats.Arrow.BinaryView.Stream.batches_length_le wire

/-- Accepted records advance to a bounded successor and use exact metadata
and body windows from the original carrier. -/
theorem batch_ranges {ipc : Arrow.Limits} {limits : Column.Limits} {input : KBytes}
    {field : Schema.Field} {offset size next : Nat} {values : Schema.Values field.kind}
    (wf : input.wf = true) (envelope : readEnvelope ipc input offset = .ok (.metadata size))
    (wire : BatchWire ipc limits input field offset size values next) :
    offset < next ∧ next ≤ input.len ∧
      (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size ∧
      ∃ body, body.toList = (input.toList.drop (offset + 8 + size)).take (next - (offset + 8 + size)) ∧
        Schema.readField ipc limits field (input.slice (offset + 8) size) body = .ok values :=
  Proofs.Formats.Arrow.BinaryView.Stream.batch_ranges wf envelope wire

end Silmaril.Formats.Arrow.BinaryView.Stream
