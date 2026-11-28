module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter.Readback
import Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter.Size

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.StreamWriter

theorem Wire.schema_extent (field : Schema.Field) : (schema field).len = schemaSize field :=
  Proofs.Formats.Arrow.BinaryView.StreamWriter.schema_extent field

theorem Wire.recordBatch_extent (node : FieldNode) (buffers : List Buffer) (count bodyLength : Nat) :
    (recordBatch node buffers count bodyLength).len = recordBatchSize buffers.length :=
  Proofs.Formats.Arrow.BinaryView.StreamWriter.recordBatch_extent node buffers count bodyLength

/-- Success certifies the declared field and all ordered batch observations
through the existing exact-EOS stream reader. -/
theorem emit_readback {ipc : Arrow.Limits} {limits : Column.Limits} {field : Schema.Field}
    {batches : List (Schema.Values field.kind)} {wire : KBytes}
    (written : emit ipc limits field batches = .ok wire) :
    ∃ decoded, Stream.read ipc limits wire = .ok decoded ∧ Agrees field batches decoded :=
  Proofs.Formats.Arrow.BinaryView.StreamWriter.emit_readback written

/-- The BinaryView law compares nullable octets in each batch and recovers
the exact field, even when there are no batches or a batch is empty. -/
theorem emit_binary_readback {ipc : Arrow.Limits} {limits : Column.Limits} {name : String}
    {nullable : Bool} {batches : List (List (Option KBytes))} {wire : KBytes}
    (written : emit ipc limits ⟨name, nullable, .binary⟩ batches = .ok wire) :
    ∃ decoded : List (List (Option KBytes)),
      Stream.read ipc limits wire = .ok ⟨⟨name, nullable, .binary⟩, decoded⟩ ∧
        decoded.map (List.map (Option.map KBytes.toList)) =
          batches.map (List.map (Option.map KBytes.toList)) :=
  Proofs.Formats.Arrow.BinaryView.StreamWriter.emit_binary_readback written

theorem emit_utf8_readback {ipc : Arrow.Limits} {limits : Column.Limits} {name : String}
    {nullable : Bool} {batches : List (List (Option String))} {wire : KBytes}
    (written : emit ipc limits ⟨name, nullable, .utf8⟩ batches = .ok wire) :
    Stream.read ipc limits wire = .ok ⟨⟨name, nullable, .utf8⟩, batches⟩ :=
  Proofs.Formats.Arrow.BinaryView.StreamWriter.emit_utf8_readback written

end Silmaril.Formats.Arrow.BinaryView.StreamWriter
