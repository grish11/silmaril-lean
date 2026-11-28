module

public import Silmaril.Formats.Arrow.BinaryView.Schema.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Schema

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Schema

/-- The two admitted union tags select exactly their declared view kinds. -/
theorem kind_ofTag_iff (tag : Nat) (kind : Kind) :
    Kind.ofTag tag = .ok kind ↔ tag = kind.tag :=
  Proofs.Formats.Arrow.BinaryView.Schema.kind_ofTag_iff tag kind

/-- A successful paired read retains the exact checked field and reads with
that field's kind and nullability. -/
theorem readBatch_binds (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (observed : Observed) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok observed ↔
      readMessage ipc schemaMetadata = .ok observed.field ∧
        readField ipc limits observed.field recordMetadata body = .ok observed.values :=
  Proofs.Formats.Arrow.BinaryView.Schema.readBatch_binds ipc limits schemaMetadata recordMetadata body observed

/-- BinaryView success gives the declared field and ordered byte windows. -/
theorem readBinary_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (name : String) (nullable : Bool)
    (values : List (Option KBytes)) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok ⟨⟨name, nullable, .binary⟩, values⟩ ↔
      readMessage ipc schemaMetadata = .ok ⟨name, nullable, .binary⟩ ∧
        ∃ frame, Batch.bindBuffers ipc limits nullable recordMetadata body = .ok frame ∧
          Column.Wire limits frame.metadata.node nullable frame.buffers values :=
  Proofs.Formats.Arrow.BinaryView.Schema.readBinary_iff
    ipc limits schemaMetadata recordMetadata body name nullable values

/-- Utf8View success gives the declared field and ordered checked strings. -/
theorem readUtf8_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (name : String) (nullable : Bool)
    (values : List (Option String)) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok ⟨⟨name, nullable, .utf8⟩, values⟩ ↔
      readMessage ipc schemaMetadata = .ok ⟨name, nullable, .utf8⟩ ∧
        ∃ frame, Batch.bindBuffers ipc limits nullable recordMetadata body = .ok frame ∧
          ∃ slots, Column.Wire limits frame.metadata.node nullable frame.buffers slots ∧
            slots.mapM (·.mapM Column.decodeUtf8) = .ok values :=
  Proofs.Formats.Arrow.BinaryView.Schema.readUtf8_iff
    ipc limits schemaMetadata recordMetadata body name nullable values

end Silmaril.Formats.Arrow.BinaryView.Schema
