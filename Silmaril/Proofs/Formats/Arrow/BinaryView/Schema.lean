module

public import Silmaril.Formats.Arrow.BinaryView.Schema.Defs
import Silmaril.Formats.Arrow.BinaryView.Batch.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Schema

open Silmaril.Formats
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Arrow.BinaryView.Schema

theorem kind_ofTag_iff (tag : Nat) (kind : Kind) :
    Kind.ofTag tag = .ok kind ↔ tag = kind.tag := by
  unfold Kind.ofTag
  split <;> cases kind <;> simp_all [Kind.tag]

theorem readBatch_binds (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (observed : Observed) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok observed ↔
      readMessage ipc schemaMetadata = .ok observed.field ∧
        readField ipc limits observed.field recordMetadata body = .ok observed.values := by
  cases schemaRead : readMessage ipc schemaMetadata with
  | error cause => simp [readBatch, schemaRead, Except.mapError, bind, Except.bind]
  | ok field =>
    rcases observed with ⟨declared, values⟩
    change _ ↔ Except.ok field = .ok declared ∧ _
    by_cases same : field = declared
    · subst declared
      cases column : readField ipc limits field recordMetadata body <;>
        simp [readBatch, schemaRead, column, Except.mapError, bind, Except.bind, pure, Except.pure]
    · cases column : readField ipc limits field recordMetadata body <;>
        simp [readBatch, schemaRead, column, Except.mapError, bind, Except.bind, pure, Except.pure, same]

theorem readBinary_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (name : String) (nullable : Bool)
    (values : List (Option KBytes)) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok ⟨⟨name, nullable, .binary⟩, values⟩ ↔
      readMessage ipc schemaMetadata = .ok ⟨name, nullable, .binary⟩ ∧
        ∃ frame, Batch.bindBuffers ipc limits nullable recordMetadata body = .ok frame ∧
          Column.Wire limits frame.metadata.node nullable frame.buffers values := by
  rw [readBatch_binds]
  exact and_congr_right fun _ => Batch.readBinary_iff ipc limits nullable recordMetadata body values

theorem readUtf8_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (schemaMetadata recordMetadata body : KBytes) (name : String) (nullable : Bool)
    (values : List (Option String)) :
    readBatch ipc limits schemaMetadata recordMetadata body = .ok ⟨⟨name, nullable, .utf8⟩, values⟩ ↔
      readMessage ipc schemaMetadata = .ok ⟨name, nullable, .utf8⟩ ∧
        ∃ frame, Batch.bindBuffers ipc limits nullable recordMetadata body = .ok frame ∧
          ∃ slots, Column.Wire limits frame.metadata.node nullable frame.buffers slots ∧
            slots.mapM (·.mapM Column.decodeUtf8) = .ok values := by
  rw [readBatch_binds]
  exact and_congr_right fun _ => Batch.readUtf8_iff ipc limits nullable recordMetadata body values

end Silmaril.Proofs.Formats.Arrow.BinaryView.Schema
