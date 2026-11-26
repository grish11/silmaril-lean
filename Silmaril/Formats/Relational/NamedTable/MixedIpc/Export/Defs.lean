module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs
public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
import Mathlib.Data.List.OfFn

/-! Checked export from the shared named table to one Int32/BinaryView IPC V5
stream. Caller-supplied batch sizes partition the stored rows in order. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc.Export

open Silmaril.Relational
open Silmaril.Formats.Arrow.MixedFlat

inductive Error where
  | table (cause : NamedTable.ExportError)
  | schemaMismatch
  | octetBytes (actual limit : Nat)
  | writer (cause : StreamWriter.Error)
  | wireBytes (actual limit : Nat)
  deriving DecidableEq

def rowPair (descriptor : Descriptor) (row : Scan.Row descriptor.schema Cell) : Pair := by
  cases descriptor with
  | mk order integer binary =>
    cases order
    · exact (row (0 : Fin 2), row (1 : Fin 2))
    · exact (row (1 : Fin 2), row (0 : Fin 2))

def prepare {Name : Type*} (db : Database Name) (name : Name)
    (expected : Descriptor) (sizes : List Nat) : Except Error (List (List Pair)) := do
  let ⟨schema, chunks⟩ ← (NamedTable.exportChunks db name sizes).mapError .table
  if same : List.ofFn schema.kind = List.ofFn expected.schema.kind then
    have equal : schema = expected.schema := by
      generalize expected.schema = target at same ⊢
      rcases schema with ⟨width, labels⟩
      rcases target with ⟨width', labels'⟩
      have widths : width = width' := by simpa using congrArg List.length same
      subst width'
      exact congrArg (PositionalSchema.mk width) (List.ofFn_injective same)
    let typed : List (Scan.Table expected.schema Cell) := equal ▸ chunks
    return typed.map (List.map (rowPair expected))
  else throw .schemaMismatch

def writerSchema (descriptor : Descriptor) : StreamWriter.Schema :=
  ⟨if descriptor.viewFirst then .viewFirst else .intFirst,
   descriptor.integer.1, descriptor.integer.2, descriptor.binary.1, descriptor.binary.2⟩

def pack (octets : List UInt8) : KBytes :=
  Silmaril.Formats.Arrow.Writer.emitWords 1 (octets.map UInt8.toNat)

def writerBatch (rows : List Pair) : StreamWriter.BatchInput :=
  ⟨rows.length, rows.map Prod.fst, rows.map (Option.map pack ∘ Prod.snd)⟩

def octetBytes (batches : List (List Pair)) : Nat :=
  batches.foldl (fun total rows =>
    rows.foldl (fun size row => size + (row.2.map List.length).getD 0) total) 0

/-- Use the same carrier and native scope as the mixed importer. The raw octet
cap is checked before packing. The final wire cap includes framing and padding. -/
def emit {Name : Type*} (db : Database Name) (name : Name) (expected : Descriptor)
    (sizes : List Nat) (limits : Limits) : Except Error KBytes := do
  let batches ← prepare db name expected sizes
  let octets := octetBytes batches
  if octets > limits.inputBytes then throw (.octetBytes octets limits.inputBytes)
  let wire ← (StreamWriter.emit limits.mixed (writerSchema expected) (batches.map writerBatch)).mapError .writer
  if wire.len > limits.inputBytes then throw (.wireBytes wire.len limits.inputBytes)
  return wire

end Silmaril.Formats.Relational.NamedTable.MixedIpc.Export
