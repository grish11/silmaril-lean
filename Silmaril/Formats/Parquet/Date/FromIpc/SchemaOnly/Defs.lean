module

public import Silmaril.Formats.Parquet.Date.FromIpc.Defs

/-! # Opt-in schema-only Date32 IPC to zero-group Parquet DATE -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly

structure Limits where
  maxFileBytes : Nat
  footer : Footer.Limits := {}

/-- The checked descriptor and the exact lack of row groups and data bytes. -/
def Matches (checked : Date.Checked) (field : Arrow.DateStream.Field) : Prop :=
  checked.snapshot.footer.start = 4 ∧ checked.snapshot.groupCount = 0 ∧
    checked.snapshot.metadata.numRows = 0 ∧ checked.binding.leaf = FromIpc.leaf field ∧
    checked.binding.annotation = .logicalAndConverted

instance (checked : Date.Checked) (field : Arrow.DateStream.Field) :
    Decidable (Matches checked field) := by
  unfold Matches
  infer_instance

namespace Internal

open FlatInt32Writer

def fileLimit (limits : Limits) : Nat := min limits.maxFileBytes (2^63 - 1)

def footerLimit (limits : Limits) : Nat :=
  min (min limits.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - 12)

def columnIndex (field : Arrow.DateStream.Field) : Compact.ColumnIndex :=
  ⟨field.name, field.nullable, ⟨4, 4⟩⟩

def frame (footer : Bytes) : Bytes :=
  ((Footer.magic.append footer).append (Bytes.ofList (KBytes.unpack 4 footer.length))).append
    Footer.magic

/-- The existing Compact group-list serializer writes a zero row total and
an empty group list. The footer follows the leading magic directly. -/
def encode (limits : Limits) (field : Arrow.DateStream.Field) : Except FromIpc.Error Bytes := do
  let compact := limits.footer.compact
  let longestName := max (Compact.schemaRoot 1).name.utf8ByteSize field.name.utf8ByteSize
  if compact.maxCollectionSize < 2 || compact.maxBinaryBytes < longestName then
    .error (.writer .schemaOrCount)
  if fileLimit limits < 12 then .error (.writer .fileLimit)
  let cap := footerLimit limits
  let footer ← (Compact.encodeGroups .date cap [columnIndex field] []).mapError (.writer ∘ .compact)
  if cap < footer.length then .error (.writer .invariant)
  return frame footer

end Internal

/-- Read the exact Date32 schema and EOS, and require zero record batches.
An explicit zero-row record still counts as a batch. -/
def convert (inputLimits : Arrow.Limits) (writerLimits : Limits)
    (readbackLimits : Date.Limits) (input : KBytes) : Except FromIpc.Error Bytes := do
  let source ← (Arrow.DateStream.read inputLimits input).mapError .reader
  if source.field.unit ≠ .day then .error (.wrongUnit source.field.unit)
  let [] := source.batches | .error (.batchCount source.batches.length)
  let wire ← Internal.encode writerLimits source.field
  let checked ← (Date.openChecked readbackLimits wire).mapError .readback
  if Matches checked source.field then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly
