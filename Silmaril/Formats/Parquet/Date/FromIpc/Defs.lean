module

public import Silmaril.Formats.Arrow.DateStream.Defs
public import Silmaril.Formats.Parquet.Date.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

/-! # Checked single-batch Arrow Date32 IPC to Parquet DATE -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.FromIpc

open DateInterop

/-- Failures in stream admission precede shape and output checks. -/
inductive Error where
  | reader (cause : Arrow.DateStream.Error)
  | wrongUnit (actual : Arrow.SchemaReader.DateUnit)
  | batchCount (actual : Nat)
  | unrepresentableDay
  | requiredNull
  | writer (cause : FlatInt32Writer.Error)
  | readback (cause : Date.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- The exact flat INT32 leaf declaration associated with the Arrow field. -/
def leaf (field : Arrow.DateStream.Field) : Footer.SchemaElement :=
  ⟨some .int32, none, some (if field.nullable then .optional else .required), field.name, none⟩

/-- The single DATE group agrees with the source descriptor and every ordered slot. -/
def Matches (checked : Date.Checked) (group : Date.RowGroup)
    (field : Arrow.DateStream.Field) (dates : Arrow.DateValues.Column) : Prop :=
  checked.snapshot.groupCount = 1 ∧ group.binding.leaf = leaf field ∧
    group.binding.annotation = .logicalAndConverted ∧ group.rowCount = dates.length ∧
    group.civilSlots = dates

instance (checked : Date.Checked) (group : Date.RowGroup)
    (field : Arrow.DateStream.Field) (dates : Arrow.DateValues.Column) :
    Decidable (Matches checked group field dates) := by
  unfold Matches
  infer_instance

namespace Internal

/-- Neither a present date without a signed day word nor a required null can be dropped. -/
def pageInput (nullable : Bool) (dates : Arrow.DateValues.Column) : Except Error PlainV1Writer.Input := do
  let some slots := dates.mapM (fun date => date.mapM Date32.ofCivil?)
    | .error .unrepresentableDay
  if nullable then return .optional slots
  let some words := slots.mapM id | .error .requiredNull
  return .required words

/-- Use the checked reader once for the exact output bytes, including its group count. -/
def certify (limits : Date.Limits) (wire : Bytes) (field : Arrow.DateStream.Field)
    (dates : Arrow.DateValues.Column) : Except Error Bytes := do
  let checked ← (Date.openChecked limits wire).mapError .readback
  let group ← (checked.readGroup limits 0).mapError .readback
  if Matches checked group field dates then .ok wire else .error .readbackMismatch

end Internal

/-- Read through EOS, then require exactly one Date32 batch. An explicit empty
batch produces a zero-row group. Bytes are available only after DATE readback. -/
def convert (inputLimits : Arrow.Limits) (writerLimits : FlatInt32Writer.Limits)
    (readbackLimits : Date.Limits) (input : KBytes) : Except Error Bytes := do
  let source ← (Arrow.DateStream.read inputLimits input).mapError .reader
  if source.field.unit ≠ .day then .error (.wrongUnit source.field.unit)
  let [dates] := source.batches | .error (.batchCount source.batches.length)
  let page ← Internal.pageInput source.field.nullable dates
  let output ← (FlatInt32Writer.emitAnnotated .date writerLimits
    ⟨dates.length, [⟨source.field.name, page⟩]⟩).mapError .writer
  Internal.certify readbackLimits output.bytes source.field dates

end Silmaril.Formats.Parquet.Date.FromIpc
