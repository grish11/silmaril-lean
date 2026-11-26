module

public import Silmaril.Formats.Arrow.BinaryView.Batch.Defs

/-! Bind an admitted Schema to one view RecordBatch. The caller pairs the
metadata slices with the body. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Schema

def Values : Kind → Type
  | .binary => List (Option KBytes)
  | .utf8 => List (Option String)

structure Observed where
  field : Field
  values : Values field.kind

inductive Error where
  | schema (cause : MetadataError)
  | record (cause : Batch.Error)
  deriving DecidableEq, Repr

def readField (ipc : Arrow.Limits) (limits : Column.Limits) (field : Field)
    (recordMetadata body : KBytes) : Except Batch.Error (Values field.kind) :=
  match field.kind with
  | .binary => Batch.readBinary ipc limits field.nullable recordMetadata body
  | .utf8 => Batch.readUtf8 ipc limits field.nullable recordMetadata body

/-- Use the checked field kind and nullability to decode the ordered column
and retain the declared field on the result. -/
def readBatch (ipc : Arrow.Limits) (limits : Column.Limits) (schemaMetadata recordMetadata body : KBytes) :
    Except Error Observed := do
  let field ← (readMessage ipc schemaMetadata).mapError .schema
  let values ← (readField ipc limits field recordMetadata body).mapError .record
  return ⟨field, values⟩

end Silmaril.Formats.Arrow.BinaryView.Schema
