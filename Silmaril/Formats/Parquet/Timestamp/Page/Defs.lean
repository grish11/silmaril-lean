module

public import Silmaril.Formats.Parquet.Timestamp.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! # Bounded nullable timestamp slots from a standalone PLAIN data page -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Page

open Numeric.Timestamp

inductive Error where
  | schemaLevels
  | unsupportedPage
  | scalar (error : ScalarPage.Error)
  deriving DecidableEq, Repr

/-- The two flat layouts admitted by the INT64 timestamp binder. -/
def leafLevels? (leaf : Footer.SchemaElement) : Option FlatPage.LevelSchema :=
  if leaf.physicalType = some .int64 ∧ leaf.numChildren.getD 0 = 0 then
    match leaf.repetition with
    | some .required => some ⟨0, 0⟩
    | some .optional => some ⟨0, 1⟩
    | _ => none
  else none

/-- Check the supplied schema levels against the leaf and take every page
    count, length and encoding field from the checked header. -/
def parameters (leaf : Footer.SchemaElement) (levels : FlatPage.LevelSchema) (codec : Int)
    (header : Parquet.Page.Header) : Except Error ScalarPage.Parameters :=
  if leafLevels? leaf = some levels then
    let sizes : ScalarPage.Sizes := ⟨header.compressedSize, header.uncompressedSize⟩
    match header.kind with
    | .dataV1 info =>
      .ok ⟨sizes, levels, info.numValues, codec, info.encoding,
        .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩
    | .dataV2 info =>
      .ok ⟨sizes, levels, info.numValues, codec, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩
    | _ => .error .unsupportedPage
  else .error .schemaLevels

abbrev Value (binding : Binding) := Ticks binding.descriptor.kind binding.descriptor.unit.tickUnit

/-- Interpret the checked scalar slots in order and retain their signed counts.
    The caller supplies the associated header, codec, levels and exact body. -/
def decode (binding : Binding) (levels : FlatPage.LevelSchema) (codec : Int)
    (header : Parquet.Page.Header) (limits : ScalarPage.Limits) (body : Bytes) :
    Except Error (List (Option (Value binding))) := do
  let params ← parameters binding.leaf levels codec header
  let slots ← (ScalarPage.decode .int64 params limits body).mapError .scalar
  return slots.map (Option.map binding.descriptor.decode)

end Silmaril.Formats.Parquet.Timestamp.Page
