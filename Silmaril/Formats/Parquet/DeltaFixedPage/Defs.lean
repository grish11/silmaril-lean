module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.DeltaByteArray.Defs

/-! Checked DELTA_BYTE_ARRAY for FIXED_LEN_BYTE_ARRAY, with the width bound to
the schema and each reconstructed value. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DeltaFixedPage

structure Limits where
  page : ScalarPage.Limits
  values : DeltaByteArray.Limits
  deriving DecidableEq, Repr

inductive Error where
  | schemaMismatch
  | invalidWidth
  | widthLimit
  | decodedByteLimit
  | widthMismatch
  | page (error : ScalarPage.Error)
  | scalar (error : DeltaByteArray.Error)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

structure WidthFor (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (width : Nat) : Prop where
  fixedPhysical : physical = .fixedLenByteArray
  matchesLeaf : leaf.physicalType = some physical
  leafArity : leaf.numChildren.getD 0 = 0
  declared : leaf.typeLength = some (width : Int)
  positive : 0 < width
  bounded : width < DeltaByteArray.valueLengthLimit

/-- Read the positive signed-i32 width from the matched footer leaf. -/
def selectWidth (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType) : Except Error Nat :=
  if physical ≠ .fixedLenByteArray ∨ leaf.physicalType ≠ some physical ∨
      leaf.numChildren.getD 0 ≠ 0 then
    .error .schemaMismatch
  else
    match leaf.typeLength with
    | none => .error .invalidWidth
    | some width =>
      if 0 < width ∧ width < (DeltaByteArray.valueLengthLimit : Int) then .ok width.toNat
      else .error .invalidWidth

/-- After checking the caller's value cap, use the declared width as the
reconstruction bound. Each suffix is itself at most that wide. -/
def limitsForWidth (width : Nat) (limits : DeltaByteArray.Limits) : DeltaByteArray.Limits :=
  { limits with
    valueBytes := min width limits.valueBytes
    suffixes := { limits.suffixes with valueBytes := min width limits.suffixes.valueBytes } }

/-- Decode one exact fixed-width scalar slice. Short reconstructions fail the
final width check and wide reconstructions fail the codec's size checks. -/
def readValues (width expected : Nat) (limits : DeltaByteArray.Limits) (source : Bytes) :
    Except Error (List Bytes) :=
  if 0 < width ∧ width < DeltaByteArray.valueLengthLimit then
    if limits.valueBytes < width then .error .widthLimit
    else if limits.decodedBytes < expected * width then .error .decodedByteLimit
    else do
      let values ← (DeltaByteArray.decode (limitsForWidth width limits) expected source).mapError Error.scalar
      if values.all (fun value => value.length == width) then pure values
      else throw .widthMismatch
  else .error .invalidWidth

/-- An exact fixed-width interpretation of the two length
streams and suffix bytes. The suffixes and output are in wire order. -/
structure ValuesWire (width expected : Nat) (limits : DeltaByteArray.Limits) (source : Bytes)
    (values : List Bytes) : Prop where
  count : values.length = expected
  widths : ∀ value ∈ values, value.length = width
  total : (values.map Bytes.length).sum = expected * width
  streams :
    ∃ (prefixStream suffixStream : DeltaBinaryPacked.Stream) (payload : List UInt8) (suffixes : List Bytes),
      source.toList = prefixStream.wire ++ suffixStream.wire ++ payload ∧
      source.length = prefixStream.wire.length + suffixStream.wire.length + (suffixes.map Bytes.length).sum ∧
      prefixStream.Valid .int32 limits.prefixes expected ∧
      suffixStream.Valid .int32 limits.suffixes.lengths expected ∧
      DeltaLengthByteArray.Assembled (limitsForWidth width limits).suffixes
        (suffixStream.reconstruct .int32) payload suffixes ∧
      (prefixStream.reconstruct .int32).headD 0 = 0 ∧
      DeltaByteArray.Reconstruction width limits.decodedBytes .empty
        (prefixStream.reconstruct .int32) suffixes values

/-- Given the matched leaf, column physical type, checked flat parameters and
exact on-disk V1/V2 body, decode only the present encoding-7 values. -/
def decode (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (params : ScalarPage.Parameters) (limits : Limits) (source : Bytes) :
    Except Error (List (Option Bytes)) := do
  let width ← selectWidth leaf physical
  let page ← (ScalarPage.prepareFor 7 params limits.page source).mapError Error.page
  let values ← readValues width (page.mask.count true) limits.values page.scalars
  (FlatPage.reconstruct page.mask values).mapError Error.slots

end Silmaril.Formats.Parquet.DeltaFixedPage
