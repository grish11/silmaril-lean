module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.ByteStreamSplit.Defs

/-! Checked BYTE_STREAM_SPLIT data pages for flat scalar columns. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteStreamSplitPage

structure Limits where
  page : ScalarPage.Limits
  scalars : ByteStreamSplit.Limits
  deriving DecidableEq, Repr

inductive Error where
  | schemaMismatch
  | unsupportedPhysical (physical : Footer.PhysicalType)
  | invalidFixedWidth
  | page (error : ScalarPage.Error)
  | scalar (error : ByteStreamSplit.Error)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

/-- The schema's width field supplies the positive fixed width. Numeric widths
are determined by their physical types. -/
inductive KindFor (typeLength : Option Int) : Footer.PhysicalType → ByteStreamSplit.Kind → Prop where
  | int32 : KindFor typeLength .int32 .int32
  | int64 : KindFor typeLength .int64 .int64
  | float : KindFor typeLength .float .floatBits
  | double : KindFor typeLength .double .doubleBits
  | fixed {width : Nat} (declared : typeLength = some (width : Int))
      (positive : 0 < width) (bounded : width < ByteStreamSplit.signedSizeLimit) :
      KindFor typeLength .fixedLenByteArray (.fixedLenBytes width)

structure Selection (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (kind : ByteStreamSplit.Kind) : Prop where
  physicalType : leaf.physicalType = some physical
  leafArity : leaf.numChildren.getD 0 = 0
  kindMatches : KindFor leaf.typeLength physical kind

/-- Select from the matched footer leaf and column metadata physical type.
A fixed-length width comes exclusively from the leaf's `typeLength`. -/
def selectKind (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType) :
    Except Error ByteStreamSplit.Kind :=
  if leaf.physicalType ≠ some physical ∨ leaf.numChildren.getD 0 ≠ 0 then .error .schemaMismatch
  else
    match physical with
    | .int32 => .ok .int32
    | .int64 => .ok .int64
    | .float => .ok .floatBits
    | .double => .ok .doubleBits
    | .fixedLenByteArray =>
      match leaf.typeLength with
      | some width =>
        if 0 < width ∧ width < (ByteStreamSplit.signedSizeLimit : Int) then .ok (.fixedLenBytes width.toNat)
        else .error .invalidFixedWidth
      | none => .error .invalidFixedWidth
    | _ => .error (.unsupportedPhysical physical)

/-- Carries the checked physical kind and its typed nullable slots. -/
structure Decoded where
  kind : ByteStreamSplit.Kind
  slots : List (Option kind.Value)

/-- The caller supplies the matched footer leaf, column physical type, and
checked flat page parameters. The raw page ID must be BYTE_STREAM_SPLIT (`9`). -/
def decode (leaf : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (params : ScalarPage.Parameters) (limits : Limits) (source : Bytes) : Except Error Decoded := do
  let kind ← selectKind leaf physical
  let page ← (ScalarPage.prepareFor 9 params limits.page source).mapError Error.page
  let values ← (ByteStreamSplit.decode kind limits.scalars (page.mask.count true) page.scalars).mapError
    Error.scalar
  let slots ← (FlatPage.reconstruct page.mask values).mapError Error.slots
  pure ⟨kind, slots⟩

end Silmaril.Formats.Parquet.ByteStreamSplitPage
