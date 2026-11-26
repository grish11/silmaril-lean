module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.DeltaByteArray.Defs

/-! Checked dispatch for flat V1/V2 data pages with Parquet delta scalar encodings. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DeltaPage

inductive Kind where
  | signed (physical : DeltaBinaryPacked.Physical)
  | byteArray
  deriving DecidableEq, Repr

def Kind.physicalType : Kind → Footer.PhysicalType
  | .signed .int32 => .int32
  | .signed .int64 => .int64
  | .byteArray => .byteArray

def Kind.ofPhysical? : Footer.PhysicalType → Option Kind
  | .int32 => some (.signed .int32)
  | .int64 => some (.signed .int64)
  | .byteArray => some .byteArray
  | _ => none

abbrev Kind.Value : Kind → Type
  | .signed physical => physical.Value
  | .byteArray => Bytes

/-- The type index carries the admitted encoding and physical-type pairing. -/
inductive Encoding : Kind → Type where
  | binaryPacked (physical : DeltaBinaryPacked.Physical) : Encoding (.signed physical)
  | lengthByteArray : Encoding .byteArray
  | byteArray : Encoding .byteArray

def Encoding.id {kind : Kind} : Encoding kind → Int
  | .binaryPacked _ => 5
  | .lengthByteArray => 6
  | .byteArray => 7

def Encoding.ofId? : (kind : Kind) → Int → Option (Encoding kind)
  | .signed physical, id => if id = 5 then some (.binaryPacked physical) else none
  | .byteArray, id =>
    if id = 6 then some .lengthByteArray else if id = 7 then some .byteArray else none

structure Limits where
  page : ScalarPage.Limits
  binaryPacked : DeltaBinaryPacked.Limits
  lengthByteArray : DeltaLengthByteArray.Limits
  byteArray : DeltaByteArray.Limits
  deriving DecidableEq, Repr

inductive Error where
  | unsupportedEncoding (kind : Kind) (id : Int)
  | page (error : ScalarPage.Error)
  | binaryPacked (error : DeltaBinaryPacked.Error)
  | lengthByteArray (error : DeltaLengthByteArray.Error)
  | byteArray (error : DeltaByteArray.Error)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

/-- Read exactly the supplied scalar slice with the selected codec's limits. -/
def Encoding.read {kind : Kind} : Encoding kind → Limits → Nat → Bytes → Except Error (List kind.Value)
  | .binaryPacked physical, limits, count, source =>
    (DeltaBinaryPacked.decode physical limits.binaryPacked count source).mapError Error.binaryPacked
  | .lengthByteArray, limits, count, source =>
    (DeltaLengthByteArray.decode limits.lengthByteArray count source).mapError Error.lengthByteArray
  | .byteArray, limits, count, source =>
    (DeltaByteArray.decode limits.byteArray count source).mapError Error.byteArray

/-- Prepare the exact on-disk body, decode only present values, and rebuild the checked slots. -/
def decode (kind : Kind) (params : ScalarPage.Parameters) (limits : Limits) (source : Bytes) :
    Except Error (List (Option kind.Value)) := do
  let some encoding := Encoding.ofId? kind params.encoding | throw (.unsupportedEncoding kind params.encoding)
  let page ← (ScalarPage.prepareFor encoding.id params limits.page source).mapError Error.page
  let values ← encoding.read limits (page.mask.count true) page.scalars
  (FlatPage.reconstruct page.mask values).mapError Error.slots

end Silmaril.Formats.Parquet.DeltaPage
