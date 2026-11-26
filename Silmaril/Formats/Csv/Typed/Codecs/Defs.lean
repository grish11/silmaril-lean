module

public import Silmaril.Formats.Csv.Typed.Defs
public import Silmaril.Formats.Spki.Defs

/-! # Cell codecs for signed Int32 and CSV-representable UTF-8 text -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Codecs

/-- Canonical decimal bytes denoting the given mathematical integer. -/
def DecimalSpelling (field : Field) (n : Int) : Prop :=
  if n < 0 then
    ∃ magnitude, field = 0x2D :: magnitude ∧ Spki.IsDecimal magnitude ∧
      Spki.digitsValue magnitude = n.natAbs
  else Spki.IsDecimal field ∧ Spki.digitsValue field = n.natAbs

/-- Canonical signed decimal, with a minus sign only on negative values. -/
def int32Text (value : Int32) : Field :=
  let digits := Spki.decimal value.toInt.natAbs
  if value.toInt < 0 then 0x2D :: digits else digits

namespace Internal

/-- Evaluate the candidate before validating its canonical spelling. -/
def signedValue : Field → Int
  | [] => 0
  | b :: bs =>
    if b = 0x2D then -(Int.ofNat (Spki.digitsValue bs))
    else Int.ofNat (Spki.digitsValue (b :: bs))

end Internal

/-- Check the Int32 range before constructing the value, then check the exact
    spelling. At most eleven input bytes reach numeric evaluation. -/
def parseInt32 (field : Field) : Option Int32 :=
  if field.length ≤ 11 then
    let n := Internal.signedValue field
    if h : Int32.minValue.toInt ≤ n ∧ n ≤ Int32.maxValue.toInt then
      let value := Int32.ofIntLE n h.1 h.2
      if int32Text value = field then some value else none
    else none
  else none

/-- Total canonical decimal printing and checked parsing for signed Int32. -/
def int32 : CellCodec Int32 := ⟨some ∘ int32Text, parseInt32⟩

/-- Text bytes admitted by the RFC 4180 wire codec after CSV unquoting. -/
def textBytesOK (field : Field) : Bool := field.all Csv.Internal.fieldData

/-- Use the original UTF-8 bytes when the CSV alphabet can carry them. -/
def utf8 : CellCodec String where
  print value :=
    let bytes := value.toByteArray.data.toList
    if textBytesOK bytes then some bytes else none
  parse field :=
    if textBytesOK field then String.fromUTF8? ⟨field.toArray⟩ else none

end Silmaril.Formats.Csv.Typed.Codecs
