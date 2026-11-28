module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs

/-! Checked RLE BOOLEAN data pages with a separate length on the value stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.RleBooleanPage

structure Limits where
  page : ScalarPage.Limits
  values : Hybrid.Limits
  deriving DecidableEq, Repr

inductive Error where
  | unsupportedPhysical (physical : Footer.PhysicalType)
  | page (error : ScalarPage.Error)
  | truncatedLength
  | lengthMismatch
  | hybrid (error : Hybrid.Error)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

/-- Each V1 or V2 value section has a four-byte unsigned little-endian length
followed by exactly that many hybrid bytes, at implicit bit width one. The
hybrid byte cap applies to the payload after the length word. -/
def readValues (expected : Nat) (limits : Hybrid.Limits) (source : Bytes) :
    Except Error (List Bool) := do
  let (lengthWord, payload) ← (Hybrid.takeExact 4 source.toList).mapError fun _ => .truncatedLength
  if KBytes.leVal lengthWord = payload.length then
    let raw ← (Hybrid.decode 1 expected limits (Bytes.ofList payload)).mapError Error.hybrid
    pure (raw.map (· == 1))
  else
    throw .lengthMismatch

/-- The length word and exact width-one run stream account for the entire
scalar suffix. The decoded values are in hybrid wire order. -/
def ValuesWire (expected : Nat) (limits : Hybrid.Limits) (source : Bytes) (values : List Bool) :
    Prop :=
  expected < Hybrid.runLimit ∧ expected ≤ limits.values ∧
    ∃ (lengthWord payload : List UInt8) (raw : List Nat),
      lengthWord.length = 4 ∧ source.toList = lengthWord ++ payload ∧
      KBytes.leVal lengthWord = payload.length ∧ payload.length ≤ limits.bytes ∧
      Hybrid.Wire 1 expected payload raw ∧ values = raw.map (· == 1)

/-- The caller supplies the checked column physical type, flat page parameters
and exact on-disk body. The raw value encoding must be RLE (3). -/
def decode (physical : Footer.PhysicalType) (params : ScalarPage.Parameters)
    (limits : Limits) (source : Bytes) : Except Error (List (Option Bool)) := do
  if physical = .boolean then
    let page ← (ScalarPage.prepareFor 3 params limits.page source).mapError Error.page
    let values ← readValues (page.mask.count true) limits.values page.scalars
    (FlatPage.reconstruct page.mask values).mapError Error.slots
  else
    throw (.unsupportedPhysical physical)

end Silmaril.Formats.Parquet.RleBooleanPage
