module

public import Silmaril.Formats.Cbor.Drisl.Convert.Defs

/-! The CBOR model permits any order of distinct string keys. The canonical
byte reader separately enforces deterministic heads and DRISL map ordering. -/

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

structure CborCodec (Numeric : Type) where
  number : Numeric → Value
  readNumber? : Value → Option Numeric

def Integer.toCbor : Integer → Value
  | .uint argument => .uint argument.toNat
  | .nint argument => .nint argument.toNat

def i64Cbor : CborCodec Int64 where
  number value := match value.toInt with
    | .ofNat amount => .uint amount
    | .negSucc amount => .nint amount
  readNumber?
    | .uint amount => int64? (.ofNat amount)
    | .nint amount => int64? (.negSucc amount)
    | _ => none

def drislCbor : CborCodec Number where
  number
    | .integer integral => integral.toCbor
    | .float bits => .float 8 bits.val
  readNumber?
    | .uint amount => .integer <$> Integer.ofInt? (.ofNat amount)
    | .nint amount => .integer <$> Integer.ofInt? (.negSucc amount)
    | .float 8 bits => if valid : okFloat64 bits = true then some (.float ⟨bits, valid⟩) else none
    | _ => none

def emptyCid : CidCodec Empty := ⟨Empty.elim, fun _ => none⟩

def utf8Value (text : String) : Value := .text text.toUTF8.data.toList

def emitLeaf {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link) :
    Scalar Numeric Link → Value
  | .data .null => .null
  | .data (.bool value) => if value then .true else .false
  | .data (.string value) => utf8Value value
  | .data (.bytes value) => .bytes value
  | .data (.number value) => numeric.number value
  | .link value => .tag 42 (.bytes (0 :: cid.bytes value))

def emitModel {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (canonical : Bool) : {index : JsonIx} → RawSyn String (Scalar Numeric Link) index →
    (match index with | .val => Value | .arr => List Value | .obj => List (Value × Value))
  | _, .scalar leaf => emitLeaf numeric cid leaf
  | _, .list items => .array (emitModel numeric cid canonical items)
  | _, .map entries =>
    let fields := emitModel numeric cid canonical entries
    .map (if canonical then fields.mergeSort (fun left right => !lexLt right.1.encode left.1.encode) else fields)
  | _, .nil => []
  | _, .cons value tail => emitModel numeric cid canonical value :: emitModel numeric cid canonical tail
  | _, .objNil => []
  | _, .objCons name value tail => (utf8Value name, emitModel numeric cid canonical value) ::
      emitModel numeric cid canonical tail

def readCborLeaf? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link) :
    Value → Option (Scalar Numeric Link)
  | .simple 20 => some (.data (.bool false))
  | .simple 21 => some (.data (.bool true))
  | .simple 22 => some (.data .null)
  | .bytes value => some (.data (.bytes value))
  | .text bytes => (.data ∘ JsonWithBytes.Scalar.string) <$> String.fromUTF8? bytes.toByteArray
  | .tag 42 (.bytes (0 :: bytes)) => .link <$> cid.parse? bytes
  | value => (.data ∘ JsonWithBytes.Scalar.number) <$> numeric.readNumber? value

mutual

def readModel? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    : Value → Option (RawJson (Scalar Numeric Link))
  | .array items => .list <$> readItems? numeric cid items
  | .map entries => .map <$> readEntries? numeric cid entries
  | value => .scalar <$> readCborLeaf? numeric cid value

def readItems? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    : List Value → Option (RawSyn String (Scalar Numeric Link) .arr)
  | [] => some .nil
  | value :: tail => return .cons (← readModel? numeric cid value) (← readItems? numeric cid tail)

def readEntries? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    : List (Value × Value) → Option (RawSyn String (Scalar Numeric Link) .obj)
  | [] => some .objNil
  | (.text bytes, value) :: tail =>
    return .objCons (← String.fromUTF8? bytes.toByteArray) (← readModel? numeric cid value)
      (← readEntries? numeric cid tail)
  | _ => none

end

/-- Membership in the value model uses decoded CBOR structures, not bytes. -/
def interpretCbor? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (value : Value) : Option (RawJson (Scalar Numeric Link)) := do
  let tree ← readModel? numeric cid value
  if JsonWithBytes.uniqueKeys tree then some tree else none

def cborValues {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link) : Set Value :=
  { value | (interpretCbor? numeric cid value).isSome }

def drislValues (profile : CidProfile := .any) : Set Value := cborValues drislCbor (Cid.codec profile)
def atprotoValues (profile : CidProfile := .any) : Set Value := cborValues i64Cbor (Cid.codec profile)
def interpretI64Cbor? (profile : CidProfile) (value : Value) : Option JsonWithBytes.OrderedI64 :=
  (interpretCbor? i64Cbor (Cid.codec profile) value).bind removeLinks?

def i64WithBytesValues : Set Value := { value | (interpretI64Cbor? .any value).isSome }

/-- Link-free DRISL values have an exact decimal interpretation. This is not
the image of preferred integer-first decimal lowering (e.g. integral doubles). -/
def representableJsonWithBytesValues : Set Value := cborValues drislCbor emptyCid

mutual

def canonicalMaps : Value → Bool
  | .array items => canonicalItems items
  | .map entries => strictlySorted (entries.map fun entry => entry.1.encode) && canonicalEntries entries
  | _ => true

def canonicalItems : List Value → Bool
  | [] => true
  | value :: tail => canonicalMaps value && canonicalItems tail

def canonicalEntries : List (Value × Value) → Bool
  | [] => true
  | (_, value) :: tail => canonicalMaps value && canonicalEntries tail

end

/-- Check the complete existing CBOR decoder output, exact bytes, key order,
and the profile's interpretation. Definite but overlong heads are rejected. -/
def parseCbor? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (bytes : List UInt8) : Option (RawJson (Scalar Numeric Link)) := do
  let value ← Cbor.decode bytes
  if value.encode = bytes ∧ canonicalMaps value = true then interpretCbor? numeric cid value else none

def canonicalCbor {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link) : Language UInt8 :=
  { bytes | (parseCbor? numeric cid bytes).isSome }

def drislCborLanguage (profile : CidProfile := .any) : Language UInt8 := canonicalCbor drislCbor (Cid.codec profile)
def atprotoCborLanguage (profile : CidProfile := .any) : Language UInt8 := canonicalCbor i64Cbor (Cid.codec profile)

def parseI64Cbor? (profile : CidProfile) (bytes : List UInt8) : Option JsonWithBytes.OrderedI64 :=
  (parseCbor? i64Cbor (Cid.codec profile) bytes).bind removeLinks?

def i64WithBytesCborLanguage : Language UInt8 := { bytes | (parseI64Cbor? .any bytes).isSome }
def representableJsonWithBytesCborLanguage : Language UInt8 := canonicalCbor drislCbor emptyCid

/-- Sort by CBOR key encoding, then check the resulting wire representation.
Reject duplicates and invalid external codec outputs. -/
def renderCbor? {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (value : RawJson (Scalar Numeric Link)) : Option (List UInt8) :=
  let bytes := (emitModel numeric cid true value).encode
  if (parseCbor? numeric cid bytes).isSome then some bytes else none

def renderJsonWithBytesCbor? (value : JsonWithBytes.Ordered) : Option (List UInt8) :=
  (fromJsonWithBytes? value).bind (renderCbor? drislCbor emptyCid)

def parseJsonWithBytesCbor? (bytes : List UInt8) : Option JsonWithBytes.Ordered :=
  (parseCbor? drislCbor emptyCid bytes).bind toJsonWithBytes?

end Silmaril.Formats.Cbor.Drisl
