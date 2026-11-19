module

public import Silmaril.Formats.Cbor.Drisl.Debug.Defs
public import Silmaril.Formats.Cbor.Drisl.Convert.Defs
public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWire.Encoding.Defs

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl.Debug

def Codec.withCid {Input Link : Type} (number : Input → JsonWire.Decimal)
    (readNumber? : JsonWire.Decimal → Option Input) (cid : CidCodec Link) :
    Codec Input JsonWire.Decimal Link :=
  ⟨number, readNumber?, cid.render, cid.read?⟩

def drislCodec (profile : CidProfile := .any) : Codec Number JsonWire.Decimal (Cid profile) :=
  Codec.withCid Number.toDecimal Number.readDecimal? (Cid.codec profile)

def atprotoCodec (profile : CidProfile := .any) : Codec Int64 JsonWire.Decimal (Cid profile) :=
  Codec.withCid (intDecimal ∘ Int64.toInt) decimalI64? (Cid.codec profile)

def linkFreeCodec {Numeric : Type} (number : Numeric → JsonWire.Decimal)
    (readNumber? : JsonWire.Decimal → Option Numeric) : Codec Numeric JsonWire.Decimal Empty :=
  ⟨number, readNumber?, Empty.elim, fun _ => none⟩

def jsonWithBytesCodec : Codec JsonWire.Decimal JsonWire.Decimal Empty := linkFreeCodec id some

def jsonWithBytesI64Codec : Codec Int64 JsonWire.Decimal Empty :=
  linkFreeCodec (intDecimal ∘ Int64.toInt) decimalI64?

def toWire {index : JsonIx} : RawSyn String (Atom JsonWire.Decimal) index → JsonWire.Syn JsonWire.Decimal index
  | .scalar .null => .scalar none
  | .scalar (.bool value) => .scalar (some (.bool value))
  | .scalar (.number value) => .scalar (some (.number value))
  | .scalar (.string value) => .scalar (some (.string (JsonWire.stringUnits value)))
  | .list items => .list (toWire items)
  | .map entries => .map (toWire entries)
  | .nil => .nil
  | .cons value tail => .cons (toWire value) (toWire tail)
  | .objNil => .objNil
  | .objCons name value tail => .objCons (JsonWire.stringUnits name) (toWire value) (toWire tail)

def ofWire? (value : JsonWire.Ast JsonWire.Decimal) : Option Tree :=
  JsonWithBytes.traverse? JsonWire.unitsString? (fun
    | none => some .null
    | some (.bool value) => some (.bool value)
    | some (.number value) => some (.number value)
    | some (.string value) => .string <$> JsonWire.unitsString? value) value

/-- JSON-debug texts are complete RFC JSON, with Unicode scalar strings and
unique names. Escaping is a choice of format, not guessed from the input. -/
def parseText? {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link) (policy : Escape)
    (bytes : Bytes) : Option (RawJson (Scalar Input Link)) := do
  let tree ← ofWire? (← JsonWire.parse? bytes)
  let value ← decode? codec policy tree
  if JsonWithBytes.uniqueKeys value then some value else none

def renderText {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link) (policy : Escape)
    (value : RawJson (Scalar Input Link)) : Bytes :=
  JsonWire.encode (toWire (encode codec policy value))

def textLanguage {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link) (policy : Escape) :
    Language UInt8 := { bytes | (parseText? codec policy ⟨bytes.toByteArray⟩).isSome }

def AtprotoTextRep (profile : CidProfile) (policy : Escape) (bytes : Bytes)
    (value : OrderedATProto (Cid profile)) : Prop :=
  parseText? (atprotoCodec profile) policy bytes = some value

/-- Interpret an ATProto debug document as JSON-with-bytes only when its
semantics contain no links. No codec casts or alternate JSON reader. -/
def parseI64Text? (profile : CidProfile) (policy : Escape) (bytes : Bytes) : Option JsonWithBytes.OrderedI64 :=
  (parseText? (atprotoCodec profile) policy bytes).bind removeLinks?

def drislTextLanguage (policy : Escape) (profile : CidProfile := .any) : Language UInt8 :=
  textLanguage (drislCodec profile) policy

def atprotoTextLanguage (policy : Escape) (profile : CidProfile := .any) : Language UInt8 :=
  textLanguage (atprotoCodec profile) policy

def jsonWithBytesTextLanguage (policy : Escape) : Language UInt8 :=
  textLanguage jsonWithBytesCodec policy

def jsonWithBytesI64TextLanguage (policy : Escape) : Language UInt8 :=
  { bytes | (parseI64Text? .any policy (Bytes.ofList bytes)).isSome }

def renderJsonWithBytes (policy : Escape) (value : JsonWithBytes.Ordered) : Bytes :=
  renderText jsonWithBytesCodec policy (value.mapScalar Scalar.data)

def parseJsonWithBytes? (policy : Escape) (bytes : Bytes) : Option JsonWithBytes.Ordered :=
  (parseText? jsonWithBytesCodec policy bytes).bind removeLinks?

end Silmaril.Formats.Cbor.Drisl.Debug
