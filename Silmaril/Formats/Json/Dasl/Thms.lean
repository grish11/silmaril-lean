module
public import Silmaril.Formats.Json.Dasl.Defs
public import Silmaril.Formats.Dasl.Presentation.Thms
import Silmaril.Proofs.Formats.Json.Dasl.Basic

@[expose] public section
namespace Silmaril.Formats.JsonDasl
open Dasl Dasl.Encode

theorem i64Number_value {input : Int} {output : Int64} (encoded : i64Number? input = some output) :
    output.toInt = input := Proofs.Formats.Json.Dasl.i64_value encoded

theorem decimal_roundtrip (number : JsonWire.Decimal) : decodeDecimal? (encodeDecimal number) = some number :=
  Proofs.Formats.Json.Dasl.decimal_roundtrip number

theorem scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWire.Scalar N) :
    decodeScalar? numbers (encodeScalar numbers value) = some value :=
  Proofs.Formats.Json.Dasl.scalar_roundtrip numbers value

theorem bytes_scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWire.Scalar N ⊕ ByteArray) :
    decodeBytesScalar? numbers (encodeBytesScalar numbers value) = some value :=
  Proofs.Formats.Json.Dasl.bytes_scalar_roundtrip numbers value

theorem ordered_scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWithBytes.Scalar N) :
    decodeOrderedScalar? numbers (encodeOrderedScalar numbers value) = some value :=
  Proofs.Formats.Json.Dasl.ordered_scalar_roundtrip numbers value

theorem raw_roundtrip {Key Scalar : Type} (keys : TotalCodec Key Value) (scalar : TotalCodec Scalar Value)
    {sort : JsonIx} (ast : RawSyn Key Scalar sort) :
    decodeRaw? keys scalar sort (encodeRaw keys scalar ast) = some ast :=
  Proofs.Formats.Json.Dasl.raw_roundtrip keys scalar ast

def decimalCodec : TotalCodec JsonWire.Decimal Value := ⟨encodeDecimal, decodeDecimal?, decimal_roundtrip⟩

def scalarCodec {N : Type} (numbers : TotalCodec N Value) : TotalCodec (JsonWire.Scalar N) Value :=
  ⟨encodeScalar numbers, decodeScalar? numbers, scalar_roundtrip numbers⟩

def bytesScalarCodec {N : Type} (numbers : TotalCodec N Value) :
    TotalCodec (JsonWire.Scalar N ⊕ ByteArray) Value :=
  ⟨encodeBytesScalar numbers, decodeBytesScalar? numbers, bytes_scalar_roundtrip numbers⟩

def rawCodec {Key Scalar : Type} (keys : TotalCodec Key Value) (scalar : TotalCodec Scalar Value) :
    TotalCodec (KeyedRawJson Key Scalar) Value :=
  ⟨encodeRaw keys scalar, decodeRaw? keys scalar .val, raw_roundtrip keys scalar⟩

def codec {N : Type} (numbers : TotalCodec N Value) : TotalCodec (JsonWire.Ast N) Value :=
  rawCodec unitsCodec (scalarCodec numbers)

def codecBytes {N : Type} (numbers : TotalCodec N Value) : TotalCodec (BytesAst N) Value :=
  rawCodec unitsCodec (bytesScalarCodec numbers)

/-- Bridge the existing Unicode-string AST with bytes without changing the raw UTF-16 profiles. -/
def orderedWithBytes {N : Type} (numbers : TotalCodec N Value) : TotalCodec (JsonWithBytes.Ordered N) Value :=
  rawCodec text ⟨encodeOrderedScalar numbers, decodeOrderedScalar? numbers, ordered_scalar_roundtrip numbers⟩

abbrev safe := codec safeCodec
abbrev i64 := codec signed
abbrev rfc := codec decimalCodec
abbrev safeBytes := codecBytes safeCodec
abbrev i64Bytes := codecBytes signed
abbrev rfcBytes := codecBytes decimalCodec

theorem includeBytes_commutes {N : Type} (numbers : TotalCodec N Value) (ast : JsonWire.Ast N) :
    ((codecBytes numbers).intoAbstract (includeBytes ast)).val = ((codec numbers).intoAbstract ast).val :=
  Proofs.Formats.Json.Dasl.include_embed _ _ (fun _ => rfl) ast

theorem parse_includeBytes_commutes {N Wire : Type} (numbers : TotalCodec N Value)
    (parse : Wire → Option (JsonWire.Ast N)) (input : Wire) :
    ((codecBytes numbers).parseAbstract? (fun wire => (parse wire).map includeBytes) input).map Subtype.val =
      ((codec numbers).parseAbstract? parse input).map Subtype.val := by
  change (((parse input).map includeBytes).map (codecBytes numbers).intoAbstract).map Subtype.val =
    ((parse input).map (codec numbers).intoAbstract).map Subtype.val
  cases parse input with
  | none => rfl
  | some ast => exact congrArg some (includeBytes_commutes numbers ast)

def parseSafeAbstract? : Bytes → Option safe.Abstract := safe.parseAbstract? parseSafe?
def parseI64Abstract? : Bytes → Option i64.Abstract := i64.parseAbstract? parseI64?
def parseRfcAbstract? : Bytes → Option rfc.Abstract := rfc.parseAbstract? JsonWire.parse?

theorem safe_per : syntaxPER parseSafeAbstract? = syntaxPER parseSafe? := safe.parseAbstract_per parseSafe?
theorem i64_per : syntaxPER parseI64Abstract? = syntaxPER parseI64? := i64.parseAbstract_per parseI64?
theorem rfc_per : syntaxPER parseRfcAbstract? = syntaxPER JsonWire.parse? := rfc.parseAbstract_per JsonWire.parse?

end Silmaril.Formats.JsonDasl
