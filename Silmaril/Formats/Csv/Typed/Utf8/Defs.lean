module

public import Silmaril.Formats.Csv.Typed.Defs
public import Silmaril.Formats.Csv.Utf8.Defs

/-! # Typed nullable CSV over UTF-8 wire bytes

The ordered schema, header matching, nullable tags, and zero-column policy
come from the typed lexical API. Wire validation uses the UTF-8 CSV profile.
-/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8

/-- Original UTF-8 bytes for a string cell. The CSV wire layer separately
    checks framing and representability of the tagged field. -/
def string : CellCodec String where
  print value := some value.toByteArray.data.toList
  parse field := String.fromUTF8? ⟨field.toArray⟩

variable {Kind : Type*} {Value : Kind → Type*}

/-- Export an ordered nullable table using the UTF-8 CSV writer. -/
def encode (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (table : Table schema Value) : Except Error Bytes :=
  match exportRows schema codecs table with
  | .error error => .error error
  | .ok rows =>
    match Csv.Utf8.encode rows with
    | some bytes => .ok bytes
    | none => .error .unrepresentableWire

/-- Validate lexical UTF-8 CSV before checking the typed schema and nullable cells. -/
def decode (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (bytes : Bytes) : Except Error (Table schema Value) :=
  match Csv.Utf8.decode bytes with
  | some rows => importRows schema codecs rows
  | none => .error .malformedWire

end Silmaril.Formats.Csv.Typed.Utf8
