module

public import Silmaril.Formats.JsonEvents.Scalar.Defs
public import Silmaril.Formats.JsonEvents.Thms

/-!
# JSON scalar payloads: lemmas

* `number_valid_iff`: a number scalar is valid exactly when its lexeme is in the RFC 8259
  number grammar;
* `stringValid_rfc8259`, `stringValid_mono`: every string is valid under `rfc8259`, and validity
  under `scalarEscapes` implies validity under `rfc8259`;
* `ValidStream.decidable`: valid streams are decidable;
* examples: number lexemes, lone and paired surrogates, a valid and an invalid stream.
-/

@[expose] public section

namespace Silmaril.Formats.JsonEvents

theorem number_valid_iff {p : JsonBytes.Profile} {lexeme : List UInt8} :
    (Scalar.number lexeme).valid p = true ↔ lexeme ∈ JsonBytes.number.matches' :=
  RegularExpression.rmatch_iff_matches' _ _

theorem stringValid_rfc8259 (units : List UInt16) : stringValid .rfc8259 units = true := rfl

theorem stringValid_mono {p : JsonBytes.Profile} {units : List UInt16}
    (_ : stringValid p units = true) : stringValid .rfc8259 units = true := rfl

instance ValidStream.decidable (p : JsonBytes.Profile) (es : List (Event Key Scalar)) :
    Decidable (ValidStream p es) := by
  unfold ValidStream; infer_instance

/-! ## Examples -/

section Examples

-- Number lexemes: `-12.5e+10` and `0` are valid; `01`, `+1`, `.5` are not.
example : (Scalar.number [0x2D, 0x31, 0x32, 0x2E, 0x35, 0x65, 0x2B, 0x31, 0x30]).valid .rfc8259 =
    true := by decide
example : (Scalar.number [0x30]).valid .rfc8259 = true := by decide
example : (Scalar.number [0x30, 0x31]).valid .rfc8259 = false := by decide
example : (Scalar.number [0x2B, 0x31]).valid .rfc8259 = false := by decide
example : (Scalar.number [0x2E, 0x35]).valid .rfc8259 = false := by decide
-- A lone high surrogate: valid under `rfc8259`, not under `scalarEscapes`.
example : (Scalar.string [0xD800]).valid .rfc8259 = true := by decide
example : (Scalar.string [0xD800]).valid .scalarEscapes = false := by decide
-- A pair (U+1F600) and a reversed pair.
example : (Scalar.string [0xD83D, 0xDE00]).valid .scalarEscapes = true := by decide
example : (Scalar.string [0xDE00, 0xD83D]).valid .scalarEscapes = false := by decide
-- `{"a":[1.0,true]}` as events.
example : ValidStream .scalarEscapes [.beginObject, .key [0x61], .beginArray,
    .scalar (.number [0x31, 0x2E, 0x30]), .scalar (.bool true), .endArray, .endObject] := by
  decide
-- A key with a lone low surrogate makes the stream invalid under `scalarEscapes` only.
example : ¬ ValidStream .scalarEscapes [.beginObject, .key [0xDC00], .scalar .null, .endObject] := by
  decide
example : ValidStream .rfc8259 [.beginObject, .key [0xDC00], .scalar .null, .endObject] := by
  decide

end Examples

end Silmaril.Formats.JsonEvents

end
