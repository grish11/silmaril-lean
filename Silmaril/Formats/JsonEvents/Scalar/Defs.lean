module

public import Silmaril.Formats.JsonEvents.Defs
public import Silmaril.Formats.JsonBytes.Defs

/-!
# JSON scalar payloads for event streams

A concrete key and scalar type for `JsonEvents` (`Event Key Scalar`, `Tree Key Scalar`), and
what makes a payload valid under a `JsonBytes.Profile`. The choices are explicit:

* **Numbers keep their lexeme.** `Scalar.number lexeme` holds the bytes of the number as
  written. A valid lexeme is in the RFC 8259 number grammar `JsonBytes.number` (no leading
  zeros, no `+`, no bare `.`, no `NaN`/`Infinity`, no hexadecimal). No numeric value is
  computed, so `1.0`, `1` and `1e0` are different scalars. Equality, range and precision of
  numbers are a consumer's business (RFC 8259 §6).
* **Strings are UTF-16 code units.** `Scalar.string units` and keys (`Key = List UInt16`) hold
  the decoded string as code units, the unit of RFC 8259 §7's `\uXXXX` escapes. So:
  - under `Profile.rfc8259` every unit sequence is valid, lone and reversed surrogates included,
    as RFC 8259 §7 and §8.2 allow;
  - under `Profile.scalarEscapes` a valid sequence is well-formed UTF-16 (`Utf16.WellFormed`):
    every high surrogate `D800..DBFF` is immediately followed by a low surrogate `DC00..DFFF`,
    and low surrogates occur only there. This is the profile in which every string denotes a
    sequence of Unicode scalar values.
* `null` and `bool b` are the literals.

`ValidStream p es` says the stream is well-formed (`JsonEvents.language`) and every payload is
valid. `Thms` makes both decidable.

Not here: a lexer from JSON bytes to these events, or a printer from them to bytes. No theorem
relates `ValidStream` to `JsonBytes.language`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonEvents

/-- Object member names: decoded strings as UTF-16 code units. -/
abbrev Key : Type := List UInt16

/-- JSON scalars, with numbers as their lexeme and strings as UTF-16 code units. -/
inductive Scalar where
  | null
  | bool (b : Bool)
  /-- A number, as the bytes of its lexeme. -/
  | number (lexeme : List UInt8)
  /-- A string, as UTF-16 code units. -/
  | string (units : List UInt16)
  deriving DecidableEq, Repr

namespace Utf16

/-- A high (leading) surrogate `D800..DBFF`. -/
def isHigh (u : UInt16) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF

/-- A low (trailing) surrogate `DC00..DFFF`. -/
def isLow (u : UInt16) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- Well-formed UTF-16: surrogates only as high-low pairs. -/
def wellFormed : List UInt16 → Bool
  | [] => true
  | u :: rest =>
    if isHigh u then
      match rest with
      | v :: rest' => isLow v && wellFormed rest'
      | [] => false
    else !isLow u && wellFormed rest

/-- `wellFormed`, as a proposition. -/
def WellFormed (units : List UInt16) : Prop := wellFormed units = true

end Utf16

/-- A string (or key) is valid under the profile. -/
def stringValid : JsonBytes.Profile → List UInt16 → Bool
  | .rfc8259, _ => true
  | .scalarEscapes, units => Utf16.wellFormed units

/-- A scalar is valid under the profile. -/
def Scalar.valid (p : JsonBytes.Profile) : Scalar → Bool
  | .null | .bool _ => true
  | .number lexeme => JsonBytes.number.rmatch lexeme
  | .string units => stringValid p units

/-- An event's payload is valid. -/
def eventValid (p : JsonBytes.Profile) : Event Key Scalar → Bool
  | .scalar s => s.valid p
  | .key k => stringValid p k
  | _ => true

/-- A well-formed event stream all of whose payloads are valid. -/
def ValidStream (p : JsonBytes.Profile) (es : List (Event Key Scalar)) : Prop :=
  es ∈ language Key Scalar ∧ ∀ e ∈ es, eventValid p e = true

end Silmaril.Formats.JsonEvents

end
