module

public import Mathlib.Algebra.Field.Rat
public import Silmaril.Formats.JsonBytes.Defs

/-!
# JSON texts with restricted or extended number tokens

RFC 8259 fixes the syntax of a number (`[ minus ] int [ frac ] [ exp ]`) but no range or
precision (§6). Many producers and consumers accept only part of it, or more than it. This module
makes each such number domain an explicit byte language of *number tokens*, and defines the JSON
texts whose number tokens all lie in it.

* `language p N`: the RFC 8259 grammar of `Silmaril.Formats.JsonBytes` (escape profile `p`), with
  the `number` rule replaced by the token language `N`. At `N = rfc` it is exactly
  `JsonBytes.language p` (`language_rfc`), it is monotone in `N` (`language_mono`), and the
  scalar-escape profile is contained in the RFC profile (`language_scalarEscapes_le`). So every
  inclusion of token languages below is an inclusion of text languages.

## Number-token languages

All of the following are sets of byte strings; the docs of each say exactly which.

* `rfc`: RFC 8259 §6, the `number` rule.
* `integerToken`: *lexical* integers, `[ minus ] int`: no fraction and no exponent. `-0` is one
  (the grammar allows it) and denotes `0`.
* `integralNumber`: RFC numbers whose *value* is an integer, whatever their spelling: `1.0`,
  `1e2`, `10e-1` and `-0.0` are in it, `1.5` and `1e-1` are not. `integerToken` is strictly
  smaller (`integerToken_le_integralNumber`).
* Bounded lexical integers (`boundedInteger lo hi`): lexical integers whose value lies in
  `[lo, hi]`. The bound is on the value, so `-0` is in every range containing `0`, including the
  unsigned one, and leading zeros cannot occur (the `int` rule forbids them).
  - `int64`: `[-2^63, 2^63 - 1]`, the two's-complement 64-bit range.
  - `uint64`: `[0, 2^64 - 1]`, the unsigned 64-bit range.
  - `safeInteger`: `[-(2^53 - 1), 2^53 - 1]`, the range outside of which, says I-JSON (RFC 7493
    §2.2), a sender cannot expect a receiver to treat an integer as an exact value. This is only
    that numeric restriction: I-JSON itself also restricts strings, member names and non-integer
    numbers, and is not defined here.
* `binary64Integer`: lexical integers whose value is *exactly* an IEEE 754 binary64 number
  (`IsBinary64Integer`): `m · 2^e` with `m < 2^53` and `0 ≤ e ≤ 971`. This is not a bound: it
  contains `2^53` and `2^64` and `(2^53 - 1) · 2^971` (the largest finite double), and omits
  `2^53 + 1`. Every safe integer is in it (`safeInteger_le_binary64Integer`), not conversely.
* Non-finite extensions, **not JSON**: RFC 8259 §6 says "Numeric values that cannot be
  represented in the grammar below (such as Infinity and NaN) are not permitted." Python's `json`
  module nevertheless writes the three tokens `Infinity`, `-Infinity` and `NaN` in number
  position (`json.dumps` with its default `allow_nan=True`) and reads them back (`json.loads`),
  and documents this as "not JSON specification compliant". `withPythonInfinity` is `rfc` plus `Infinity` and
  `-Infinity`; `withPythonNonFinite` adds `NaN`. No other spelling (`+Infinity`, `inf`, `-NaN`)
  is included; JSON5 and other dialects get their own languages.

## Values

`intValue` is the value of a lexical integer, and `value` that of any RFC number token, as an
exact rational: the digits, the decimal point and the exponent read in base ten, with no
rounding. On bytes outside the token languages they are junk values.

References (`references.bib`): `rfc8259` (§6), `rfc7493` (§2.2), `ieee-754-2019` (§3.3),
`python-json`.
Lemmas: `Silmaril.Formats.JsonNumbers.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonNumbers

open RegularExpression Silmaril.Formats.Utf8 Silmaril.Formats.JsonBytes

/-! ## The grammar with a number-token language -/

/-- The values without nested structure other than numbers: `false`, `null`, `true`, strings. -/
def literal (p : Profile) : RegularExpression UInt8 := falseLit + nullLit + trueLit + string p

mutual

/-- `value`, with number tokens from `N`. -/
inductive Value (p : Profile) (N : Language UInt8) : List UInt8 → Prop
  | literal {w} : w ∈ (literal p).matches' → Value p N w
  | number {w} : w ∈ N → Value p N w
  | emptyArray {a b} : a ∈ beginArray.matches' → b ∈ endArray.matches' → Value p N (a ++ b)
  | array {a xs b} : a ∈ beginArray.matches' → Elements p N xs → b ∈ endArray.matches' →
      Value p N (a ++ xs ++ b)
  | emptyObject {a b} : a ∈ beginObject.matches' → b ∈ endObject.matches' → Value p N (a ++ b)
  | object {a ms b} : a ∈ beginObject.matches' → Members p N ms → b ∈ endObject.matches' →
      Value p N (a ++ ms ++ b)

/-- `value *( value-separator value )`. -/
inductive Elements (p : Profile) (N : Language UInt8) : List UInt8 → Prop
  | one {v} : Value p N v → Elements p N v
  | cons {v s vs} : Value p N v → s ∈ valueSeparator.matches' → Elements p N vs →
      Elements p N (v ++ s ++ vs)

/-- `member *( value-separator member )`. -/
inductive Members (p : Profile) (N : Language UInt8) : List UInt8 → Prop
  | one {k c v} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → Value p N v →
      Members p N (k ++ c ++ v)
  | cons {k c v s ms} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → Value p N v →
      s ∈ valueSeparator.matches' → Members p N ms → Members p N (k ++ c ++ v ++ s ++ ms)

end

/-- `ws value ws`, the whole input, with number tokens from `N`. -/
def Text (p : Profile) (N : Language UInt8) (w : List UInt8) : Prop :=
  ∃ a v b, a ∈ ws.matches' ∧ Value p N v ∧ b ∈ ws.matches' ∧ w = a ++ v ++ b

/-- The JSON texts (escape profile `p`) whose number tokens are all in `N`. -/
def language (p : Profile) (N : Language UInt8) : Language UInt8 := {w | Text p N w}

/-! ## Values of number tokens -/

/-- An ASCII decimal digit. -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The value of a string of decimal digits. -/
def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - 0x30)) 0

/-- The value of a lexical integer `[ minus ] int`. -/
def intValue : List UInt8 → Int
  | 0x2D :: ds => -(digitsValue ds : Int)
  | ds => digitsValue ds

/-- The value of an exponent part after `e`/`E`: `[ minus / plus ] 1*DIGIT`. -/
def expValue : List UInt8 → Int
  | 0x2D :: ds => -(digitsValue ds : Int)
  | 0x2B :: ds => digitsValue ds
  | ds => digitsValue ds

/-- The parts of an unsigned number token: integer digits, fraction digits, exponent. -/
def unsignedParts (r : List UInt8) : List UInt8 × List UInt8 × Int :=
  let i := r.takeWhile isDigit
  match r.dropWhile isDigit with
  | 0x2E :: t => (i, t.takeWhile isDigit, match t.dropWhile isDigit with
      | _ :: x => expValue x
      | [] => 0)
  | _ :: x => (i, [], expValue x)
  | [] => (i, [], 0)

/-- The exact value of an unsigned number token `int [ frac ] [ exp ]`:
`digits(int frac) · 10 ^ (exp - length frac)`. -/
def unsignedValue (r : List UInt8) : ℚ :=
  let (i, f, x) := unsignedParts r
  (digitsValue (i ++ f) : ℚ) * (10 : ℚ) ^ (x - f.length)

/-- The exact value of an RFC 8259 number token. -/
def value : List UInt8 → ℚ
  | 0x2D :: r => -unsignedValue r
  | r => unsignedValue r

/-- An integer is exactly an IEEE 754 binary64 value: `m · 2^e` with a 53-bit significand
`m` and `0 ≤ e ≤ 971` (IEEE 754-2019 §3.3, binary64: `p = 53`, `emax = 1023`; an integer-valued
finite double has such a form, the largest being `(2^53 - 1) · 2^971`). -/
def IsBinary64Integer (n : Int) : Prop := ∃ e ≤ 971, ∃ m < 2 ^ 53, n.natAbs = m * 2 ^ e

/-! ## Number-token languages -/

/-- RFC 8259 §6 `number`. -/
def rfc : Language UInt8 := number.matches'

/-- Lexical integers `[ minus ] int`: no fraction, no exponent. -/
def integerToken : Language UInt8 := ((1 + char 0x2D) * int).matches'

/-- RFC numbers whose exact value is an integer (`1`, `1.0`, `1e2`, `-0.0`). -/
def integralNumber : Language UInt8 := {w | w ∈ rfc ∧ (value w).den = 1}

/-- Lexical integers with value in `[lo, hi]`. -/
def boundedInteger (lo hi : Int) : Language UInt8 :=
  {w | w ∈ integerToken ∧ lo ≤ intValue w ∧ intValue w ≤ hi}

/-- Lexical integers in the signed 64-bit range `[-2^63, 2^63 - 1]`. -/
def int64 : Language UInt8 := boundedInteger (-2 ^ 63) (2 ^ 63 - 1)

/-- Lexical integers in the unsigned 64-bit range `[0, 2^64 - 1]` (`-0` included). -/
def uint64 : Language UInt8 := boundedInteger 0 (2 ^ 64 - 1)

/-- Lexical integers in I-JSON's interoperable range `[-(2^53 - 1), 2^53 - 1]`
(RFC 7493 §2.2). -/
def safeInteger : Language UInt8 := boundedInteger (-(2 ^ 53 - 1)) (2 ^ 53 - 1)

/-- Lexical integers whose value is exactly a binary64 number. -/
def binary64Integer : Language UInt8 := {w | w ∈ integerToken ∧ IsBinary64Integer (intValue w)}

/-- `Infinity`. -/
def infinityLit : RegularExpression UInt8 := word [0x49, 0x6E, 0x66, 0x69, 0x6E, 0x69, 0x74, 0x79]

/-- `NaN`. -/
def nanLit : RegularExpression UInt8 := word [0x4E, 0x61, 0x4E]

/-- **Not JSON.** RFC numbers and Python `json`'s `Infinity` and `-Infinity`. -/
def withPythonInfinity : Language UInt8 := (number + (1 + char 0x2D) * infinityLit).matches'

/-- **Not JSON.** RFC numbers and Python `json`'s `Infinity`, `-Infinity` and `NaN`. -/
def withPythonNonFinite : Language UInt8 :=
  (number + (1 + char 0x2D) * infinityLit + nanLit).matches'

/-! ## A decision procedure

The rules of `language` tried on every split of the input, as in
`Silmaril.Formats.JsonBytes.Decide`, with number tokens checked by the decidable membership in
`N`. A reference oracle for small kernel-checked examples, not a parser
(`Silmaril.Formats.JsonNumbers.Thms`: `textB_iff`). -/

/-- Every way to cut a list into a prefix and a suffix. -/
def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map fun ab => (x :: ab.1, ab.2)

section Decide

variable (p : Profile) (N : Language UInt8) [DecidablePred (· ∈ N)]

mutual

/-- `Value p N w`, with fuel. -/
def valueB : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w => (literal p).rmatch w || decide (w ∈ N) ||
      (splits w).any fun ar =>
        (beginArray.rmatch ar.1 && (splits ar.2).any fun mb =>
          endArray.rmatch mb.2 && (mb.1.isEmpty || elementsB n mb.1)) ||
        (beginObject.rmatch ar.1 && (splits ar.2).any fun mb =>
          endObject.rmatch mb.2 && (mb.1.isEmpty || membersB n mb.1))

/-- `Elements p N w`, with fuel. -/
def elementsB : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w => valueB n w ||
      (splits w).any fun vr => valueB n vr.1 && (splits vr.2).any fun sx =>
        valueSeparator.rmatch sx.1 && elementsB n sx.2

/-- `Members p N w`, with fuel. -/
def membersB : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w =>
      (splits w).any fun mr =>
        ((splits mr.1).any fun kr => (string p).rmatch kr.1 && (splits kr.2).any fun cv =>
          nameSeparator.rmatch cv.1 && valueB n cv.2) &&
        (mr.2.isEmpty || (splits mr.2).any fun sm =>
          valueSeparator.rmatch sm.1 && membersB n sm.2)

end

/-- `Text p N w`: whitespace, a value with enough fuel, whitespace. -/
def textB (w : List UInt8) : Bool :=
  (splits w).any fun ar => ws.rmatch ar.1 && (splits ar.2).any fun vb =>
    ws.rmatch vb.2 && valueB p N (2 * vb.1.length + 1) vb.1

end Decide

end Silmaril.Formats.JsonNumbers

end
