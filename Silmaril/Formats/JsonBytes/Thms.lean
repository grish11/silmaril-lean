module

public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Formats.Utf8.Thms
import Silmaril.Proofs.Formats.JsonBytes.Basic
import Silmaril.Proofs.Formats.JsonBytes.Profile

/-!
# The language of JSON texts over bytes: lemmas

* `mem_ws`: `ws` is exactly the byte lists of the four whitespace bytes;
* `language_isWellFormed`: every JSON text is well-formed UTF-8 (RFC 8259 §8.1);
* `nil_not_mem_language`: the empty input is not a JSON text;
* `mem_language_iff_of_head`: a text whose first byte is not whitespace, `[` or `{` is exactly a
  scalar followed by whitespace, a regular language; `mem_language_iff_rmatch_of_head` decides
  it with Mathlib's `rmatch`;
* worked examples: numbers, literals, strings, escapes and surrogates under both profiles,
  UTF-8 inside strings, a byte-order mark, trailing data, and nested arrays and objects.
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes

open RegularExpression Silmaril.Formats.Utf8

theorem mem_ws {w : List UInt8} : w ∈ ws.matches' ↔ ∀ b ∈ w, IsWsByte b :=
  Silmaril.Proofs.Formats.JsonBytes.mem_ws

/-- RFC 8259 §8.1: a JSON text is UTF-8. Every word of the language is well-formed UTF-8. -/
theorem language_isWellFormed {p : Profile} {w : List UInt8} (h : w ∈ language p) :
    IsWellFormed w :=
  Silmaril.Proofs.Formats.JsonBytes.language_isWellFormed h

theorem value_ne_nil {p : Profile} {w : List UInt8} (h : Value p w) : w ≠ [] :=
  Silmaril.Proofs.Formats.JsonBytes.value_ne_nil h

theorem nil_not_mem_language (p : Profile) : [] ∉ language p :=
  Silmaril.Proofs.Formats.JsonBytes.nil_not_mem_language p

/-- A value whose first byte is not whitespace, `[` or `{` is a scalar. -/
theorem value_scalar_of_head {p : Profile} {b : UInt8} {t : List UInt8}
    (h : Value p (b :: t)) (hw : ¬ IsWsByte b) (ha : b ≠ 0x5B) (ho : b ≠ 0x7B) :
    (b :: t) ∈ (scalar p).matches' :=
  Silmaril.Proofs.Formats.JsonBytes.value_scalar_of_head h hw ha ho

/-- A text that does not start with whitespace, `[` or `{` is a scalar value followed by
whitespace: membership is that of a regular language. -/
theorem mem_language_iff_of_head {p : Profile} {b : UInt8} {t : List UInt8}
    (hw : ¬ IsWsByte b) (ha : b ≠ 0x5B) (ho : b ≠ 0x7B) :
    (b :: t) ∈ language p ↔ (b :: t) ∈ (scalar p * ws).matches' :=
  Silmaril.Proofs.Formats.JsonBytes.mem_language_iff_of_head hw ha ho

/-- The executable form of `mem_language_iff_of_head`. -/
theorem mem_language_iff_rmatch_of_head {p : Profile} {b : UInt8} {t : List UInt8}
    (hw : ¬ IsWsByte b) (ha : b ≠ 0x5B) (ho : b ≠ 0x7B) :
    (b :: t) ∈ language p ↔ (scalar p * ws).rmatch (b :: t) = true :=
  (mem_language_iff_of_head hw ha ho).trans (rmatch_iff_matches' _ _).symm

/-- Membership in a lexical rule, from the executable matcher. -/
theorem mem_of_rmatch {r : RegularExpression UInt8} {w : List UInt8} (h : r.rmatch w = true) :
    w ∈ r.matches' :=
  (rmatch_iff_matches' r w).mp h

/-! ## Examples

Each example is one complete input. Comments show the bytes as text; `·` marks a byte that is
not printable. -/

section Examples

/-- Decide a text that starts with a byte other than whitespace, `[` and `{`. -/
local macro "json_head" : tactic =>
  `(tactic| first
    | exact (mem_language_iff_rmatch_of_head (by decide) (by decide) (by decide)).mpr
        (by decide +kernel)
    | exact fun h => absurd ((mem_language_iff_rmatch_of_head (by decide) (by decide)
        (by decide)).mp h) (by decide +kernel))

/-! ### Numbers (§6) -/

example : [0x30] ∈ language .rfc8259 := by json_head                          -- 0
example : [0x2D, 0x30] ∈ language .rfc8259 := by json_head                    -- -0
example : [0x2D, 0x31, 0x32, 0x2E, 0x35, 0x65, 0x2B, 0x31, 0x30] ∈ language .rfc8259 := by
  json_head                                                                   -- -12.5e+10
example : [0x31, 0x45, 0x34, 0x30, 0x30] ∈ language .rfc8259 := by json_head  -- 1E400
example : [0x30, 0x2E, 0x30, 0x65, 0x2D, 0x30] ∈ language .rfc8259 := by json_head  -- 0.0e-0
example : [0x31, 0x20, 0x0A] ∈ language .rfc8259 := by json_head            -- 1 followed by ws
example : [0x30, 0x31] ∉ language .rfc8259 := by json_head                    -- 01
example : [0x2B, 0x31] ∉ language .rfc8259 := by json_head                    -- +1
example : [0x2E, 0x35] ∉ language .rfc8259 := by json_head                    -- .5
example : [0x35, 0x2E] ∉ language .rfc8259 := by json_head                    -- 5.
example : [0x31, 0x65] ∉ language .rfc8259 := by json_head                    -- 1e
example : [0x2D] ∉ language .rfc8259 := by json_head                          -- -
example : [0x2D, 0x2D, 0x31] ∉ language .rfc8259 := by json_head              -- --1
example : [0x30, 0x78, 0x31, 0x46] ∉ language .rfc8259 := by json_head        -- 0x1F
example : [0x4E, 0x61, 0x4E] ∉ language .rfc8259 := by json_head              -- NaN
example : [0x31, 0x20, 0x32] ∉ language .rfc8259 := by json_head              -- 1 2

/-! ### Literals (§3) -/

example : [0x74, 0x72, 0x75, 0x65] ∈ language .rfc8259 := by json_head        -- true
example : [0x6E, 0x75, 0x6C, 0x6C, 0x09] ∈ language .scalarEscapes := by json_head  -- null·
example : [0x74, 0x72, 0x75] ∉ language .rfc8259 := by json_head              -- tru
example : [0x54, 0x72, 0x75, 0x65] ∉ language .rfc8259 := by json_head        -- True
example : [0x74, 0x72, 0x75, 0x65, 0x78] ∉ language .rfc8259 := by json_head  -- truex

/-! ### Strings, escapes and UTF-8 (§7, §8.1) -/

example : [0x22, 0x22] ∈ language .scalarEscapes := by json_head              -- ""
-- "é", raw UTF-8 `C3 A9`.
example : [0x22, 0xC3, 0xA9, 0x22] ∈ language .scalarEscapes := by json_head
-- "😀", raw UTF-8 `F0 9F 98 80`.
example : [0x22, 0xF0, 0x9F, 0x98, 0x80, 0x22] ∈ language .scalarEscapes := by json_head
-- "\"\\\/\n"
example : [0x22, 0x5C, 0x22, 0x5C, 0x5C, 0x5C, 0x2F, 0x5C, 0x6E, 0x22] ∈ language .rfc8259 := by
  json_head
-- "é" and "é": hex digits in either case.
example : [0x22, 0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x22] ∈ language .scalarEscapes := by
  json_head
example : [0x22, 0x5C, 0x75, 0x30, 0x30, 0x45, 0x39, 0x22] ∈ language .scalarEscapes := by
  json_head
-- "😀", a surrogate pair: valid in both profiles.
example : [0x22, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x22] ∈
    language .scalarEscapes := by json_head
example : [0x22, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x22] ∈
    language .rfc8259 := by json_head
-- "\uD800", a lone high surrogate: RFC 8259 grammar only.
example : [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22] ∈ language .rfc8259 := by json_head
example : [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22] ∉ language .scalarEscapes := by
  json_head
-- "\uDE00\uD83D", a reversed pair: RFC 8259 grammar only.
example : [0x22, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x22] ∈
    language .rfc8259 := by json_head
example : [0x22, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x22] ∉
    language .scalarEscapes := by json_head
-- "\ud800a": a high surrogate escape followed by a character, not by a low surrogate escape.
example : [0x22, 0x5C, 0x75, 0x64, 0x38, 0x30, 0x30, 0x61, 0x22] ∉ language .scalarEscapes := by
  json_head
-- Unterminated "abc, unknown escape "\a", short escape "\u12", "\U0041".
example : [0x22, 0x61, 0x62, 0x63] ∉ language .rfc8259 := by json_head
example : [0x22, 0x5C, 0x61, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0x5C, 0x75, 0x31, 0x32, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0x5C, 0x55, 0x30, 0x30, 0x34, 0x31, 0x22] ∉ language .rfc8259 := by json_head
-- A raw line feed or tab inside a string must be escaped.
example : [0x22, 0x0A, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0x09, 0x22] ∉ language .rfc8259 := by json_head
-- Ill-formed UTF-8 in a string: overlong `C0 AF`, encoded surrogate `ED A0 80`, `FF`,
-- a truncated `E2 82`.
example : [0x22, 0xC0, 0xAF, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0xED, 0xA0, 0x80, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0xFF, 0x22] ∉ language .rfc8259 := by json_head
example : [0x22, 0xE2, 0x82, 0x22] ∉ language .rfc8259 := by json_head
-- Single quotes are not string delimiters.
example : [0x27, 0x61, 0x27] ∉ language .rfc8259 := by json_head

/-! ### Whole input -/

-- A byte-order mark before `1` (`EF BB BF 31`) is not part of the language.
example : [0xEF, 0xBB, 0xBF, 0x31] ∉ language .rfc8259 := by json_head
-- A NUL after the value.
example : [0x31, 0x00] ∉ language .rfc8259 := by json_head
example : ([] : List UInt8) ∉ language .rfc8259 := nil_not_mem_language _

/-! ### Arrays and objects (§4, §5), by explicit derivation -/

-- ` [ ] `: whitespace before, inside and after.
example : [0x20, 0x5B, 0x20, 0x5D, 0x20] ∈ language .rfc8259 :=
  ⟨[0x20], [0x5B, 0x20, 0x5D], [0x20], mem_of_rmatch (by decide +kernel),
    .emptyArray (a := [0x5B, 0x20]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
      (mem_of_rmatch (by decide +kernel)),
    mem_of_rmatch (by decide +kernel), rfl⟩

-- `[[]]`
example : [0x5B, 0x5B, 0x5D, 0x5D] ∈ language .rfc8259 :=
  ⟨[], _, [], mem_of_rmatch (by decide +kernel),
    .array (a := [0x5B]) (xs := [0x5B, 0x5D]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
      (.one (.emptyArray (a := [0x5B]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
        (mem_of_rmatch (by decide +kernel))))
      (mem_of_rmatch (by decide +kernel)),
    mem_of_rmatch (by decide +kernel), rfl⟩

-- `{"a":[1, true],"a":null}`: duplicate names are grammatical (§4).
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x5B, 0x31, 0x2C, 0x20, 0x74, 0x72, 0x75, 0x65, 0x5D,
    0x2C, 0x22, 0x61, 0x22, 0x3A, 0x6E, 0x75, 0x6C, 0x6C, 0x7D] ∈ language .scalarEscapes :=
  ⟨[], _, [], mem_of_rmatch (by decide +kernel),
    .object (a := [0x7B]) (b := [0x7D]) (mem_of_rmatch (by decide +kernel))
      (.cons (k := [0x22, 0x61, 0x22]) (c := [0x3A]) (s := [0x2C])
        (mem_of_rmatch (by decide +kernel)) (mem_of_rmatch (by decide +kernel))
        (.array (a := [0x5B]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
          (.cons (v := [0x31]) (s := [0x2C, 0x20]) (.scalar (mem_of_rmatch (by decide +kernel)))
            (mem_of_rmatch (by decide +kernel))
            (.one (.scalar (w := [0x74, 0x72, 0x75, 0x65]) (mem_of_rmatch (by decide +kernel)))))
          (mem_of_rmatch (by decide +kernel)))
        (mem_of_rmatch (by decide +kernel))
        (.one (k := [0x22, 0x61, 0x22]) (c := [0x3A]) (mem_of_rmatch (by decide +kernel))
          (mem_of_rmatch (by decide +kernel))
          (.scalar (w := [0x6E, 0x75, 0x6C, 0x6C]) (mem_of_rmatch (by decide +kernel)))))
      (mem_of_rmatch (by decide +kernel)),
    mem_of_rmatch (by decide +kernel), rfl⟩

-- The same bytes as a `Bytes` value.
example : (Bytes.ofList [0x5B, 0x5B, 0x5D, 0x5D]).IsJson .rfc8259 := by
  rw [Bytes.IsJson, Bytes.toList_ofList]
  exact ⟨[], _, [], mem_of_rmatch (by decide +kernel),
    .array (a := [0x5B]) (xs := [0x5B, 0x5D]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
      (.one (.emptyArray (a := [0x5B]) (b := [0x5D]) (mem_of_rmatch (by decide +kernel))
        (mem_of_rmatch (by decide +kernel))))
      (mem_of_rmatch (by decide +kernel)),
    mem_of_rmatch (by decide +kernel), rfl⟩

end Examples

end Silmaril.Formats.JsonBytes

/-! ## The scalar-escape profile refines the RFC 8259 profile

Every text that is valid under `Profile.scalarEscapes` is valid under `Profile.rfc8259`. The
inclusion is strict: the lone high surrogate escape `"\uD800"` above is in `language .rfc8259`
and not in `language .scalarEscapes`. -/

namespace Silmaril.Formats.JsonBytes

open scoped Computability

/-- One scalar-escape `char` is a sequence of RFC 8259 `char`s (a surrogate pair is two). -/
theorem strChar_scalarEscapes_le :
    (strChar .scalarEscapes).matches' ≤ (strChar .rfc8259).matches'∗ :=
  Silmaril.Proofs.Formats.JsonBytes.Profile.strChar_le

theorem string_scalarEscapes_le : (string .scalarEscapes).matches' ≤ (string .rfc8259).matches' :=
  Silmaril.Proofs.Formats.JsonBytes.Profile.string_le

theorem value_rfc8259_of_scalarEscapes {w : List UInt8} (h : Value .scalarEscapes w) :
    Value .rfc8259 w :=
  Silmaril.Proofs.Formats.JsonBytes.Profile.value_rfc8259 h

theorem language_scalarEscapes_le : language .scalarEscapes ≤ language .rfc8259 :=
  Silmaril.Proofs.Formats.JsonBytes.Profile.language_le

end Silmaril.Formats.JsonBytes

end
