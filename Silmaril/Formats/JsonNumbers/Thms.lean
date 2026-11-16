module

public import Silmaril.Formats.JsonNumbers.Defs
public import Silmaril.Formats.JsonBytes.Decide.Thms
import Silmaril.Proofs.Formats.JsonNumbers.Basic
import Silmaril.Proofs.Formats.JsonNumbers.Decide
import Silmaril.Proofs.Formats.JsonNumbers.Tokens

/-!
# JSON texts with restricted or extended number tokens: lemmas

* `language_rfc`: with the RFC 8259 number rule the grammar is `JsonBytes.language p`;
* `language_mono`, `language_scalarEscapes_le`: inclusions of number-token languages (and of
  escape profiles) are inclusions of text languages;
* `textB_iff`: the decision procedure, hence `Decidable` membership whenever membership in the
  number-token language is decidable; instances for every token language of `Defs`;
* the lattice of token languages:
  - `safeInteger ≤ int64 ≤ integerToken`, `uint64 ≤ integerToken`,
    `safeInteger ≤ binary64Integer ≤ integerToken`,
  - `integerToken ≤ integralNumber ≤ rfc ≤ withPythonInfinity ≤ withPythonNonFinite`,
  and the text languages over them (`*_text_le`);
* strictness and incomparability, each with a concrete witness: `1.0` (integral, not a lexical
  integer), `9007199254740992 = 2^53` (binary64, not safe), `9007199254740993 = 2^53 + 1` (int64,
  not binary64), `18446744073709551616 = 2^64` (binary64, not uint64), `-1` (int64, not
  uint64), `9223372036854775808 = 2^63` (uint64, not int64), `Infinity`, `NaN`;
* examples on whole texts.
-/

@[expose] public section

namespace Silmaril.Formats.JsonNumbers

open RegularExpression Silmaril.Formats.JsonBytes

/-! ## The grammar -/

/-- With RFC 8259 number tokens, the grammar is exactly the JSON byte language. -/
theorem language_rfc (p : Profile) : language p rfc = JsonBytes.language p :=
  Silmaril.Proofs.Formats.JsonNumbers.language_rfc p

/-- Fewer number tokens, fewer texts. -/
theorem language_mono (p : Profile) {N M : Language UInt8} (h : N ≤ M) :
    language p N ≤ language p M :=
  Silmaril.Proofs.Formats.JsonNumbers.language_mono' le_rfl h

/-- Scalar-value escapes are RFC escapes, for any number tokens. -/
theorem language_scalarEscapes_le (N : Language UInt8) :
    language .scalarEscapes N ≤ language .rfc8259 N :=
  Silmaril.Proofs.Formats.JsonNumbers.language_mono' string_scalarEscapes_le le_rfl

/-- Texts with number tokens in `N ≤ rfc` are JSON texts. -/
theorem language_le_json (p : Profile) {N : Language UInt8} (h : N ≤ rfc) :
    language p N ≤ JsonBytes.language p :=
  language_rfc p ▸ language_mono p h

/-! ## Decision procedure -/

theorem textB_iff {p : Profile} {N : Language UInt8} [DecidablePred (· ∈ N)] {w : List UInt8} :
    textB p N w = true ↔ w ∈ language p N :=
  Silmaril.Proofs.Formats.JsonNumbers.Decide.textB_iff

instance language.decidableMem (p : Profile) (N : Language UInt8) [DecidablePred (· ∈ N)]
    (w : List UInt8) : Decidable (w ∈ language p N) :=
  decidable_of_iff _ textB_iff

instance rfc.decidableMem : DecidablePred (· ∈ rfc) := fun w =>
  decidable_of_iff _ (rmatch_iff_matches' number w)

instance integerToken.decidableMem : DecidablePred (· ∈ integerToken) := fun w =>
  decidable_of_iff _ (rmatch_iff_matches' ((1 + char 0x2D) * int) w)

instance integralNumber.decidableMem : DecidablePred (· ∈ integralNumber) := fun w =>
  inferInstanceAs (Decidable (w ∈ rfc ∧ (value w).den = 1))

instance boundedInteger.decidableMem (lo hi : Int) : DecidablePred (· ∈ boundedInteger lo hi) :=
  fun w => inferInstanceAs (Decidable (w ∈ integerToken ∧ lo ≤ intValue w ∧ intValue w ≤ hi))

instance int64.decidableMem : DecidablePred (· ∈ int64) := boundedInteger.decidableMem _ _
instance uint64.decidableMem : DecidablePred (· ∈ uint64) := boundedInteger.decidableMem _ _
instance safeInteger.decidableMem : DecidablePred (· ∈ safeInteger) :=
  boundedInteger.decidableMem _ _

/-- Binary64 exactness, as a bounded search: some `2^e` with `e ≤ 971` divides `|n|` with a
quotient below `2^53`. -/
theorem isBinary64Integer_iff {n : Int} :
    IsBinary64Integer n ↔ ∃ e < 972, 2 ^ e ∣ n.natAbs ∧ n.natAbs / 2 ^ e < 2 ^ 53 :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.isBinary64Integer_iff

instance IsBinary64Integer.decidable (n : Int) : Decidable (IsBinary64Integer n) :=
  decidable_of_iff' _ isBinary64Integer_iff

instance binary64Integer.decidableMem : DecidablePred (· ∈ binary64Integer) := fun w =>
  inferInstanceAs (Decidable (w ∈ integerToken ∧ IsBinary64Integer (intValue w)))

instance withPythonInfinity.decidableMem : DecidablePred (· ∈ withPythonInfinity) := fun w =>
  decidable_of_iff _ (rmatch_iff_matches' _ w)

instance withPythonNonFinite.decidableMem : DecidablePred (· ∈ withPythonNonFinite) := fun w =>
  decidable_of_iff _ (rmatch_iff_matches' _ w)

/-! ## Inclusions of number-token languages -/

theorem integerToken_le_rfc : integerToken ≤ rfc :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.integerToken_le_rfc

/-- On a lexical integer, the exact value of the number token is its integer value. -/
theorem value_eq_intValue {w : List UInt8} (h : w ∈ integerToken) : value w = (intValue w : ℚ) :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.value_eq_intValue h

theorem integerToken_le_integralNumber : integerToken ≤ integralNumber :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.integerToken_le_integralNumber

theorem integralNumber_le_rfc : integralNumber ≤ rfc := fun _ h => h.1

theorem boundedInteger_le_integerToken (lo hi : Int) : boundedInteger lo hi ≤ integerToken :=
  fun _ h => h.1

theorem boundedInteger_mono {lo hi lo' hi' : Int} (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    boundedInteger lo hi ≤ boundedInteger lo' hi' :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.boundedInteger_mono hl hh

theorem safeInteger_le_int64 : safeInteger ≤ int64 :=
  boundedInteger_mono (by decide) (by decide)

theorem int64_le_integerToken : int64 ≤ integerToken := boundedInteger_le_integerToken _ _

theorem uint64_le_integerToken : uint64 ≤ integerToken := boundedInteger_le_integerToken _ _

theorem safeInteger_le_binary64Integer : safeInteger ≤ binary64Integer :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.safeInteger_le_binary64Integer

theorem binary64Integer_le_integerToken : binary64Integer ≤ integerToken := fun _ h => h.1

theorem rfc_le_withPythonInfinity : rfc ≤ withPythonInfinity :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.rfc_le_withPythonInfinity

theorem withPythonInfinity_le_withPythonNonFinite : withPythonInfinity ≤ withPythonNonFinite :=
  Silmaril.Proofs.Formats.JsonNumbers.Tokens.withPythonInfinity_le_withPythonNonFinite

/-! ## Inclusions of text languages -/

theorem integerToken_text_le (p : Profile) : language p integerToken ≤ JsonBytes.language p :=
  language_le_json p integerToken_le_rfc

theorem integralNumber_text_le (p : Profile) :
    language p integralNumber ≤ JsonBytes.language p :=
  language_le_json p integralNumber_le_rfc

theorem integerToken_text_le_integralNumber (p : Profile) :
    language p integerToken ≤ language p integralNumber :=
  language_mono p integerToken_le_integralNumber

theorem safeInteger_text_le_int64 (p : Profile) : language p safeInteger ≤ language p int64 :=
  language_mono p safeInteger_le_int64

theorem safeInteger_text_le_binary64Integer (p : Profile) :
    language p safeInteger ≤ language p binary64Integer :=
  language_mono p safeInteger_le_binary64Integer

theorem int64_text_le (p : Profile) : language p int64 ≤ language p integerToken :=
  language_mono p int64_le_integerToken

theorem uint64_text_le (p : Profile) : language p uint64 ≤ language p integerToken :=
  language_mono p uint64_le_integerToken

theorem binary64Integer_text_le (p : Profile) :
    language p binary64Integer ≤ language p integerToken :=
  language_mono p binary64Integer_le_integerToken

/-- JSON texts are texts of the Python-`Infinity` extension. -/
theorem json_le_withPythonInfinity (p : Profile) :
    JsonBytes.language p ≤ language p withPythonInfinity :=
  language_rfc p ▸ language_mono p rfc_le_withPythonInfinity

theorem withPythonInfinity_text_le (p : Profile) :
    language p withPythonInfinity ≤ language p withPythonNonFinite :=
  language_mono p withPythonInfinity_le_withPythonNonFinite

/-! ## Strictness and incomparability, with witnesses -/

/-- `1.0` has an integer value but is not a lexical integer. -/
theorem integralNumber_not_le_integerToken : ¬ integralNumber ≤ integerToken := fun h =>
  (show [0x31, 0x2E, 0x30] ∉ integerToken by decide +kernel)
    (h (show [0x31, 0x2E, 0x30] ∈ integralNumber by decide +kernel))

/-- `1.5` is an RFC number whose value is not an integer. -/
theorem rfc_not_le_integralNumber : ¬ rfc ≤ integralNumber := fun h =>
  (show [0x31, 0x2E, 0x35] ∉ integralNumber by decide +kernel)
    (h (show [0x31, 0x2E, 0x35] ∈ rfc by decide +kernel))

/-- `9007199254740992 = 2^53` is exactly a binary64 value but not a safe integer. -/
theorem binary64Integer_not_le_safeInteger : ¬ binary64Integer ≤ safeInteger := fun h =>
  (show "9007199254740992".toUTF8.toList ∉ safeInteger by decide +kernel)
    (h (show "9007199254740992".toUTF8.toList ∈ binary64Integer by decide +kernel))

/-- `9007199254740993 = 2^53 + 1` is a signed 64-bit integer that no binary64 value equals. -/
theorem int64_not_le_binary64Integer : ¬ int64 ≤ binary64Integer := fun h =>
  (show "9007199254740993".toUTF8.toList ∉ binary64Integer by decide +kernel)
    (h (show "9007199254740993".toUTF8.toList ∈ int64 by decide +kernel))

/-- `18446744073709551616 = 2^64` is exactly a binary64 value but out of the 64-bit ranges. -/
theorem binary64Integer_not_le_uint64 : ¬ binary64Integer ≤ uint64 := fun h =>
  (show "18446744073709551616".toUTF8.toList ∉ uint64 by decide +kernel)
    (h (show "18446744073709551616".toUTF8.toList ∈ binary64Integer by decide +kernel))

theorem binary64Integer_not_le_int64 : ¬ binary64Integer ≤ int64 := fun h =>
  (show "18446744073709551616".toUTF8.toList ∉ int64 by decide +kernel)
    (h (show "18446744073709551616".toUTF8.toList ∈ binary64Integer by decide +kernel))

/-- `-1` is signed, not unsigned. -/
theorem int64_not_le_uint64 : ¬ int64 ≤ uint64 := fun h =>
  (show [0x2D, 0x31] ∉ uint64 by decide +kernel)
    (h (show [0x2D, 0x31] ∈ int64 by decide +kernel))

/-- `9223372036854775808 = 2^63` is unsigned, not signed. -/
theorem uint64_not_le_int64 : ¬ uint64 ≤ int64 := fun h =>
  (show "9223372036854775808".toUTF8.toList ∉ int64 by decide +kernel)
    (h (show "9223372036854775808".toUTF8.toList ∈ uint64 by decide +kernel))

/-- `Infinity` is not an RFC 8259 number. -/
theorem withPythonInfinity_not_le_rfc : ¬ withPythonInfinity ≤ rfc := fun h =>
  (show "Infinity".toUTF8.toList ∉ rfc by decide +kernel)
    (h (show "Infinity".toUTF8.toList ∈ withPythonInfinity by decide +kernel))

/-- `NaN` is not in the `Infinity` extension. -/
theorem withPythonNonFinite_not_le_withPythonInfinity :
    ¬ withPythonNonFinite ≤ withPythonInfinity := fun h =>
  (show "NaN".toUTF8.toList ∉ withPythonInfinity by decide +kernel)
    (h (show "NaN".toUTF8.toList ∈ withPythonNonFinite by decide +kernel))

/-! ## Examples -/

section Examples

-- Tokens.
example : "-0".toUTF8.toList ∈ uint64 := by decide +kernel
-- Lexical form and value range together: `1.0e0` has value `1` but is not a lexical integer.
example : "1.0e0".toUTF8.toList ∈ integralNumber := by decide +kernel
example : "1.0e0".toUTF8.toList ∉ int64 := by decide +kernel
example : "1e0".toUTF8.toList ∉ uint64 := by decide +kernel
example : "[1.0e0]".toUTF8.toList ∈ language .rfc8259 integralNumber := by decide +kernel
example : "[1.0e0]".toUTF8.toList ∉ language .rfc8259 int64 := by decide +kernel
example : "1e2".toUTF8.toList ∈ integralNumber := by decide +kernel
example : "10e-1".toUTF8.toList ∈ integralNumber := by decide +kernel
example : "1e-1".toUTF8.toList ∉ integralNumber := by decide +kernel
example : "-9223372036854775808".toUTF8.toList ∈ int64 := by decide +kernel
example : "-9223372036854775809".toUTF8.toList ∉ int64 := by decide +kernel
example : "18446744073709551615".toUTF8.toList ∈ uint64 := by decide +kernel
example : "18446744073709551615".toUTF8.toList ∉ binary64Integer := by decide +kernel
example : "-9007199254740991".toUTF8.toList ∈ safeInteger := by decide +kernel
example : "-9007199254740992".toUTF8.toList ∉ safeInteger := by decide +kernel
example : "-Infinity".toUTF8.toList ∈ withPythonInfinity := by decide +kernel
example : "+Infinity".toUTF8.toList ∉ withPythonNonFinite := by decide +kernel
example : "-NaN".toUTF8.toList ∉ withPythonNonFinite := by decide +kernel
example : "01".toUTF8.toList ∉ integerToken := by decide +kernel

-- Whole texts.
example : "[1, -2]".toUTF8.toList ∈ language .rfc8259 int64 := by decide +kernel
example : "[1, 2.0]".toUTF8.toList ∉ language .rfc8259 integerToken := by decide +kernel
example : "[1, 2.0]".toUTF8.toList ∈ language .rfc8259 integralNumber := by decide +kernel
example : "{\"a\": 9007199254740993}".toUTF8.toList ∈ language .rfc8259 int64 := by decide +kernel
example : "{\"a\": 9007199254740993}".toUTF8.toList ∉ language .rfc8259 binary64Integer := by
  decide +kernel
example : "[NaN]".toUTF8.toList ∉ JsonBytes.language .rfc8259 := by decide +kernel
example : "[NaN]".toUTF8.toList ∈ language .rfc8259 withPythonNonFinite := by decide +kernel
example : "[NaN]".toUTF8.toList ∉ language .rfc8259 withPythonInfinity := by decide +kernel

end Examples

end Silmaril.Formats.JsonNumbers

end
