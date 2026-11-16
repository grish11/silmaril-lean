module

public import Silmaril.Formats.Cbor.Deterministic.Defs
public import Silmaril.Formats.Cbor.Drisl.Thms
import Silmaril.Proofs.Formats.Cbor.Deterministic

/-!
# Deterministically encoded CBOR, relative to a float rule: lemmas

* `check_iff`: decide, re-encode; the `Decidable` instance;
* `language_le_wellFormed`, `value_unique`: members are well-formed and determine their value;
* `language_mono`: a weaker float rule or no UTF-8 requirement gives a larger language;
* `drisl_le`: every DRISL profile (any boundary, link rule or integer range) is deterministic
  relative to `FloatRule.only64` with UTF-8 text;
* examples. They separate the three float rules, and show non-shortest heads, unsorted keys and
  indefinite lengths rejected.

Every statement holds *relative to the supplied float rule*. None of them is a claim of RFC 8949
§4.2.1 preferred-float determinism (see the module documentation of `Defs`).
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.Deterministic

theorem check_iff {P : DetProfile} {w : List UInt8} : check P w = true ↔ w ∈ language P :=
  Silmaril.Proofs.Formats.Cbor.Deterministic.check_iff

instance language.decidableMem (P : DetProfile) (w : List UInt8) : Decidable (w ∈ language P) :=
  decidable_of_iff _ check_iff

theorem language_le_wellFormed (P : DetProfile) : language P ≤ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.Deterministic.language_le_wellFormed P

theorem value_unique {P : DetProfile} {v v' : Value} (h : detOk P v = true)
    (h' : detOk P v' = true) (he : v.encode = v'.encode) : v = v' :=
  Silmaril.Proofs.Formats.Cbor.Deterministic.value_unique h h' he

theorem language_mono {P Q : DetProfile}
    (hf : ∀ w b, P.floatOk w b = true → Q.floatOk w b = true)
    (hu : Q.utf8Text = true → P.utf8Text = true) : language P ≤ language Q :=
  Silmaril.Proofs.Formats.Cbor.Deterministic.language_mono hf hu

/-- Every DRISL profile is deterministic relative to 64-bit floats, with UTF-8 text. -/
theorem drisl_le (P : Drisl.Profile) : Drisl.language P ≤ language ⟨FloatRule.only64, true⟩ :=
  Silmaril.Proofs.Formats.Cbor.Deterministic.drisl_le P

/-! ## Examples -/

section Examples

/-- No floats, UTF-8 text: the float-free core-deterministic items. -/
def noFloats : DetProfile := ⟨FloatRule.none, true⟩
/-- 64-bit floats only (CBOR/c-42, DRISL style). -/
def only64 : DetProfile := ⟨FloatRule.only64, true⟩
/-- Any float width (deterministic except in floats). -/
def anyFloat : DetProfile := ⟨FloatRule.any, true⟩

-- `{1: 2, "a": [0]}` sorted by encodings (`01` < `61 61`); any tag is allowed (tag 1 here).
example : [0xA2, 0x01, 0x02, 0x61, 0x61, 0x81, 0xC1, 0x00] ∈ language noFloats := by decide +kernel
-- Unsorted keys, a duplicate key, a non-shortest head, an indefinite array.
example : [0xA2, 0x61, 0x61, 0x00, 0x01, 0x02] ∉ language noFloats := by decide +kernel
example : [0xA2, 0x01, 0x02, 0x01, 0x03] ∉ language noFloats := by decide +kernel
example : [0x18, 0x00] ∉ language noFloats := by decide +kernel
example : [0x9F, 0xFF] ∉ language noFloats := by decide +kernel
-- Half-precision 1.0 (`f9 3c00`): allowed only by the `any` rule.
example : [0xF9, 0x3C, 0x00] ∈ language anyFloat := by decide +kernel
example : [0xF9, 0x3C, 0x00] ∉ language only64 := by decide +kernel
example : [0xF9, 0x3C, 0x00] ∉ language noFloats := by decide +kernel
-- Double 1.0: allowed by `only64` and `any`. (RFC 8949 preferred serialization would require
-- the half-precision form, which is why `only64` is not RFC §4.2.1.)
example : [0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] ∈ language only64 := by decide +kernel
-- Ill-formed UTF-8 text is rejected only when the profile asks for UTF-8.
example : [0x62, 0xC3, 0x28] ∉ language noFloats := by decide +kernel
example : [0x62, 0xC3, 0x28] ∈ language ⟨FloatRule.none, false⟩ := by decide +kernel

end Examples

end Silmaril.Formats.Cbor.Deterministic

end
