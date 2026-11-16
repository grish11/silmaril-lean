module

public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Formats.JsonBytes.Decide.Thms
public import Silmaril.Semantics.Accept.Thms
public import Silmaril.Semantics.Accept.Bounded.Defs
public import Silmaril.Semantics.Accept.Order.Thms

/-!
# The UTF-8 and JSON byte languages in the `Silmaril.Accept` vocabulary

This module restates the existing results with the generic acceptance API of
`Silmaril.Semantics.Accept`, so that acceptor developments can use them without unfolding
the format definitions:

* `Utf8.decides_isWellFormed`, `JsonBytes.decides_textB`: the checkers `Accept.Decides`
  their languages, so `Accept.ofBool` of each checker *is* the language;
* `JsonBytes.decides_bytes`: the same check on `Bytes`, decided as a preimage
  (`Accept.Decides.comp`);
* `JsonBytes.decidesOn_scalarHead`: the regular check `(scalar p * ws).rmatch` decides the
  language on the domain of inputs that do not start with whitespace, `[` or `{`
  (`Accept.DecidesOn`). Outside that domain it is not a decider;
* `JsonBytes.profile_lt`: in the language preorder `Accept.LangPre profileLang` on profiles,
  `scalarEscapes` is strictly below `rfc8259` (a lone `\uD800` escape separates them);
* `JsonBytes.language_le_utf8`: every JSON text is in the UTF-8 language.

The only definitions are the domain `scalarHead` and the set-valued `profileLang`; the proofs are
short restatements.
-/

@[expose] public section

namespace Silmaril.Formats

open Silmaril.Accept

theorem Utf8.decides_isWellFormed : Decides Utf8.isWellFormed Utf8.language :=
  fun _ => Utf8.isWellFormed_iff

theorem Utf8.ofBool_isWellFormed : ofBool Utf8.isWellFormed = Utf8.language :=
  decides_iff_ofBool_eq.mp Utf8.decides_isWellFormed

namespace JsonBytes

theorem decides_textB (p : Profile) : Decides (Decide.textB p) (language p) :=
  fun _ => Decide.textB_iff

theorem ofBool_textB (p : Profile) : ofBool (Decide.textB p) = language p :=
  decides_iff_ofBool_eq.mp (decides_textB p)

/-- The check on `Bytes`: the language of `Bytes.IsJson p` is a preimage under `toList`. -/
theorem decides_bytes (p : Profile) :
    Decides (Decide.textB p ∘ Bytes.toList) {b : Bytes | b.IsJson p} :=
  (decides_textB p).comp Bytes.toList

/-- Inputs whose first byte is not whitespace, `[` or `{`. -/
def scalarHead : Set (List UInt8) :=
  {w | ∃ b t, w = b :: t ∧ ¬ IsWsByte b ∧ b ≠ 0x5B ∧ b ≠ 0x7B}

/-- The regular check decides the language on `scalarHead`, and only there is it claimed. -/
theorem decidesOn_scalarHead (p : Profile) :
    DecidesOn scalarHead (fun w => (scalar p * ws).rmatch w) (language p) := by
  rintro _ ⟨b, t, rfl, hw, ha, ho⟩
  exact (mem_language_iff_rmatch_of_head hw ha ho).symm

theorem language_le_utf8 (p : Profile) : language p ≤ Utf8.language :=
  fun _ h => language_isWellFormed h

/-- `"\uD800"`: in the RFC 8259 language, not in the scalar-escape one. -/
theorem loneSurrogate_mem : [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22] ∈ language .rfc8259 ∧
    [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22] ∉ language .scalarEscapes := by
  constructor <;> decide +kernel

/-- The language map on profiles, as sets (for `Accept.LangPre`). -/
def profileLang (p : Profile) : Set (List UInt8) := language p

/-- Profiles ordered by their languages: `scalarEscapes` is strictly finer than `rfc8259`. -/
theorem profile_lt : LangPre.of profileLang .scalarEscapes < LangPre.of profileLang .rfc8259 := by
  rw [LangPre.lt_iff]
  exact ssubset_of_subset_not_subset language_scalarEscapes_le
    fun h => loneSurrogate_mem.2 (h loneSurrogate_mem.1)

end JsonBytes

end Silmaril.Formats

end
