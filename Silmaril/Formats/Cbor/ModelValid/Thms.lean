module

public import Silmaril.Formats.Cbor.ModelValid.Defs
public import Silmaril.Formats.Cbor.Value.Thms
import Silmaril.Proofs.Formats.Cbor.ModelValid

/-!
# CBOR basic validity relative to the `Cbor.Value` model: lemmas

* `encodableB_iff`: the encodability check decides `Value.Encodable`;
* `check_iff`: decides `ModelValid.language`; the `Decidable` instance;
* `language_le_wellFormed`: members are well-formed items;
* examples: UTF-8 text, duplicate keys, and the model-relative caveat (a half and a double float
  key are distinct here).
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.ModelValid

theorem encodableB_iff (v : Value) : encodableB v = true ↔ v.Encodable :=
  Silmaril.Proofs.Formats.Cbor.ModelValid.encodableB_iff v

theorem check_iff {w : List UInt8} : check w = true ↔ w ∈ language :=
  Silmaril.Proofs.Formats.Cbor.ModelValid.check_iff

instance language.decidableMem (w : List UInt8) : Decidable (w ∈ language) :=
  decidable_of_iff _ check_iff

theorem language_le_wellFormed : language ≤ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.ModelValid.language_le_wellFormed

/-! ## Examples -/

section Examples

-- `{"b": 1, "a": 2}`: keys need not be sorted for validity.
example : [0xA2, 0x61, 0x62, 0x01, 0x61, 0x61, 0x02] ∈ language := by decide +kernel
-- `{1: 2, 1: 3}`: a duplicate key is not valid.
example : [0xA2, 0x01, 0x02, 0x01, 0x03] ∉ language := by decide +kernel
-- `"\xC3("`: ill-formed UTF-8 text is not valid, also as a map key or inside a tag.
example : [0x62, 0xC3, 0x28] ∉ language := by decide +kernel
example : [0xA1, 0x62, 0xC3, 0x28, 0x00] ∉ language := by decide +kernel
example : [0xC0, 0x62, 0xC3, 0x28] ∉ language := by decide +kernel
-- Model-relative caveat: half `1.5` (`f9 3e00`) and double `1.5` are the same number in the
-- generic data model, but different `Value`s, so this map is `ModelValid` although RFC 8949
-- would call its keys duplicates.
example : [0xA2, 0xF9, 0x3E, 0x00, 0x01, 0xFB, 0x3F, 0xF8, 0, 0, 0, 0, 0, 0, 0x02] ∈ language := by
  decide +kernel
-- Only shortest-head definite encodings are members: `18 00` is a valid item, but not here.
example : [0x18, 0x00] ∉ language := by decide +kernel

end Examples

end Silmaril.Formats.Cbor.ModelValid

end
