module

public import Silmaril.Formats.Ascii.Defs
public import Silmaril.Formats.JsonBytes.Decide.Thms
import Silmaril.Proofs.Formats.Ascii.Basic

/-!
# The language of ASCII bytes: lemmas

* `isAscii_iff`: the executable check decides the language, hence the `Decidable` instances
  (also for `printable`, `json p` and `Bytes.IsAscii`);
* `printable_le`, `language_le_utf8`: printable ASCII ⊆ ASCII ⊆ well-formed UTF-8;
* `mem_language_iff_exists_chars`: the ASCII sequences are exactly the UTF-8 encodings of
  strings of characters `U+0000..U+007F`;
* `json_le`, `json_le_ascii`, `json_le_utf8`: ASCII-only JSON is JSON, ASCII and UTF-8;
* examples, including JSON texts inside and outside `json`.
-/

@[expose] public section

namespace Silmaril.Formats.Ascii

theorem mem_language {w : List UInt8} : w ∈ language ↔ ∀ b ∈ w, b < 0x80 := Iff.rfl

/-- The executable check decides the language. -/
theorem isAscii_iff {w : List UInt8} : isAscii w = true ↔ w ∈ language :=
  Silmaril.Proofs.Formats.Ascii.isAscii_iff

instance language.decidableMem (w : List UInt8) : Decidable (w ∈ language) :=
  decidable_of_iff _ isAscii_iff

instance printable.decidableMem (w : List UInt8) : Decidable (w ∈ printable) :=
  inferInstanceAs (Decidable (∀ b ∈ w, IsPrintableByte b))

instance json.decidableMem (p : JsonBytes.Profile) (w : List UInt8) : Decidable (w ∈ json p) :=
  inferInstanceAs (Decidable (w ∈ JsonBytes.language p ∧ w ∈ language))

instance _root_.Silmaril.Formats.Bytes.IsAscii.decidable (b : Bytes) : Decidable b.IsAscii :=
  language.decidableMem b.toList

theorem printable_le : printable ≤ language := fun _ h b hb =>
  UInt8.lt_of_le_of_lt (h b hb).2 (by decide)

/-- ASCII bytes are well-formed UTF-8. -/
theorem language_le_utf8 : language ≤ Utf8.language := fun _ h => Utf8.isWellFormed_of_ascii h

/-- The ASCII sequences are exactly the UTF-8 encodings of strings of `U+0000..U+007F`. -/
theorem mem_language_iff_exists_chars {w : List UInt8} :
    w ∈ language ↔
      ∃ cs : List Char, (∀ c ∈ cs, c.toNat < 0x80) ∧ w = cs.flatMap String.utf8EncodeChar :=
  Silmaril.Proofs.Formats.Ascii.mem_language_iff_exists_chars

theorem json_le (p : JsonBytes.Profile) : json p ≤ JsonBytes.language p := fun _ h => h.1

theorem json_le_ascii (p : JsonBytes.Profile) : json p ≤ language := fun _ h => h.2

theorem json_le_utf8 (p : JsonBytes.Profile) : json p ≤ Utf8.language :=
  le_trans (json_le_ascii p) language_le_utf8

/-! ## Examples -/

section Examples

example : [0x00, 0x41, 0x7F] ∈ language := by decide +kernel
example : [0x41, 0x80] ∉ language := by decide +kernel
-- `é` in UTF-8 is well-formed but not ASCII.
example : [0xC3, 0xA9] ∉ language := by decide +kernel
example : [0x20, 0x41, 0x7E] ∈ printable := by decide +kernel
example : [0x41, 0x0A] ∉ printable := by decide +kernel
-- `"é"` as an escape is ASCII JSON; written directly it is JSON but not ASCII.
example : [0x22, 0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x22] ∈ json .rfc8259 := by decide +kernel
example : [0x22, 0xC3, 0xA9, 0x22] ∈ JsonBytes.language .rfc8259 := by decide +kernel
example : [0x22, 0xC3, 0xA9, 0x22] ∉ json .rfc8259 := by decide +kernel

end Examples

end Silmaril.Formats.Ascii

end
