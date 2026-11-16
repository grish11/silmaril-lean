module

public import Silmaril.Wasm.Component.Reference.WIT.Utf8.Thms
public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms
public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Semantics.Accept.Items.Thms
public import Silmaril.Wasm.Game.Accept.Complete.Thms

/-! # JSON texts and JSONL-shaped item lists as WIT inputs

Bridges from the format task's JSON byte language (`Silmaril.Formats.JsonBytes.language p`,
RFC 8259, #261) and the generic item bounds (`Silmaril.Semantics.Accept.Items`, #275) to WIT
acceptance.

* **JSON as `string`**: a JSON text is UTF-8 (`JsonBytes.language_isWellFormed`), so JSON texts
  are exactly the UTF-8 encodings of the strings `jsonStrings p`
  (`utf8_jsonStrings`). A WIT `string` validator (imported or exported `accept(string)`)
  can therefore be exact for JSON, and its byte language is always sound for UTF-8.
* **JSON as `list<u8>`**: the byte language itself, `ValLang.ofByteLang (language p)`.
* **JSONL-shaped inputs as `list<list<u8>>`**: the item lists all of whose items are JSON
  texts, `jsonItems p := Silmaril.Accept.everyItem (language p)`, represented by `Repr.items`.
  A per-item bound (`Silmaril.Accept.itemsWithin List.length n`) transfers to WIT validators of
  `list<list<u8>>` (`completeWithin_items_iff`). It bounds each item, not the list.
  This is the item-sequence reading only: how items are delimited in a byte stream (newline
  separators, the JSON Lines byte format) is not modelled here.
* **One-call modules**: if the JSON language is infinite (stated as a hypothesis here; it is not
  proved in this file), no one-call `accept(ptr, len)` module acceptor is complete for it
  (`not_complete_json_of_infinite`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

/-- JSON texts are well-formed UTF-8. -/
theorem json_le_utf8 (p : Silmaril.Formats.JsonBytes.Profile) :
    Silmaril.Formats.JsonBytes.language p ≤ Silmaril.Formats.Utf8.language :=
  fun _ h => Silmaril.Formats.JsonBytes.language_isWellFormed h

/-- The strings whose UTF-8 encoding is a JSON text. -/
def jsonStrings (p : Silmaril.Formats.JsonBytes.Profile) : ValLang E (.prim .string) :=
  {s : String | WIT.utf8 s ∈ Silmaril.Formats.JsonBytes.language p}

/-- **The JSON texts are exactly the UTF-8 encodings of `jsonStrings`.** -/
theorem utf8_jsonStrings (p : Silmaril.Formats.JsonBytes.Profile) :
    (jsonStrings (E := E) p).utf8 = Silmaril.Formats.JsonBytes.language p := by
  apply Set.Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩; exact hs
  · intro w hw
    have hu : w ∈ ValLang.utf8 (Set.univ : ValLang E (.prim .string)) := by
      rw [utf8_univ]; exact json_le_utf8 p hw
    obtain ⟨s, -, rfl⟩ := hu
    exact ⟨s, hw, rfl⟩

/-- A string acceptor is exact for JSON (as bytes) iff it accepts exactly `jsonStrings`. -/
theorem exact_json_iff {A : ValLang E (.prim .string)} {p : Silmaril.Formats.JsonBytes.Profile} :
    Lang.Exact A.utf8 (Silmaril.Formats.JsonBytes.language p) ↔ Lang.Exact A (jsonStrings p) := by
  rw [← utf8_jsonStrings (E := E) p]
  exact (Set.image_injective.2 utf8_injective).eq_iff

/-! ## JSONL-shaped item lists -/

/-- Item lists all of whose items are JSON texts. -/
def jsonItems (p : Silmaril.Formats.JsonBytes.Profile) : Set (List (List UInt8)) :=
  Silmaril.Accept.everyItem (Silmaril.Formats.JsonBytes.language p)

/-- **Per-item bounds transfer**: a WIT `list<list<u8>>` validator is complete for the JSON
item lists within a per-item length bound iff its Lean pullback is. -/
theorem completeWithin_items_iff (A : ValLang E (.list .bytes))
    (p : Silmaril.Formats.JsonBytes.Profile) (n : Nat) :
    Lang.CompleteWithin ((Repr.items).lang (Silmaril.Accept.itemsWithin List.length n)) A
        ((Repr.items).lang (jsonItems p)) ↔
      Lang.CompleteWithin (Silmaril.Accept.itemsWithin List.length n) ((Repr.items).pull A)
        (jsonItems p) :=
  Repr.completeWithin_lang_iff _

/-- JSON item lists are closed under concatenation, so a per-item bound alone does not
bound the number of items. -/
theorem jsonItems_append {p : Silmaril.Formats.JsonBytes.Profile} {s t : List (List UInt8)}
    (hs : s ∈ jsonItems p) (ht : t ∈ jsonItems p) : s ++ t ∈ jsonItems p :=
  Silmaril.Accept.append_mem_everyItem.2 ⟨hs, ht⟩

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Game.Accept.ModuleAcceptor

/-- **If the JSON language is infinite**, no one-call module acceptor is complete for it. -/
theorem not_complete_json_of_infinite (A : ModuleAcceptor) {p : Silmaril.Formats.JsonBytes.Profile}
    (h : (Silmaril.Formats.JsonBytes.language p : Set (List UInt8)).Infinite) :
    ¬ Silmaril.Formats.Accept.Lang.Complete A.lang (Silmaril.Formats.JsonBytes.language p) :=
  A.not_complete_of_infinite h

end Silmaril.Wasm.Game.Accept.ModuleAcceptor
