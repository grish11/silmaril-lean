module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Thms
public import Silmaril.Formats.Utf8.Thms

/-! # WIT `string` acceptors and the UTF-8 language

WIT `string` values are Lean `String`s (`ValType.Interp`), whose UTF-8 bytes are the
canonical ABI's `string-encoding=utf8` (`WIT.utf8`). Against the UTF-8 language of
`Silmaril.Formats.Utf8` (Unicode Table 3-7):

* the byte language of **any** string acceptor is sound for UTF-8 well-formedness
  (`sound_utf8_language`): a `string` validator can only ever accept well-formed UTF-8;
* the byte language of the acceptor of **all** strings is exactly the UTF-8 language
  (`utf8_univ`), so `string` and well-formed `list<u8>` carry the same inputs;
* a byte specification `L` is met by a `string` acceptor `A` (`A.utf8` sound and complete for
  `L`) only if `L` is within UTF-8 (`subset_language_of_exact`).

Scope: `utf8` encoding only; the canonical ABI's `latin1+utf16` and `utf16` string encodings
are not covered here.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

/-- The UTF-8 bytes of a string are well-formed UTF-8. -/
theorem utf8_mem_language (s : String) : WIT.utf8 s ∈ Silmaril.Formats.Utf8.language :=
  Silmaril.Formats.Utf8.toUTF8_isWellFormed s

/-- **Every string acceptor's byte language is sound for UTF-8.** -/
theorem sound_utf8_language (A : ValLang E (.prim .string)) :
    Lang.Sound A.utf8 Silmaril.Formats.Utf8.language := by
  rintro _ ⟨s, -, rfl⟩
  exact utf8_mem_language s

/-- **The strings are exactly the well-formed UTF-8 byte strings.** -/
theorem utf8_univ :
    ValLang.utf8 (Set.univ : ValLang E (.prim .string)) = Silmaril.Formats.Utf8.language := by
  apply Set.Subset.antisymm (sound_utf8_language _)
  intro w hw
  have hv : (ByteArray.mk w.toArray).IsValidUTF8 :=
    Silmaril.Formats.Utf8.isValidUTF8_iff.2 hw
  exact ⟨String.fromUTF8 _ hv, trivial, rfl⟩

/-- A byte specification exactly met by a string acceptor lies within UTF-8. -/
theorem subset_language_of_exact {A : ValLang E (.prim .string)} {L : ByteLang}
    (h : Lang.Exact A.utf8 L) : L ≤ Silmaril.Formats.Utf8.language :=
  h ▸ sound_utf8_language A

end Silmaril.Wasm.Component.WIT
