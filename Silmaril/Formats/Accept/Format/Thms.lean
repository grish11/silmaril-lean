module

public import Silmaril.Formats.Accept.Format.Defs
public import Silmaril.Formats.Accept.Thms

/-! # Byte languages of formats: theorems

* `mem_lang_iff`: valid inputs are the inputs related to some AST.
* `lang_ofDecoder`: for a decoder, the inputs it decodes.
* `lang_ofLanguage`: the format of a language has that language.
* `lang_mono`: a format morphism preserves bytes, so it includes languages.
* `lang_restrict`: restricting a format restricts its language.
* `Lang.Sound`/`Complete` of an acceptor for a format are those for its language
  (`sound_lang_iff`).
-/

@[expose] public section

namespace Silmaril.Formats.Format

open Silmaril.Formats.Accept

theorem mem_lang_iff (F : Format) (w : List UInt8) :
    w ∈ F.lang ↔ ∃ ast, F.rel (Bytes.ofList w) ast := by
  constructor
  · rintro ⟨d, rfl⟩; exact ⟨F.ast d, d, (Bytes.ofList_toList _).symm, rfl⟩
  · rintro ⟨_, d, hd, -⟩; exact ⟨d, by rw [hd, Bytes.toList_ofList]⟩

/-- **A decoder's valid inputs are those it decodes.** -/
theorem lang_ofDecoder {A : Type} (decode : Bytes → Option A) :
    (ofDecoder decode).lang = {w | (decode (Bytes.ofList w)).isSome} := by
  ext w
  constructor
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl⟩
    show (decode (Bytes.ofList b.toList)).isSome
    rw [Bytes.ofList_toList, h]; rfl
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
    exact ⟨⟨⟨Bytes.ofList w, a⟩, ha⟩, Bytes.toList_ofList w⟩

theorem lang_ofLanguage (L : ByteLang) : (ofLanguage L).lang = L := by
  ext w
  constructor
  · rintro ⟨⟨⟨b, _⟩, h⟩, rfl⟩; exact h
  · intro h
    exact ⟨⟨⟨Bytes.ofList w, ()⟩, by show (Bytes.ofList w).toList ∈ L; rwa [Bytes.toList_ofList]⟩,
      Bytes.toList_ofList w⟩

/-- A morphism of formats preserves bytes, so it includes the valid inputs. -/
theorem lang_mono {F G : Format} (f : F ⟶ G) : F.lang ≤ G.lang := by
  rintro _ ⟨d, rfl⟩
  exact ⟨f.onDerivation d, by rw [f.bytes_commute]⟩

theorem lang_restrict (F : Format) (accept : Bytes → F.Ast → Prop) :
    (F.restrict accept).lang ≤ F.lang := by
  rintro _ ⟨d, rfl⟩
  exact ⟨d.val, rfl⟩

/-- An acceptor is sound for a format iff it is sound for its language (by definition). -/
theorem sound_lang_iff (A : ByteLang) (F : Format) :
    Lang.Sound A F.lang ↔ ∀ w ∈ A, ∃ ast, F.rel (Bytes.ofList w) ast :=
  ⟨fun h w hw => (mem_lang_iff F w).1 (h hw), fun h w hw => (mem_lang_iff F w).2 (h w hw)⟩

end Silmaril.Formats.Format
