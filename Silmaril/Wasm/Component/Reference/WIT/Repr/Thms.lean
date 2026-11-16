module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Defs
public import Silmaril.Formats.Accept.Bounded.Thms

/-! # Representing Lean types by WIT types: theorems

* `Repr.lang r S` is the preimage of `S` under `r.symm`; membership is reflected exactly
  (`mem_lang`).
* **Validator bridges.** For any WIT acceptor set `A` (for instance a component's
  `valLang t σ f`), let `r.pull A := r ⁻¹' A` be the Lean inputs whose representation `A`
  accepts. Then `A` is sound, complete or exact for `r.lang S` iff `r.pull A` is for `S`
  (`sound_lang_iff`, `complete_lang_iff`, `exact_lang_iff`). The same holds within a bound:
  for a bound `D` on the Lean side, completeness within `r.lang D` is completeness within `D`
  (`completeWithin_lang_iff`), so length, depth or per-item bounds stated on Lean values
  transfer to WIT validators.
* The combinators compute as expected (`list_apply`, `bytes_apply`, `items_apply`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

namespace Repr

variable {α : Type} {t : ValType Ref Resource} (r : Repr E α t)

/-- The Lean inputs whose representation `A` accepts. -/
def pull (A : ValLang E t) : Set α := r ⁻¹' A

theorem lang_eq (S : Set α) : r.lang S = r.symm ⁻¹' S := Lang.encode_equiv r S

@[simp] theorem mem_lang {S : Set α} {x : α} : r x ∈ r.lang S ↔ x ∈ S :=
  r.injective.mem_set_image

theorem mem_lang' {S : Set α} {v : t.Interp E} : v ∈ r.lang S ↔ r.symm v ∈ S := by
  rw [lang_eq]; rfl

@[simp] theorem pull_lang (S : Set α) : r.pull (r.lang S) = S := by
  ext x; exact r.mem_lang

@[simp] theorem lang_pull (A : ValLang E t) : r.lang (r.pull A) = A := by
  ext v; rw [mem_lang']; show r (r.symm v) ∈ A ↔ v ∈ A; rw [Equiv.apply_symm_apply]

/-- **A WIT acceptor is sound for a represented specification iff its Lean pullback is.** -/
theorem sound_lang_iff {A : ValLang E t} {S : Set α} :
    Lang.Sound A (r.lang S) ↔ Lang.Sound (r.pull A) S := by
  conv_lhs => rw [← r.lang_pull A]
  exact Lang.sound_encode_iff r.injective

/-- **A WIT acceptor is complete for a represented specification iff its Lean pullback is.** -/
theorem complete_lang_iff {A : ValLang E t} {S : Set α} :
    Lang.Complete A (r.lang S) ↔ Lang.Complete (r.pull A) S := by
  conv_lhs => rw [← r.lang_pull A]
  exact Lang.complete_encode_iff r.injective

theorem exact_lang_iff {A : ValLang E t} {S : Set α} :
    Lang.Exact A (r.lang S) ↔ Lang.Exact (r.pull A) S := by
  conv_lhs => rw [← r.lang_pull A]
  exact Lang.exact_encode_iff r

/-- **Bounded completeness transfers**: a Lean-side bound `D` (length, depth, per item). -/
theorem completeWithin_lang_iff {A : ValLang E t} {S D : Set α} :
    Lang.CompleteWithin (r.lang D) A (r.lang S) ↔ Lang.CompleteWithin D (r.pull A) S := by
  conv_lhs => rw [← r.lang_pull A]
  exact Lang.completeWithin_encode_iff r.injective

theorem soundWithin_lang_iff {A : ValLang E t} {S D : Set α} :
    Lang.SoundWithin (r.lang D) A (r.lang S) ↔ Lang.SoundWithin D (r.pull A) S := by
  conv_lhs => rw [← r.lang_pull A]
  exact Lang.soundWithin_encode_iff r.injective

end Repr

@[simp] theorem Repr.bytes_apply (w : List UInt8) : (Repr.bytes (E := E)) w = w := rfl

@[simp] theorem Repr.list_apply {α : Type} {t : ValType Ref Resource} (r : Repr E α t)
    (xs : List α) : r.list xs = xs.map r := rfl

@[simp] theorem Repr.items_apply (xs : List (List UInt8)) : (Repr.items (E := E)) xs = xs := by
  show xs.map id = xs; exact List.map_id xs

/-- The byte languages are the `list<u8>` specifications of their own representation. -/
theorem Repr.bytes_lang (L : ByteLang) : (Repr.bytes (E := E)).lang L = ValLang.ofByteLang L := by
  ext w; simp [Repr.lang, Lang.encode, Repr.bytes, ValLang.ofByteLang]; rfl

end Silmaril.Wasm.Component.WIT
