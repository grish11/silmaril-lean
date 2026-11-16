module

public import Silmaril.Formats.Accept.Defs
public import Silmaril.Prelude.Bytes.Digits.Thms
public import Silmaril.Semantics.Accept.Thms

/-! # Accepted sets: theorems

Soundness and completeness of acceptor sets against specifications, their transport along
encodings and decodings, the closure of soundness and completeness under the Kleene
operations of Mathlib's `Language`, the agreement with the Bool-checker vocabulary of
`Silmaril.Semantics.Accept` (`sound_ofBool_iff`, `complete_ofBool_iff`, `exact_ofBool_iff`),
the bytes-like membership API (`KBytes`, `ByteArray`,
`Array UInt8`, `Formats.Bytes`) and the CSLib `Acceptor` reading of byte languages.
-/

@[expose] public section

namespace Silmaril.Formats.Accept

universe u v

open Set
open scoped Computability

namespace Lang

variable {α : Type u} {β : Type v} {A A' B S S' T : Lang α}

theorem exact_iff_sound_and_complete : Exact A S ↔ Sound A S ∧ Complete A S :=
  ⟨fun h => h ▸ ⟨subset_rfl, subset_rfl⟩, fun h => Subset.antisymm h.1 h.2⟩

theorem Exact.sound (h : Exact A S) : Sound A S := (exact_iff_sound_and_complete.1 h).1

theorem Exact.complete (h : Exact A S) : Complete A S := (exact_iff_sound_and_complete.1 h).2

theorem sound_iff : Sound A S ↔ ∀ x, x ∈ A → x ∈ S := Iff.rfl

theorem complete_iff : Complete A S ↔ ∀ x, x ∈ S → x ∈ A := Iff.rfl

/-- Accepting less stays sound. -/
theorem Sound.mono_left (h : A' ⊆ A) (hs : Sound A S) : Sound A' S := h.trans hs

/-- A weaker specification stays sound. -/
theorem Sound.mono_right (hs : Sound A S) (h : S ⊆ S') : Sound A S' := hs.trans h

/-- Accepting more stays complete. -/
theorem Complete.mono_left (hc : Complete A S) (h : A ⊆ A') : Complete A' S := hc.trans h

/-- A stronger specification stays complete. -/
theorem Complete.mono_right (h : S' ⊆ S) (hc : Complete A S) : Complete A S' := h.trans hc

/-- Soundness composes with specification refinement. -/
theorem Sound.trans (h₁ : Sound A B) (h₂ : Sound B S) : Sound A S := Subset.trans h₁ h₂

theorem Sound.union (h₁ : Sound A S) (h₂ : Sound B T) : Sound (A ∪ B) (S ∪ T) :=
  union_subset_union h₁ h₂

theorem Complete.union (h₁ : Complete A S) (h₂ : Complete B T) : Complete (A ∪ B) (S ∪ T) :=
  union_subset_union h₁ h₂

theorem Sound.inter (h₁ : Sound A S) (h₂ : Sound B T) : Sound (A ∩ B) (S ∩ T) :=
  inter_subset_inter h₁ h₂

theorem Complete.inter (h₁ : Complete A S) (h₂ : Complete B T) : Complete (A ∩ B) (S ∩ T) :=
  inter_subset_inter h₁ h₂

/-! ### Bool checkers (`Silmaril.Semantics.Accept`) -/

/-- A checker is sound for `S` iff the language it accepts is. -/
theorem sound_ofBool_iff {check : α → Bool} :
    Sound (Silmaril.Accept.ofBool check) S ↔ Silmaril.Accept.Sound check S :=
  Silmaril.Accept.sound_iff_ofBool_subset.symm

/-- A checker is complete for `S` iff the language it accepts is. -/
theorem complete_ofBool_iff {check : α → Bool} :
    Complete (Silmaril.Accept.ofBool check) S ↔ Silmaril.Accept.Complete check S :=
  Silmaril.Accept.complete_iff_subset_ofBool.symm

/-- A checker decides `S` iff the language it accepts is exactly `S`. -/
theorem exact_ofBool_iff {check : α → Bool} :
    Exact (Silmaril.Accept.ofBool check) S ↔ Silmaril.Accept.Decides check S :=
  Silmaril.Accept.decides_iff_ofBool_eq.symm

/-! ### Transport -/

theorem Sound.encode (e : α → β) (h : Sound A S) : Sound (A.encode e) (S.encode e) :=
  image_mono h

theorem Complete.encode (e : α → β) (h : Complete A S) : Complete (A.encode e) (S.encode e) :=
  image_mono h

theorem Sound.decode (d : β → α) (h : Sound A S) : Sound (A.decode d) (S.decode d) :=
  preimage_mono h

theorem Complete.decode (d : β → α) (h : Complete A S) : Complete (A.decode d) (S.decode d) :=
  preimage_mono h

theorem Sound.decode? (d : β → Option α) (h : Sound A S) : Sound (A.decode? d) (S.decode? d) :=
  fun _ ⟨a, ha, hd⟩ => ⟨a, h ha, hd⟩

theorem Complete.decode? (d : β → Option α) (h : Complete A S) :
    Complete (A.decode? d) (S.decode? d) :=
  fun _ ⟨a, ha, hd⟩ => ⟨a, h ha, hd⟩

/-- Along an injective encoding, soundness is reflected as well as preserved. -/
theorem sound_encode_iff {e : α → β} (he : Function.Injective e) :
    Sound (A.encode e) (S.encode e) ↔ Sound A S :=
  image_subset_image_iff he

/-- Along an injective encoding, completeness is reflected as well as preserved. -/
theorem complete_encode_iff {e : α → β} (he : Function.Injective e) :
    Complete (A.encode e) (S.encode e) ↔ Complete A S :=
  image_subset_image_iff he

/-- Along an equivalence, encoding is decoding by the inverse. -/
theorem encode_equiv (e : α ≃ β) (A : Lang α) : A.encode e = A.decode e.symm :=
  e.image_eq_preimage_symm A

/-- Along an equivalence, exactness is preserved and reflected. -/
theorem exact_encode_iff (e : α ≃ β) : Exact (A.encode e) (S.encode e) ↔ Exact A S :=
  (image_injective.2 e.injective).eq_iff

/-- Decoding along a total decoding is the partial decoding that always succeeds. -/
theorem decode?_some (d : β → α) (A : Lang α) : A.decode? (some ∘ d) = A.decode d := by
  ext b; simp [decode?, decode]

end Lang

namespace ByteLang

variable {β : Type u} [BytesLike β] {L M : ByteLang}

theorem accepts_iff (L : ByteLang) (b : β) : L.Accepts b ↔ toBytes b ∈ L := Iff.rfl

@[simp] theorem mem_over (L : ByteLang) (b : β) : b ∈ L.over β ↔ L.Accepts b := Iff.rfl

@[simp] theorem accepts_list (L : ByteLang) (bs : List UInt8) : L.Accepts bs ↔ bs ∈ L := Iff.rfl

@[simp] theorem accepts_array (L : ByteLang) (a : Array UInt8) : L.Accepts a ↔ a.toList ∈ L :=
  Iff.rfl

@[simp] theorem accepts_byteArray (L : ByteLang) (b : ByteArray) :
    L.Accepts b ↔ b.data.toList ∈ L := Iff.rfl

@[simp] theorem accepts_bytes (L : ByteLang) (b : Formats.Bytes) : L.Accepts b ↔ b.toList ∈ L :=
  Iff.rfl

@[simp] theorem accepts_kbytes (L : ByteLang) (t : KBytes) : L.Accepts t ↔ t.toList ∈ L :=
  Iff.rfl

/-- A `KBytes` and its `ByteArray` are accepted together. -/
theorem accepts_toByteArray (L : ByteLang) (t : KBytes) : L.Accepts t.toByteArray ↔ L.Accepts t :=
  Iff.rfl

/-- Acceptance only sees the bytes. -/
theorem accepts_congr {γ : Type v} [BytesLike γ] {b : β} {c : γ} (h : toBytes b = toBytes c) :
    L.Accepts b ↔ L.Accepts c := by
  rw [accepts_iff, accepts_iff, h]

theorem Accepts.mono (h : L ≤ M) {b : β} (hb : L.Accepts b) : M.Accepts b := h hb

theorem over_mono (h : L ≤ M) : L.over β ⊆ M.over β := fun _ hb => h hb

/-- A lawful bytes-like type represents every string, so its accepted values determine the
byte language. -/
theorem ofLang_over (L : ByteLang) (β : Type u) [LawfulBytesLike β] : ofLang (L.over β) = L := by
  ext bs
  refine ⟨fun ⟨b, hb, e⟩ => e ▸ hb, fun h => ⟨LawfulBytesLike.ofBytes bs, ?_, ?_⟩⟩
  · show toBytes (LawfulBytesLike.ofBytes (β := β) bs) ∈ L
    rw [LawfulBytesLike.toBytes_ofBytes]; exact h
  · exact LawfulBytesLike.toBytes_ofBytes bs

/-- Byte-language equality is acceptance equality on any lawful bytes-like type. -/
theorem ext_over (β : Type u) [LawfulBytesLike β] (h : L.over β = M.over β) : L = M := by
  rw [← ofLang_over L β, ← ofLang_over M β, h]

/-! ### Kleene operations -/

@[simp] theorem accepts_add (b : β) : (L + M).Accepts b ↔ L.Accepts b ∨ M.Accepts b := Iff.rfl

@[simp] theorem accepts_zero (b : β) : ¬ (0 : ByteLang).Accepts b := id

theorem accepts_mul (b : β) :
    (L * M).Accepts b ↔ ∃ x ∈ L, ∃ y ∈ M, x ++ y = toBytes b := Language.mem_mul

theorem sound_add {L' M' : ByteLang} (h₁ : Lang.Sound L L') (h₂ : Lang.Sound M M') :
    Lang.Sound (L + M) (L' + M') := union_subset_union h₁ h₂

theorem complete_add {L' M' : ByteLang} (h₁ : Lang.Complete L L') (h₂ : Lang.Complete M M') :
    Lang.Complete (L + M) (L' + M') := union_subset_union h₁ h₂

/-- Soundness is preserved by concatenation. -/
theorem sound_mul {L' M' : ByteLang} (h₁ : Lang.Sound L L') (h₂ : Lang.Sound M M') :
    Lang.Sound (L * M) (L' * M') := image2_subset h₁ h₂

/-- Completeness is preserved by concatenation. -/
theorem complete_mul {L' M' : ByteLang} (h₁ : Lang.Complete L L') (h₂ : Lang.Complete M M') :
    Lang.Complete (L * M) (L' * M') := image2_subset h₁ h₂

/-- Soundness is preserved by the Kleene star. -/
theorem sound_kstar {L' : ByteLang} (h : Lang.Sound L L') : Lang.Sound (L∗ : ByteLang) (L'∗ : ByteLang) :=
  (kstar_mono (show L ≤ L' from h) : L∗ ≤ L'∗)

/-- Completeness is preserved by the Kleene star. -/
theorem complete_kstar {L' : ByteLang} (h : Lang.Complete L L') : Lang.Complete (L∗ : ByteLang) (L'∗ : ByteLang) :=
  (kstar_mono (show L' ≤ L from h) : L'∗ ≤ L∗)

/-- A byte checker accepts a bytes-like value when it accepts its bytes. -/
@[simp] theorem accepts_ofBool (check : List UInt8 → Bool) (b : β) :
    ByteLang.Accepts (Silmaril.Accept.ofBool check) b ↔ check (toBytes b) = true := Iff.rfl

/-! ### CSLib acceptors -/

open Cslib.Automata in
/-- A byte language is its own CSLib language. -/
@[simp] theorem acceptor_language (L : ByteLang) : Acceptor.language L = L := rfl

open Cslib.Automata in
/-- A CSLib acceptor over bytes accepts a bytes-like value when it accepts its bytes. -/
@[simp] theorem accepts_language {A : Type v} [Acceptor A UInt8] (a : A) (b : β) :
    ByteLang.Accepts (Acceptor.language a) b ↔ Acceptor.Accepts a (toBytes b) := Iff.rfl

end ByteLang

end Silmaril.Formats.Accept

namespace Silmaril.KBytes

open Silmaril.Formats.Accept

@[simp] theorem toList_ofList (bs : List UInt8) : (ofList bs).toList = bs := unpack_leVal bs

@[simp] theorem len_ofList (bs : List UInt8) : (ofList bs).len = bs.length := rfl

theorem wf_ofList (bs : List UInt8) : (ofList bs).wf = true := rfl

/-- `KBytes` represent every byte string (by one leaf). -/
instance : LawfulBytesLike KBytes where
  toBytes := KBytes.toList
  ofBytes := ofList
  toBytes_ofBytes := toList_ofList

end Silmaril.KBytes
