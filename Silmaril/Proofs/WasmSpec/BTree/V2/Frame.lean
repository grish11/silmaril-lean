module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Specs

/-!
# The B-tree library, version 2: the memory frame

`Unchanged B B' S` (`B'` at least as large as `B`, with the bytes of `B` on every page outside
`S`) is reflexive, transitive and monotone in `S`; words and bounded arrays on pages outside
`S` are unchanged (`Unchanged.wd_eq`, `BA.frame`), and so is a tree whose pages are all
outside `S` (`Repr.frame`). A `SameOutside` inside the pages `S` is an `Unchanged`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Execution Silmaril.Wasm.Logic.Words

variable {B B' B'' : ByteArray} {S S' : Nat → Prop}

theorem Unchanged.refl (B : ByteArray) (S : Nat → Prop) : Unchanged B B S :=
  ⟨le_refl _, fun _ _ _ => rfl⟩

theorem Unchanged.mono (h : Unchanged B B' S) (hS : ∀ p, S p → S' p) : Unchanged B B' S' :=
  ⟨h.1, fun i hi hs => h.2 i hi fun h' => hs (hS _ h')⟩

theorem Unchanged.trans (h : Unchanged B B' S) (h' : Unchanged B' B'' S) : Unchanged B B'' S :=
  ⟨h.1.trans h'.1, fun i hi hs => (h'.2 i (lt_of_lt_of_le hi h.1) hs).trans (h.2 i hi hs)⟩

/-- A `SameOutside` whose region lies on the pages `S`. -/
theorem SameOutside.unchanged {a len : Nat} (h : SameOutside B B' a len)
    (hS : ∀ i, a ≤ i → i < a + len → S (i / page)) : Unchanged B B' S :=
  ⟨h.1.ge, fun i _ hs => h.2 i (by
    by_contra hc
    exact hs (hS i (by omega) (by omega)))⟩

/-- A word on pages outside `S` is unchanged. -/
theorem Unchanged.wd_eq {a : Nat} (h : Unchanged B B' S) (ha : a + 4 ≤ B.size)
    (hs : ∀ i, a ≤ i → i < a + 4 → ¬ S (i / page)) : wd B' a = wd B a := by
  have hb' : a + 4 ≤ B'.size := le_trans ha h.1
  have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ = Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
    apply List.ext_getElem?
    intro i
    rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
    dsimp only
    split
    · exact h.2 _ (by omega) (hs _ (by omega) (by omega))
    · rfl
  rw [wd, wd, Silmaril.Wasm.Logic.Core.load_eq ha, Silmaril.Wasm.Logic.Core.load_eq hb', hr]

/-- A bounded array on pages outside `S` is unchanged. -/
theorem BA.frame {a n : Nat} {α : List (BitVec 32)} (hA : BA B a n α) (h : Unchanged B B' S)
    (hs : ∀ i, a ≤ i → i < a + 4 + 4 * n → ¬ S (i / page)) : BA B' a n α := by
  obtain ⟨h0, hw, hn, hmax, hsz⟩ := hA
  have hlen : wd B' a = wd B a := h.wd_eq (by omega) fun i h1 h2 => hs i h1 (by omega)
  have hws : words B' (a + 4) α.length = words B (a + 4) α.length := by
    unfold words
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < α.length := List.mem_range.1 hk
    exact h.wd_eq (by omega) fun i h1 h2 => hs i (by omega) (by omega)
  exact ⟨hlen.trans h0, hws.trans hw, hn, hmax, le_trans hsz h.1⟩

/-- An ordered bounded array on pages outside `S` is unchanged. -/
theorem OBAnd.frame {a n : Nat} {α : List (BitVec 32)} (hA : OBAnd B a n α)
    (h : Unchanged B B' S) (hs : ∀ i, a ≤ i → i < a + 4 + 4 * n → ¬ S (i / page)) :
    OBAnd B' a n α :=
  ⟨⟨hA.1.1.frame h hs, hA.1.2⟩, hA.2⟩

/-- A byte on page `x` is on page `x`. -/
theorem div_page {x i : Nat} (h1 : page * x ≤ i) (h2 : i < page * x + page) : i / page = x := by
  simp only [page] at *
  omega

/-- The word at offset `o` of page `x`, for `o + 4 ≤ 65536`. -/
theorem page_word {x o : Nat} (ho : o + 4 ≤ page) :
    ∀ i, page * x + o ≤ i → i < page * x + o + 4 → i / page = x := fun _ h1 h2 =>
  div_page (by omega) (by omega)

/-- The keys array of page `x` lies on page `x`. -/
theorem keys_on_page {x : Nat} :
    ∀ i, page * x + 4 ≤ i → i < page * x + 4 + 4 + 4 * 8090 → i / page = x := fun _ h1 h2 =>
  div_page (by omega) (by simp only [page] at *; omega)

/-- The pointer array of page `x` lies on page `x`. -/
theorem ptrs_on_page {x : Nat} :
    ∀ i, page * x + 32768 ≤ i → i < page * x + 32768 + 4 + 4 * 8091 → i / page = x :=
  fun _ h1 h2 => div_page (by omega) (by simp only [page] at *; omega)

/-- The node at page `x` (leaf indicator, keys, pointers) is unchanged if `x ∉ S`. -/
theorem node_frame {x : Nat} (h : Unchanged B B' S) (hx : ¬ S x) (hok : PageOK B x) :
    wd B' (page * x) = wd B (page * x) ∧
    (∀ ks, OBAnd B (page * x + 4) 8090 ks → OBAnd B' (page * x + 4) 8090 ks) ∧
    (∀ ps, BA B (page * x + 32768) 8091 ps → BA B' (page * x + 32768) 8091 ps) := by
  have hsz : page * (x + 1) ≤ B.size := hok.2.2
  refine ⟨h.wd_eq (by simp only [page] at *; omega) fun i h1 h2 => ?_,
    fun ks hk => hk.frame h fun i h1 h2 => ?_, fun ps hp => hp.frame h fun i h1 h2 => ?_⟩
  · rw [page_word (o := 0) (by decide) i (by omega) (by omega)]
    exact hx
  · rw [keys_on_page i h1 h2]
    exact hx
  · rw [ptrs_on_page i h1 h2]
    exact hx

/-- **A tree whose pages are all outside `S` is unchanged.** -/
theorem Repr.frame {T : Tree} (hR : Repr B T) (h : Unchanged B B' S)
    (hs : ∀ p, Owns p T → ¬ S p ∧ PageOK B p) : Repr B' T := by
  induction hR with
  | @leaf x ks hl hk =>
    have hn := node_frame h (hs x .here).1 (hs x .here).2
    exact .leaf (hn.1 ▸ hl) (hn.2.1 ks hk)
  | @inner x ks cs hl hk hp hc ih =>
    have hn := node_frame h (hs x .here).1 (hs x .here).2
    exact .inner (hn.1 ▸ hl) (hn.2.1 ks hk) (hn.2.2 _ hp)
      fun c hm => ih c hm fun p hp' => hs p (.child hm hp')

/-! ## Byte regions -/

/-- `B'` has the size of `B` and its bytes outside the addresses `R`. -/
def Agree (B B' : ByteArray) (R : Nat → Prop) : Prop :=
  B'.size = B.size ∧ ∀ i, ¬ R i → B'.data.toList[i]? = B.data.toList[i]?

variable {R R' : Nat → Prop}

theorem Agree.refl (B : ByteArray) (R : Nat → Prop) : Agree B B R := ⟨rfl, fun _ _ => rfl⟩

theorem Agree.trans (h : Agree B B' R) (h' : Agree B' B'' R') :
    Agree B B'' fun i => R i ∨ R' i :=
  ⟨h'.1.trans h.1, fun i hi => (h'.2 i fun h'' => hi (.inr h'')).trans
    (h.2 i fun h'' => hi (.inl h''))⟩

theorem Agree.mono (h : Agree B B' R) (hR : ∀ i, R i → R' i) : Agree B B' R' :=
  ⟨h.1, fun i hi => h.2 i fun h' => hi (hR i h')⟩

/-- A `SameOutside` is an `Agree` on its segment. -/
theorem SameOutside.agree {a len : Nat} (h : SameOutside B B' a len) :
    Agree B B' fun i => a ≤ i ∧ i < a + len :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

/-- An `Agree` whose addresses lie on the pages `S` is an `Unchanged`. -/
theorem Agree.unchanged (h : Agree B B' R) (hS : ∀ i, R i → S (i / page)) : Unchanged B B' S :=
  ⟨h.1.ge, fun i _ hs => h.2 i fun hr => hs (hS i hr)⟩

/-- A word outside the addresses `R` is unchanged. -/
theorem Agree.wd_eq {a : Nat} (h : Agree B B' R) (hs : ∀ i, a ≤ i → i < a + 4 → ¬ R i) :
    wd B' a = wd B a := by
  by_cases ha : a + 4 ≤ B.size
  · have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ =
        Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
      apply List.ext_getElem?
      intro i
      rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
      dsimp only
      split
      · exact h.2 _ (hs _ (by omega) (by omega))
      · rfl
    rw [wd, wd, Silmaril.Wasm.Logic.Core.load_eq ha, Silmaril.Wasm.Logic.Core.load_eq (h.1 ▸ ha), hr]
  · have hl : Memory.load B a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by omega)
    have hl' : Memory.load B' a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by rw [h.1]; omega)
    rw [wd, wd, hl, hl']

/-- Words outside the addresses `R` are unchanged. -/
theorem Agree.words_eq {a n : Nat} (h : Agree B B' R) (hs : ∀ i, a ≤ i → i < a + 4 * n → ¬ R i) :
    words B' a n = words B a n := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < n := List.mem_range.1 hk
  exact h.wd_eq fun i h1 h2 => hs i (by omega) (by omega)

/-- A bounded array outside the addresses `R` is unchanged. -/
theorem BA.agree {a n : Nat} {α : List (BitVec 32)} (hA : BA B a n α) (h : Agree B B' R)
    (hs : ∀ i, a ≤ i → i < a + 4 + 4 * n → ¬ R i) : BA B' a n α := by
  obtain ⟨h0, hw, hn, hmax, hsz⟩ := hA
  have hlen : wd B' a = wd B a := h.wd_eq fun i h1 h2 => hs i h1 (by omega)
  have hws : words B' (a + 4) α.length = words B (a + 4) α.length :=
    h.words_eq fun i h1 h2 => hs i (by omega) (by omega)
  exact ⟨hlen.trans h0, hws.trans hw, hn, hmax, h.1 ▸ hsz⟩

/-- An ordered bounded array outside the addresses `R` is unchanged. -/
theorem OBAnd.agree {a n : Nat} {α : List (BitVec 32)} (hA : OBAnd B a n α) (h : Agree B B' R)
    (hs : ∀ i, a ≤ i → i < a + 4 + 4 * n → ¬ R i) : OBAnd B' a n α :=
  ⟨⟨hA.1.1.agree h hs, hA.1.2⟩, hA.2⟩

end Silmaril.WasmSpec.BTree.V2
