module

public import Silmaril.Proofs.WasmSpec.BTree.V2.InsLeaf
public import Silmaril.Proofs.WasmSpec.BTree.V2.Alloc

/-!
# The B-tree library, version 2: allocation and splitting as subtree updates

After `alloc_node` (`AllocPost`), a subtree is still a subtree with the new free list and an
update keeping its keys (`alloc_sub`), and a page it returns is free for the subtree
(`alloc_fresh`). After `split_child` with that page, the split tree is a subtree and an update
keeping the keys (`split_sub`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-- `alloc_node` changes no byte of the old memory outside page `0`. -/
theorem AllocPost.unchanged {B B' : ByteArray} {φ φ' : List (BitVec 32)} {r : BitVec 32}
    (h : AllocPost B φ r B' φ') : Unchanged B B' (· = 0) :=
  ⟨h.2.1, fun i hi hs => h.2.2.2.2.1 i hi (.inr (by simp only [page] at hs; omega))⟩

/-- `alloc_node` keeps the words at `0` and `4`. -/
theorem AllocPost.wd_low {B B' : ByteArray} {φ φ' : List (BitVec 32)} {r : BitVec 32}
    (h : AllocPost B φ r B' φ') {a : Nat} (ha : a + 4 ≤ 8) (hb : 8 ≤ B.size) : wd B' a = wd B a :=
  wd_of_bytes (by omega) (by have := h.2.1; omega) fun i _ hi => h.2.2.2.2.1 i (by omega) (.inl (by omega))

/-- A page of a subtree is not page `0`. -/
theorem Sub.ne_zero {B : ByteArray} {t : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)}
    {r : Bool} {d p : Nat} {X : Tree} (hS : Sub B t φ lo hi r d X) (hp : Owns p X) : ¬ p = 0 :=
  fun e => absurd (e ▸ (hS.hpg p hp).1) (by decide)

/-- The metadata page is in memory. -/
theorem Sub.size8 {B : ByteArray} {t : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)}
    {r : Bool} {d : Nat} {X : Tree} (hS : Sub B t φ lo hi r d X) : 8 + 4 + 4 * 16381 ≤ B.size :=
  hS.hfree.1.1.2.2.2.2

/-- **After `alloc_node`**, a subtree is a subtree with the new free list, and an update keeping
its keys. -/
theorem alloc_sub {B B' : ByteArray} {t : Nat} {φ φ' : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d : Nat} {X : Tree} {rv : BitVec 32}
    (hS : Sub B t φ lo hi r d X) (h : AllocPost B φ rv B' φ') :
    Sub B' t φ' lo hi r d X ∧ Upd B B' φ φ' X X fun _ => False := by
  have hU : Unchanged B B' (· = 0) := h.unchanged
  have h8 := hS.size8
  refine ⟨⟨hS.ht, hS.ht', (h.wd_low (by omega) (by omega)).trans hS.h0, h.1, h.2.2.1,
    fun q hq => ⟨h.2.2.2.2.2.1 q hq, (hS.hfok q (h.2.2.2.1.subset hq)).2⟩,
    hS.hR.frame hU fun p hp => ⟨hS.ne_zero hp, hS.hpg p hp⟩, hS.ho, hS.hb, hS.hd,
    fun p hp => (hS.hpg p hp).mono h.2.1⟩,
    ⟨rfl, h.2.2.2.1, h.wd_low (by omega) (by omega), h.2.1, fun p hp => .inl hp,
      hU.mono fun p hp => .inl hp, fun k => ⟨Or.inl, fun h => h.resolve_right id⟩⟩⟩

/-- **A page from `alloc_node`** is valid, not a page of the subtree, and not free any more. -/
theorem alloc_fresh {B B' : ByteArray} {t : Nat} {φ φ' : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d : Nat} {X : Tree} {rv : BitVec 32}
    (hS : Sub B t φ lo hi r d X) (h : AllocPost B φ rv B' φ') (hne : rv ≠ -1) :
    PageOK B' rv.toNat ∧ ¬ Owns rv.toNat X ∧ rv ∉ φ' ∧
      ((∃ q ∈ φ, q.toNat = rv.toNat) ∨ B.size ≤ page * rv.toNat) := by
  obtain ⟨hok, hn, hw⟩ := h.2.2.2.2.2.2.resolve_left hne
  refine ⟨hok, fun ho => ?_, hn, hw.imp (fun hq => ⟨rv, hq, rfl⟩) id⟩
  rcases hw with hq | hb
  · exact (hS.hfok rv hq).2 ho
  · have := (hS.hpg _ ho).2.2
    simp only [page] at *
    omega

/-- The bytes of the old memory after `alloc_node` and `split_child` (pages `x`, `y`, `z` of
the node, its child and the new page). -/
theorem split_frame {B B' B'' : ByteArray} {φ φ' : List (BitVec 32)} {rv : BitVec 32} {X : Tree}
    {x y : Nat} (hA : AllocPost B φ rv B' φ') (hU : Unchanged B' B'' fun p => p = x ∨ p = y ∨ p = rv.toNat)
    (hx : Owns x X) (hy : Owns y X)
    (hw : (∃ q ∈ φ, q.toNat = rv.toNat) ∨ B.size ≤ page * rv.toNat) : Unchanged B B'' (Owned X φ) := by
  refine ⟨hA.2.1.trans hU.1, fun i hi hs => ?_⟩
  have h0 : i / page ≠ 0 := fun e => hs (.inl e)
  have hs' : ¬ (i / page = x ∨ i / page = y ∨ i / page = rv.toNat) := by
    rintro (e | e | e)
    · exact hs (.inr (.inl (e ▸ hx)))
    · exact hs (.inr (.inl (e ▸ hy)))
    · rcases hw with hq | hb
      · exact hs (.inr (.inr (e ▸ hq)))
      · exact not_fresh hi (e ▸ hb)
  exact (hU.2 i (lt_of_lt_of_le hi hA.2.1) hs').trans (hA.unchanged.2 i hi h0)

/-- **After `alloc_node` and `split_child`**, the split tree is a subtree with the new free
list, and an update keeping the keys. -/
theorem split_sub {B B' B'' : ByteArray} {t d' x j y : Nat} {φ φ' : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r ly : Bool} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    {rv : BitVec 32} (hS : Sub B t φ lo hi r (d' + 1) (.node x false kx cs))
    (hA : AllocPost B φ rv B' φ') (hne : rv ≠ -1) (hj : j < cs.length)
    (hy : cs[j] = .node y ly ky cy) (hky : ky.length = 2 * t - 1) (hkx : kx.length < 2 * t - 1)
    (hsz : B''.size = B'.size) (hR : Repr B'' ((Tree.node x false kx cs).splitChild t rv.toNat j))
    (hU : Unchanged B' B'' fun p => p = x ∨ p = y ∨ p = rv.toNat) :
    Sub B'' t φ' lo hi r (d' + 1) ((Tree.node x false kx cs).splitChild t rv.toNat j) ∧
      Upd B B'' φ φ' (.node x false kx cs) ((Tree.node x false kx cs).splitChild t rv.toNat j)
        fun _ => False := by
  obtain ⟨hS', -⟩ := alloc_sub hS hA
  obtain ⟨hzok, hzX, hzφ, hw⟩ := alloc_fresh hS hA hne
  have hm : Tree.node y ly ky cy ∈ cs := hy ▸ List.getElem_mem hj
  have hx1 : 1 ≤ x := (hS.hpg x .here).1
  have hy1 : 1 ≤ y := (hS.hpg y (.child hm .here)).1
  have hz1 : 1 ≤ rv.toNat := hzok.1
  have hlen : cs.length = kx.length + 1 := (hS.ho.shape hj).2
  have hown := fun p => splitChild_owns (t := t) (z := rv.toNat) (x := x) (l := false) (kx := kx)
    (p := p) hj hy
  have hU0 : ∀ i, i < 8 + 4 + 4 * 16381 → ¬ (i / page = x ∨ i / page = y ∨ i / page = rv.toNat) := by
    intro i hi; simp only [page]; omega
  have hsz8 := hS'.size8
  have hszB := hS.size8
  refine ⟨⟨hS.ht, hS.ht', (hU.wd_eq (by omega) fun i _ h => hU0 i (by omega)).trans hS'.h0,
    hsz ▸ hS'.hsz, hS'.hfree.frame hU fun i _ h => hU0 i (by omega), fun q hq => ⟨?_, ?_⟩, hR,
    splitChild_ordered (by have := hS.ht; omega) hj hy hky hS.ho,
    splitChild_balanced hS.ht hj hlen hy hky hkx hS.hb, splitChild_distinct hj hy hS.hd hzX,
    fun p hp => ?_⟩, ⟨splitChild_page, hA.2.2.2.1, ?_, hA.2.1.trans (le_of_eq hsz.symm),
      fun p hp => ?_, split_frame hA hU .here (.child hm .here) hw,
      fun k => (splitChild_inTree (by have := hS.ht; omega) hj hlen hy hky).trans
        ⟨Or.inl, fun h => h.resolve_right id⟩⟩⟩
  · exact (hS'.hfok q hq).1.mono (le_of_eq hsz.symm)
  · intro ho
    rcases (hown _).1 ho with h | h
    · exact (hS'.hfok q hq).2 h
    · exact hzφ ((BitVec.eq_of_toNat_eq h) ▸ hq)
  · rcases (hown p).1 hp with h | rfl
    · exact (hS'.hpg p h).mono (le_of_eq hsz.symm)
    · exact hzok.mono (le_of_eq hsz.symm)
  · exact (hU.wd_eq (by omega) fun i _ h => hU0 i (by omega)).trans (hA.wd_low (by omega) (by omega))
  · rcases (hown p).1 hp with h | rfl
    · exact .inl h
    · exact .inr hw

/-! ## Descending after a split -/

/-- The bounds of the left half: the old lower bound and the median. -/
theorem bounds_left {lo hi : Option (BitVec 32)} {kx : List (BitVec 32)} {j : Nat} {m : BitVec 32}
    (hj : j ≤ kx.length) :
    lob lo (kx.insertIdx j m) j = lob lo kx j ∧ hib hi (kx.insertIdx j m) j = some m := by
  have hl : (kx.insertIdx j m).length = kx.length + 1 := List.length_insertIdx_of_le_length hj m
  refine ⟨?_, ?_⟩
  · by_cases h0 : j = 0
    · simp [lob, h0]
    · simp only [lob, h0, ↓reduceIte]
      rw [List.getElem?_insertIdx_of_lt (by omega)]
  · simp only [hib, show j ≠ (kx.insertIdx j m).length by omega, ↓reduceIte]
    exact median_key hj

/-- The bounds of the right half: the median and the old upper bound. -/
theorem bounds_right {lo hi : Option (BitVec 32)} {kx : List (BitVec 32)} {j : Nat} {m : BitVec 32}
    (hj : j ≤ kx.length) :
    lob lo (kx.insertIdx j m) (j + 1) = some m ∧ hib hi (kx.insertIdx j m) (j + 1) = hib hi kx j := by
  have hl : (kx.insertIdx j m).length = kx.length + 1 := List.length_insertIdx_of_le_length hj m
  refine ⟨?_, ?_⟩
  · simp only [lob, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact median_key hj
  · by_cases hn : j = kx.length
    · simp [hib, hn]
    · simp only [hib, show j + 1 ≠ (kx.insertIdx j m).length by omega, hn, ↓reduceIte]
      rw [List.getElem?_insertIdx_of_gt (by omega), Nat.add_sub_cancel]

/-- `k` below the median lies within the left half's bounds. -/
theorem within_left {L U : Option (BitVec 32)} {m k : BitVec 32} (hw : Within L U k)
    (hk : k.toInt < m.toInt) : Within L (some m) k :=
  ⟨hw.1, fun h hh => by cases hh; exact hk⟩

/-- `k` above the median lies within the right half's bounds. -/
theorem within_right {L U : Option (BitVec 32)} {m k : BitVec 32} (hw : Within L U k)
    (hk : m.toInt < k.toInt) : Within (some m) U k :=
  ⟨fun l hl => by cases hl; exact hk, hw.2⟩

/-- An inner node in order has one child more than keys. -/
theorem Ordered.inner_len {lo hi : Option (BitVec 32)} {y : Nat} {ky : List (BitVec 32)}
    {cy : List Tree} (ho : Ordered lo hi (.node y false ky cy)) : cy.length = ky.length + 1 := by
  cases ho with
  | mk _ _ hlen _ => simpa using hlen

end Silmaril.WasmSpec.BTree.V2
