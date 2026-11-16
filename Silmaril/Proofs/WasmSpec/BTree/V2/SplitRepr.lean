module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Frame
public import Silmaril.Proofs.WasmSpec.BTree.V2.Trees

/-!
# The B-tree library, version 2: the split in memory

`split_repr`: if, after `split_child`, the three pages it writes hold the split node, the
shrunk child and the new node, and every other page is unchanged, then the memory holds the
split tree `Tree.splitChild`. Facts about `Distinct` used for the frame.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-- A node's page is not a page of its children. -/
theorem Distinct.root_not_child {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
    {c : Tree} (hd : Distinct (.node x l ks cs)) (hc : c ∈ cs) : ¬ Owns x c := by
  cases hd with
  | node hx _ _ => exact hx c hc

/-- Distinct children own disjoint pages. -/
theorem Distinct.disjoint {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
    {i j p : Nat} (hd : Distinct (.node x l ks cs)) (hi : i < cs.length) (hj : j < cs.length)
    (hij : i ≠ j) (hp : Owns p cs[i]) : ¬ Owns p cs[j] := by
  cases hd with
  | node _ hpw _ =>
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_getElem.1 hpw i j hi hj h p hp
    · exact fun hp' => List.pairwise_iff_getElem.1 hpw j i hj hi h p hp' hp

/-- The children of a distinct node are distinct. -/
theorem Distinct.child {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
    {c : Tree} (hd : Distinct (.node x l ks cs)) (hc : c ∈ cs) : Distinct c := by
  cases hd with
  | node _ _ hcd => exact hcd c hc

/-- A tree in memory has a child in memory. -/
theorem Repr.child {B : ByteArray} {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
    {c : Tree} (hR : Repr B (.node x l ks cs)) (hc : c ∈ cs) : Repr B c := by
  cases hR with
  | leaf => simp at hc
  | inner _ _ _ hcR => exact hcR c hc

/-- The leaf flag of a tree in memory is the leaf indicator. -/
theorem Repr.leaf_iff {B : ByteArray} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} (hR : Repr B (.node x l ks cs)) :
    (l = true ↔ wd B (page * x) ≠ 0) ∧ (l = true → cs = []) ∧ OBAnd B (page * x + 4) 8090 ks ∧
      (l = false → BA B (page * x + 32768) 8091 (cs.map Tree.ptr)) := by
  cases hR with
  | leaf hl hk =>
    exact ⟨⟨fun _ => hl, fun _ => rfl⟩, fun _ => rfl, hk, fun h => Bool.noConfusion h⟩
  | inner hl hk hp _ =>
    exact ⟨⟨fun h => Bool.noConfusion h, fun h => absurd hl h⟩, fun h => Bool.noConfusion h, hk,
      fun _ => hp⟩

/-- **A node in memory** from its page's contents and its children in memory. -/
theorem Repr.node' {B : ByteArray} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} (hl : l = true ↔ wd B (page * x) ≠ 0) (hcs : l = true → cs = [])
    (hk : OBAnd B (page * x + 4) 8090 ks)
    (hp : l = false → BA B (page * x + 32768) 8091 (cs.map Tree.ptr))
    (hc : ∀ c ∈ cs, Repr B c) : Repr B (.node x l ks cs) := by
  cases l
  · exact .inner (by simpa using mt hl.2 (by simp)) hk (hp rfl) hc
  · rw [hcs rfl]
    exact .leaf (hl.1 rfl) hk

/-- An element of `cs.set i c'` other than `c'` is a child at another index. -/
theorem mem_set_ne {cs : List Tree} {i : Nat} {c c' : Tree} (h : c ∈ cs.set i c') :
    c = c' ∨ ∃ j, ∃ hj : j < cs.length, j ≠ i ∧ cs[j] = c := by
  obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem h
  by_cases hji : j = i
  · subst hji
    exact .inl (by simpa using hjc.symm)
  · refine .inr ⟨j, by simpa using hj, hji, ?_⟩
    rw [← hjc, List.getElem_set_ne (Ne.symm hji)]

/-- The children of the split node other than the two halves are unchanged in memory. -/
theorem split_other_child {B B' : ByteArray} {x i z : Nat} {kx : List (BitVec 32)}
    {cs : List Tree} {c : Tree} (hR : Repr B (.node x false kx cs))
    (hd : Distinct (.node x false kx cs)) (hpg : ∀ p, Owns p (.node x false kx cs) → PageOK B p)
    (hz : ¬ Owns z (.node x false kx cs)) (hi : i < cs.length) {j : Nat} (hj : j < cs.length)
    (hji : j ≠ i) (hc : cs[j] = c)
    (hU : Unchanged B B' (fun p => p = x ∨ p = cs[i].page ∨ p = z)) : Repr B' c := by
  subst hc
  have hm : cs[j] ∈ cs := List.getElem_mem hj
  refine (hR.child hm).frame hU fun p hp => ⟨?_, hpg p (.child hm hp)⟩
  rintro (rfl | rfl | rfl)
  · exact hd.root_not_child hm hp
  · exact hd.disjoint hi hj (Ne.symm hji) (Owns.root _) hp
  · exact hz (.child hm hp)

/-- The children of the full child are unchanged in memory. -/
theorem split_grandchild {B B' : ByteArray} {x i z y : Nat} {kx ky : List (BitVec 32)}
    {ly : Bool} {cs cy : List Tree} {c : Tree} (hR : Repr B (.node x false kx cs))
    (hd : Distinct (.node x false kx cs)) (hpg : ∀ p, Owns p (.node x false kx cs) → PageOK B p)
    (hz : ¬ Owns z (.node x false kx cs)) (hi : i < cs.length)
    (hy : cs[i] = .node y ly ky cy) (hc : c ∈ cy)
    (hU : Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z)) : Repr B' c := by
  have hm : Tree.node y ly ky cy ∈ cs := hy ▸ List.getElem_mem hi
  have hRy : Repr B (.node y ly ky cy) := hR.child hm
  have hdy : Distinct (.node y ly ky cy) := hd.child hm
  have hown : ∀ p, Owns p c → Owns p (.node x false kx cs) := fun p hp => .child hm (.child hc hp)
  refine (hRy.child hc).frame hU fun p hp => ⟨?_, hpg p (hown p hp)⟩
  rintro (rfl | rfl | rfl)
  · exact hd.root_not_child hm (.child hc hp)
  · exact hdy.root_not_child hc hp
  · exact hz (hown _ hp)

/-- The pointers of the split node: the old ones with `z` after child `i`. -/
theorem split_ptrs {cs : List Tree} {i z y : Nat} {ly : Bool} {ky : List (BitVec 32)}
    {cy : List Tree} {ky' : List (BitVec 32)} {cy' : List Tree} {cz : Tree} (hi : i < cs.length)
    (hy : cs[i] = .node y ly ky cy) (hz : cz.page = z) :
    ((cs.set i (.node y ly ky' cy')).insertIdx (i + 1) cz).map Tree.ptr =
      (cs.map Tree.ptr).insertIdx (i + 1) (BitVec.ofNat 32 z) := by
  have hset : (cs.set i (.node y ly ky' cy')).map Tree.ptr = cs.map Tree.ptr := by
    rw [List.map_set]
    have hp : (Tree.node y ly ky' cy').ptr = (cs.map Tree.ptr)[i]'(by simpa using hi) := by
      simp [hy, Tree.ptr, Tree.page]
    rw [hp, List.set_getElem_self]
  rw [List.map_insertIdx, hset, Tree.ptr, hz]

/-- The children of the split node are in memory. -/
theorem split_children {B B' : ByteArray} {x i z y : Nat} {kx ky : List (BitVec 32)}
    {ly : Bool} {cs cy : List Tree} {ky₁ ky₂ : List (BitVec 32)} {cy₁ cy₂ : List Tree}
    (hR : Repr B (.node x false kx cs)) (hd : Distinct (.node x false kx cs))
    (hpg : ∀ p, Owns p (.node x false kx cs) → PageOK B p) (hz : ¬ Owns z (.node x false kx cs))
    (hi : i < cs.length) (hy : cs[i] = .node y ly ky cy)
    (hU : Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z))
    (hy' : Repr B' (.node y ly ky₁ cy₁)) (hz' : Repr B' (.node z ly ky₂ cy₂)) :
    ∀ c ∈ (cs.set i (.node y ly ky₁ cy₁)).insertIdx (i + 1) (.node z ly ky₂ cy₂), Repr B' c := by
  have hU' : Unchanged B B' (fun p => p = x ∨ p = cs[i].page ∨ p = z) := by
    rw [hy]
    exact hU
  intro c hc
  rcases List.mem_insertIdx (by simpa using Nat.succ_le_of_lt hi) |>.1 hc with rfl | hc
  · exact hz'
  · rcases mem_set_ne hc with rfl | ⟨j, hj, hji, hjc⟩
    · exact hy'
    · exact split_other_child hR hd hpg hz hi hj hji hjc hU'

/-- **The split in memory**: if the pages of the node, of the full child and of the new node
hold the split node and the two halves, and every other page is unchanged, the memory holds
the split tree. -/
theorem split_repr {B B' : ByteArray} {t x i z y : Nat} {kx ky : List (BitVec 32)} {ly : Bool}
    {cs cy : List Tree} (hR : Repr B (.node x false kx cs)) (hd : Distinct (.node x false kx cs))
    (hpg : ∀ p, Owns p (.node x false kx cs) → PageOK B p) (hz : ¬ Owns z (.node x false kx cs))
    (hi : i < cs.length) (hy : cs[i] = .node y ly ky cy)
    (hU : Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z))
    (hx0 : wd B' (page * x) = 0)
    (hxk : OBAnd B' (page * x + 4) 8090 (kx.insertIdx i (ky.getD (t - 1) 0)))
    (hxp : BA B' (page * x + 32768) 8091 ((cs.map Tree.ptr).insertIdx (i + 1) (BitVec.ofNat 32 z)))
    (hyl : wd B' (page * y) = wd B (page * y)) (hyk : OBAnd B' (page * y + 4) 8090 (ky.take (t - 1)))
    (hyp : ly = false → BA B' (page * y + 32768) 8091 ((cy.take t).map Tree.ptr))
    (hzl : wd B' (page * z) = wd B (page * y)) (hzk : OBAnd B' (page * z + 4) 8090 (ky.drop t))
    (hzp : ly = false → BA B' (page * z + 32768) 8091 ((cy.drop t).map Tree.ptr)) :
    Repr B' ((Tree.node x false kx cs).splitChild t z i) := by
  have hm : Tree.node y ly ky cy ∈ cs := hy ▸ List.getElem_mem hi
  have hl := (hR.child hm).leaf_iff
  have hy' : Repr B' (.node y ly (ky.take (t - 1)) (cy.take t)) :=
    Repr.node' (by rw [hyl]; exact hl.1) (fun h => by rw [hl.2.1 h]; simp) hyk hyp
      fun c hc => split_grandchild hR hd hpg hz hi hy (List.mem_of_mem_take hc) hU
  have hz' : Repr B' (.node z ly (ky.drop t) (cy.drop t)) :=
    Repr.node' (by rw [hzl]; exact hl.1) (fun h => by rw [hl.2.1 h]; simp) hzk hzp
      fun c hc => split_grandchild hR hd hpg hz hi hy (List.mem_of_mem_drop hc) hU
  have he : (Tree.node x false kx cs).splitChild t z i = .node x false
      (kx.insertIdx i (ky.getD (t - 1) 0)) ((cs.set i (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx
        (i + 1) (.node z ly (ky.drop t) (cy.drop t))) := by
    simp only [Tree.splitChild, List.getElem?_eq_getElem hi, hy]
  rw [he]
  exact .inner hx0 hxk (by rw [split_ptrs hi hy rfl]; exact hxp)
    (split_children hR hd hpg hz hi hy hU hy' hz')

/-! ## Arrays for the split -/

/-- The first `m` words of a segment. -/
theorem words_take {B : ByteArray} {p n m : Nat} (hm : m ≤ n) :
    (words B p n).take m = words B p m := by
  have h : words B p n = words B p m ++ words B (p + 4 * m) (n - m) := by
    rw [← words_append, Nat.add_sub_cancel' hm]
  rw [h, List.take_left' (by simp)]

/-- The words of a segment from the `k`-th on. -/
theorem words_drop {B : ByteArray} {p n k : Nat} (hk : k ≤ n) :
    (words B p n).drop k = words B (p + 4 * k) (n - k) := by
  have h : words B p n = words B p k ++ words B (p + 4 * k) (n - k) := by
    rw [← words_append, Nat.add_sub_cancel' hk]
  rw [h, List.drop_left' (by simp)]

/-- **Truncating a bounded array**: writing a smaller length `m` keeps the first `m` elements. -/
theorem BA.truncate {B : ByteArray} {a n m : Nat} {α : List (BitVec 32)} (h : BA B a n α)
    (hm : m ≤ α.length) : BA (wr B a (BitVec.ofNat 32 m)) a n (α.take m) := by
  obtain ⟨h0, hw, hn, hmax, hsz⟩ := h
  have ha : a + 4 ≤ B.size := by omega
  have hl : (α.take m).length = m := by simp [hm]
  refine ⟨by rw [wd_wr_same _ ha, hl], ?_, by simp; omega, hmax, by rw [size_wr _ ha]; exact hsz⟩
  rw [hl, words_wr_out _ ha (by omega), ← words_take hm, hw]

/-- A sublist of an ordered array without duplicates, as a bounded array, is one. -/
theorem OBAnd.of_sublist {B B' : ByteArray} {a a' n n' : Nat} {α α' : List (BitVec 32)}
    (h : OBAnd B a n α) (hs : α'.Sublist α) (hA : BA B' a' n' α') : OBAnd B' a' n' α' :=
  ⟨⟨hA, h.1.2.sublist hs⟩, h.2.sublist hs⟩

end Silmaril.WasmSpec.BTree.V2
