module

public import Silmaril.Proofs.WasmSpec.BTree.V2.InsPure
public import Silmaril.Proofs.WasmSpec.BTree.V2.SplitChild

/-!
# The B-tree library, version 2: inserting into a leaf, abstractly

A key `k` within a leaf's bounds and not among its keys, inserted at its `oba_find` index,
gives a leaf that is again a subtree (`leaf_sub`) and an update adding `k` (`leaf_upd`), when
the memory changed only in the leaf's keys. The bounds of child `j` contain `k` when `j` is its
`oba_find` index (`within_child`). The context of `insert_nonfull` is determined by the memory
(`NFPre.unique`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-- **`k` lies within the bounds of child `j`**, its `oba_find` index among keys it is not in. -/
theorem within_child {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} {k : BitVec 32}
    {j : Nat} (hw : Within lo hi k) (hF : FindsAt ks k j) (hk : k ∉ ks) :
    Within (lob lo ks j) (hib hi ks j) k := by
  obtain ⟨hjl, hlt, hge⟩ := hF
  refine ⟨fun l hl => ?_, fun h hh => ?_⟩
  · by_cases hj : j = 0
    · exact hw.1 l (by simpa [lob, hj] using hl)
    · have hj' : j - 1 < ks.length := by omega
      have he : ks[j - 1] = l := by simpa [lob, hj, hj'] using hl
      have h1 : (ks.getD (j - 1) 0).toInt < k.toInt := hlt (j - 1) (by omega)
      rw [getD_of_lt _ hj', he] at h1
      exact h1
  · by_cases hj : j = ks.length
    · exact hw.2 h (by simpa [hib, hj] using hh)
    · have hj' : j < ks.length := by omega
      have he : ks[j] = h := by simpa [hib, hj, hj'] using hh
      have h1 : k.toInt ≤ (ks.getD j 0).toInt := hge j (le_refl _) hj'
      rw [getD_of_lt _ hj', he] at h1
      have hne : k ≠ h := fun e => hk (e ▸ he ▸ List.getElem_mem hj')
      have hne' : k.toInt ≠ h.toInt := fun e => hne (BitVec.toInt_inj.1 e)
      omega

/-- Inserting `k` at its `oba_find` index keeps the keys strictly increasing. -/
theorem insert_sorted {ks : List (BitVec 32)} {k : BitVec 32} {j : Nat}
    (hs : ks.Pairwise fun a b => a.toInt < b.toInt) (hF : FindsAt ks k j) (hk : k ∉ ks) :
    (ks.insertIdx j k).Pairwise fun a b => a.toInt < b.toInt :=
  pairwise_insertIdx (lo := none) (hi := none) hs hF.1
    (within_child ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩ hF hk)

/-- The keys of a leaf after inserting `k`. -/
theorem leaf_inTree {x j : Nat} {ks : List (BitVec 32)} {k k' : BitVec 32} (hj : j ≤ ks.length) :
    InTree k' (.node x true (ks.insertIdx j k) []) ↔ InTree k' (.node x true ks []) ∨ k' = k := by
  rw [inTree_leaf, inTree_leaf, List.mem_insertIdx hj]
  exact or_comm

/-- The ordered leaf after inserting `k` within its bounds. -/
theorem leaf_ordered {lo hi : Option (BitVec 32)} {x j : Nat} {ks : List (BitVec 32)}
    {k : BitVec 32} (ho : Ordered lo hi (.node x true ks [])) (hw : Within lo hi k)
    (hF : FindsAt ks k j) (hk : k ∉ ks) : Ordered lo hi (.node x true (ks.insertIdx j k) []) := by
  have hks := ho.keys
  refine .mk (insert_sorted hks.1 hF hk) (fun k' hk' => ?_) (by simp) (fun i h => by simp at h)
  rcases (List.mem_insertIdx hF.1).1 hk' with rfl | h
  · exact hw
  · exact hks.2 k' h

/-- The balanced leaf after inserting a key into a non-full leaf. -/
theorem leaf_balanced {t d x j : Nat} {r : Bool} {ks : List (BitVec 32)} {k : BitVec 32}
    (hb : Balanced t r d (.node x true ks [])) (hn : ks.length < 2 * t - 1) (hj : j ≤ ks.length) :
    Balanced t r d (.node x true (ks.insertIdx j k) []) := by
  have hl : (ks.insertIdx j k).length = ks.length + 1 := List.length_insertIdx_of_le_length hj k
  cases hb with
  | leaf hk =>
    refine .leaf ⟨?_, by omega⟩
    rcases hk.1 with h | h
    · exact .inl h
    · exact .inr (by omega)

/-- A leaf owns only its page. -/
theorem owns_leaf {p x : Nat} {ks : List (BitVec 32)} (h : Owns p (.node x true ks [])) : p = x := by
  cases h with
  | here => rfl
  | child hc _ => simp at hc

/-- The context of `insert_nonfull` is determined by the memory and the root page. -/
theorem NFPre.unique {B : ByteArray} {t t' : Nat} {φ φ' : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d : Nat} {X X' : Tree} {k : BitVec 32}
    (h : NFPre B t φ lo hi r d X k) (h' : NFPre B t' φ' lo hi r d X' k) (hp : X.page = X'.page) :
    t' = t ∧ φ' = φ ∧ X' = X := by
  have ht : t' = t := by
    have e := congrArg BitVec.toNat (h'.1.h0.symm.trans h.1.h0)
    rwa [toNat_ofNat_lt (by have := h'.1.ht'; omega),
      toNat_ofNat_lt (by have := h.1.ht'; omega)] at e
  refine ⟨ht, h.1.hfree.1.1.unique h'.1.hfree.1.1, ?_⟩
  exact Repr.unique h'.1.hR h.1.hR hp.symm (fun p hp' => by have := (h'.1.hpg p hp').2.1; omega)
    (fun p hp' => by have := (h.1.hpg p hp').2.1; omega)

/-- A leaf without children is distinct. -/
theorem distinct_leaf (x : Nat) (ks : List (BitVec 32)) : Distinct (.node x true ks []) :=
  .node (fun _ h => by simp at h) List.Pairwise.nil (fun _ h => by simp at h)

/-- **Inserting into a leaf**: after `ba_insert` wrote the leaf's keys with `k` at its
`oba_find` index (and nothing else), the leaf is a subtree again and an update adding `k`. -/
theorem leaf_step {B B' : ByteArray} {t : Nat} {φ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x j : Nat} {kx : List (BitVec 32)}
    {k : BitVec 32} (h : NFPre B t φ lo hi r d (.node x true kx []) k) (hF : FindsAt kx k j)
    (A : Agree B B' fun i => page * x + 4 ≤ i ∧ i < page * x + 4 + (4 + 4 * 8090))
    (hK : BA B' (page * x + 4) 8090 (kx.insertIdx j k)) :
    Sub B' t φ lo hi r d (.node x true (kx.insertIdx j k) []) ∧
      Upd B B' φ φ (.node x true kx []) (.node x true (kx.insertIdx j k) []) (· = k) := by
  obtain ⟨hS, hn, hw, hk⟩ := h
  have hx : PageOK B x := hS.hpg x .here
  have hx1 : 1 ≤ x := hx.1
  have hnot : k ∉ kx := fun hm => hk (.here hm)
  have hs := insert_sorted hS.ho.keys.1 hF hnot
  have hl := hS.hR.leaf_iff
  have hlw : wd B' (page * x) = wd B (page * x) :=
    A.wd_eq (by intro i h1 h2 hr; simp only [page] at *; omega)
  have hown : ∀ p, Owns p (.node x true (kx.insertIdx j k) []) → p = x := fun p hp => owns_leaf hp
  refine ⟨⟨hS.ht, hS.ht', (A.wd_eq ?_).trans hS.h0, A.1 ▸ hS.hsz, hS.hfree.agree A ?_,
    fun q hq => ⟨(hS.hfok q hq).1.mono (le_of_eq A.1.symm), fun hq' => (hS.hfok q hq).2
      ((hown _ hq') ▸ .here)⟩, .leaf (hlw ▸ hl.1.1 rfl) ⟨⟨hK, sortedS_of_strict hs⟩,
      nodup_of_strict hs⟩, leaf_ordered hS.ho hw hF hnot, leaf_balanced hS.hb hn hF.1,
    distinct_leaf _ _, fun p hp => (hown p hp) ▸ hx.mono (le_of_eq A.1.symm)⟩,
    ⟨rfl, List.Sublist.refl _, A.wd_eq ?_, le_of_eq A.1.symm, fun p hp => .inl ((hown p hp) ▸ .here),
      A.unchanged fun i hr => .inr (.inl ?_), fun k' => leaf_inTree hF.1⟩⟩
  · intro i h1 h2 hr; simp only [page] at *; omega
  · intro i h1 h2 hr; simp only [page] at *; omega
  · intro i h1 h2 hr; simp only [page] at *; omega
  · have e : i / page = x := div_page (by omega) (by simp only [page] at *; omega)
    rw [e]
    exact .here

end Silmaril.WasmSpec.BTree.V2
