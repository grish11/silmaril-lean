module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Oba

/-!
# The B-tree library, version 2: abstract trees

Facts about the abstract trees of `Silmaril.WasmSpec.BTree.V2.Defs` used by the search: the
bounds of an ordered tree's keys (`Ordered.within`), where a key not among a node's keys
lies (`inTree_child_iff`: in child `i`, the `oba_find` index), and that `oba_find`'s index
with a different key there means the key is absent (`not_mem_of_findsAt`); a tree in memory is
determined by the memory and its root page (`Repr.unique`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-- A node with a child is an inner node with one child more than keys. -/
theorem Ordered.shape {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} {j : Nat} (ho : Ordered lo hi (.node x l ks cs)) (hj : j < cs.length) :
    l = false ∧ cs.length = ks.length + 1 := by
  cases ho with
  | mk _ _ hlen _ =>
    cases l
    · exact ⟨rfl, by simpa using hlen⟩
    · simp only [↓reduceIte] at hlen
      omega

/-- The bounds of child `j` of an ordered node. -/
theorem Ordered.child {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} {j : Nat} (ho : Ordered lo hi (.node x l ks cs)) (hj : j < cs.length) :
    Ordered (if j = 0 then lo else ks[j - 1]?) (if j = ks.length then hi else ks[j]?) cs[j] := by
  cases ho with
  | mk _ _ _ hcs => exact hcs j hj

/-- The keys of an ordered node are within its bounds and strictly increasing. -/
theorem Ordered.keys {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} (ho : Ordered lo hi (.node x l ks cs)) :
    (ks.Pairwise fun a b => a.toInt < b.toInt) ∧ ∀ k ∈ ks, Within lo hi k := by
  cases ho with
  | mk hs hw _ _ => exact ⟨hs, hw⟩

/-- A key within the bounds of child `j` of an ordered node is within the node's bounds. -/
theorem Ordered.within_of_child {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} {j : Nat} {k : BitVec 32}
    (ho : Ordered lo hi (.node x l ks cs)) (hj : j < cs.length)
    (hw' : Within (if j = 0 then lo else ks[j - 1]?) (if j = ks.length then hi else ks[j]?) k) :
    Within lo hi k := by
  have hlen : cs.length = ks.length + 1 := (ho.shape hj).2
  have hw : ∀ k ∈ ks, Within lo hi k := ho.keys.2
  refine ⟨fun l' hl' => ?_, fun h' hh' => ?_⟩
  · by_cases hj0 : j = 0
    · exact hw'.1 l' (by simpa [hj0] using hl')
    · have hjk : j - 1 < ks.length := by omega
      have h1 : ks[j - 1].toInt < k.toInt := hw'.1 ks[j - 1] (by simp [hj0, hjk])
      have h2 : l'.toInt < ks[j - 1].toInt := (hw ks[j - 1] (List.getElem_mem hjk)).1 l' hl'
      omega
  · by_cases hjn : j = ks.length
    · exact hw'.2 h' (by simpa [hjn] using hh')
    · have hjk : j < ks.length := by omega
      have h1 : k.toInt < ks[j].toInt := hw'.2 ks[j] (by simp [hjn, hjk])
      have h2 : ks[j].toInt < h'.toInt := (hw ks[j] (List.getElem_mem hjk)).2 h' hh'
      omega

/-- The keys of an ordered tree lie within its bounds. -/
theorem Ordered.within {lo hi : Option (BitVec 32)} {T : Tree} {k : BitVec 32}
    (ho : Ordered lo hi T) (hk : InTree k T) : Within lo hi k := by
  induction hk generalizing lo hi with
  | here h => exact ho.keys.2 _ h
  | @child x l ks cs c hc _ ih =>
    obtain ⟨j, hj, hcj⟩ : ∃ j, ∃ h : j < cs.length, cs[j] = c := List.getElem_of_mem hc
    have hw' := ih (hcj ▸ ho.child hj)
    exact ho.within_of_child hj hw'

/-- The keys of a node: its own and its children's. -/
theorem inTree_node_iff {k : BitVec 32} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} : InTree k (.node x l ks cs) ↔ k ∈ ks ∨ ∃ c ∈ cs, InTree k c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | here h => exact .inl h
    | child hc h => exact .inr ⟨_, hc, h⟩
  · rcases h with h | ⟨c, hc, h⟩
    · exact .here h
    · exact .child hc h

/-- In an ordered node, a key `k` that is not one of the keys and lies in child `j` lies in
child `i`, the first index whose key is not below `k`. -/
theorem Ordered.index_eq {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} {k : BitVec 32} {i j : Nat}
    (ho : Ordered lo hi (.node x l ks cs)) (hF : FindsAt ks k i) (hj : j < cs.length)
    (hw' : Within (if j = 0 then lo else ks[j - 1]?) (if j = ks.length then hi else ks[j]?) k) :
    j = i := by
  have hlen : cs.length = ks.length + 1 := (ho.shape hj).2
  obtain ⟨hil, hlt, hge⟩ := hF
  rcases Nat.lt_trichotomy j i with hji | hji | hji
  · have hjk : j < ks.length := by omega
    have h1 : k.toInt < ks[j].toInt := hw'.2 ks[j] (by simp [show j ≠ ks.length by omega, hjk])
    have h2 : (ks.getD j 0).toInt < k.toInt := hlt j hji
    rw [getD_of_lt _ hjk] at h2
    omega
  · exact hji
  · have hjk : j - 1 < ks.length := by omega
    have h1 : ks[j - 1].toInt < k.toInt := hw'.1 ks[j - 1] (by simp [show j ≠ 0 by omega, hjk])
    have h2 : k.toInt ≤ (ks.getD (j - 1) 0).toInt := hge (j - 1) (by omega) hjk
    rw [getD_of_lt _ hjk] at h2
    omega

/-- **The child-index lemma**: in an ordered node, a key `k` that is not one of the keys
lies in the tree iff it lies in child `i`, where `i` is the first index whose key is not
below `k`. -/
theorem inTree_child_iff {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} {k : BitVec 32} {i : Nat}
    (ho : Ordered lo hi (.node x l ks cs)) (hF : FindsAt ks k i) (hk : k ∉ ks)
    (hi : i < cs.length) : InTree k (.node x l ks cs) ↔ InTree k cs[i] := by
  refine ⟨fun h => ?_, fun h => .child (List.getElem_mem hi) h⟩
  obtain ⟨c, hc, h⟩ : ∃ c ∈ cs, InTree k c := (inTree_node_iff.1 h).resolve_left hk
  obtain ⟨j, hj, hcj⟩ : ∃ j, ∃ h : j < cs.length, cs[j] = c := List.getElem_of_mem hc
  have hw' := (ho.child hj).within (hcj ▸ h)
  have hji : j = i := ho.index_eq hF hj hw'
  subst hji
  rwa [hcj]

/-- A key of a leaf is one of its keys. -/
theorem inTree_leaf {x : Nat} {ks : List (BitVec 32)} {k : BitVec 32} :
    InTree k (.node x true ks []) ↔ k ∈ ks := by
  refine ⟨fun h => ?_, fun h => .here h⟩
  cases h with
  | here h => exact h
  | child hc _ => simp at hc

/-- If the `oba_find` index `i` of `k` in strictly increasing keys is not a position holding
`k`, then `k` is not a key. -/
theorem not_mem_of_findsAt {ks : List (BitVec 32)} {k : BitVec 32} {i : Nat}
    (hs : ks.Pairwise fun a b => a.toInt < b.toInt) (hF : FindsAt ks k i)
    (hne : ∀ h : i < ks.length, ks[i] ≠ k) : k ∉ ks := by
  intro hk
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
  obtain ⟨hil, hlt, hge⟩ := hF
  have hlt' := hlt j
  rw [getD_of_lt _ hj] at hlt'
  rcases Nat.lt_trichotomy j i with hji | rfl | hji
  · exact absurd (hlt' hji) (lt_irrefl _)
  · exact hne hj rfl
  · have h1 := hge i (by omega) (by omega)
    rw [getD_of_lt _ (by omega)] at h1
    have h2 := List.pairwise_iff_getElem.1 hs i j (by omega) hj hji
    omega

/-- Strictly increasing keys are sorted and without duplicates. -/
theorem sortedS_of_strict {ks : List (BitVec 32)}
    (hs : ks.Pairwise fun a b => a.toInt < b.toInt) : SortedS ks :=
  hs.imp fun h => le_of_lt h

/-- The page of a tree's root is one of its pages. -/
theorem Owns.root (T : Tree) : Owns T.page T := by
  obtain ⟨x, l, ks, cs⟩ := T
  exact .here

/-- A child's pages are pages of the node. -/
theorem Owns.of_child {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {c : Tree}
    (hc : c ∈ cs) (h : Owns p c) : Owns p (.node x l ks cs) := .child hc h

/-- Equal pointers of pages below `2 ^ 32` are equal pages. -/
theorem page_eq_of_ptr {T T' : Tree} (h : T.ptr = T'.ptr) (hb : T.page < 2 ^ 32)
    (hb' : T'.page < 2 ^ 32) : T.page = T'.page := by
  have e : T.page % 2 ^ 32 = T'.page % 2 ^ 32 := by
    simpa only [Tree.ptr, BitVec.toNat_ofNat] using congrArg BitVec.toNat h
  rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at e

/-- Lists of trees with the same pointers, each determined by its root page, are equal. -/
theorem children_eq {cs cs' : List Tree} (hptr : cs'.map Tree.ptr = cs.map Tree.ptr)
    (hb : ∀ c ∈ cs, c.page < 2 ^ 32) (hb' : ∀ c ∈ cs', c.page < 2 ^ 32)
    (ih : ∀ c ∈ cs, ∀ c' ∈ cs', c.page = c'.page → c = c') : cs = cs' := by
  have hlen : cs'.length = cs.length := by simpa using congrArg List.length hptr
  refine List.ext_getElem hlen.symm fun i h₁ h₂ => ?_
  have hi : cs[i].ptr = cs'[i].ptr := by
    have e := congrArg (fun l => l[i]?) hptr
    simpa [h₁, h₂] using e.symm
  have hm : cs[i] ∈ cs := List.getElem_mem h₁
  have hm' : cs'[i] ∈ cs' := List.getElem_mem h₂
  exact ih _ hm _ hm' (page_eq_of_ptr hi (hb _ hm) (hb' _ hm'))

/-- **A tree in memory is determined by the memory and its root page** (its pages being
below `2 ^ 32`, so that they are determined by the pointers). -/
theorem Repr.unique {B : ByteArray} {T T' : Tree} (h : Repr B T) (h' : Repr B T')
    (hp : T.page = T'.page) (hb : ∀ p, Owns p T → p < 2 ^ 32)
    (hb' : ∀ p, Owns p T' → p < 2 ^ 32) : T = T' := by
  induction h generalizing T' with
  | @leaf x ks hl hk =>
    show Tree.node x true ks [] = T'
    cases h' with
    | @leaf x' ks' _ hk' =>
      have hx : x = x' := hp
      subst hx
      have hks : ks' = ks := hk.1.1.unique hk'.1.1
      rw [hks]
    | @inner x' _ _ hl' =>
      have hx : x = x' := hp
      subst hx
      exact absurd hl' hl
  | @inner x ks cs hl hk hps hc ih =>
    show Tree.node x false ks cs = T'
    cases h' with
    | @leaf x' _ hl' =>
      have hx : x = x' := hp
      subst hx
      exact absurd hl hl'
    | @inner x' ks' cs' _ hk' hps' hc' =>
      show Tree.node x false ks cs = Tree.node x' false ks' cs'
      have hx : x = x' := hp
      subst hx
      have hks : ks' = ks := hk.1.1.unique hk'.1.1
      have hcs : cs = cs' := children_eq (hps.unique hps')
        (fun c hm => hb _ (.child hm (Owns.root c))) (fun c hm => hb' _ (.child hm (Owns.root c)))
        fun c hm c' hm' he => ih c hm (hc' c' hm') he (fun p hp => hb p (.child hm hp))
          (fun p hp => hb' p (.child hm' hp))
      rw [hks, hcs]

end Silmaril.WasmSpec.BTree.V2
