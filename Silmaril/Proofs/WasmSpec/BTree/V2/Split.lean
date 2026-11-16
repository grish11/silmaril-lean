module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Specs
public import Silmaril.Proofs.WasmSpec.BTree.V2.Trees

/-!
# The B-tree library, version 2: splitting a full child, abstractly

Pure facts about `Tree.splitChild` (CLRS `B-TREE-SPLIT-CHILD` on abstract trees): its explicit
form, that it keeps the keys (`splitChild_inTree`), adds the page `z` (`splitChild_owns`),
and keeps order (`splitChild_ordered`), balance (`splitChild_balanced`) and distinct pages
(`splitChild_distinct`); and the same facts for replacing one child of a node
(`ordered_set`, `balanced_set`, `distinct_set`, `inTree_set`, `owns_set`), which the
insertion proof uses after a recursive call.

The children's bounds of `Ordered` are handled through `Kids` (the children part of
`Ordered`) and its two cons rules (`kids_one`, `kids_cons`), so that the split is an
induction on the child index.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-! ## Lists -/

/-- Inserting at index `i` is cutting the list there. -/
theorem insertIdx_take_drop {α : Type} {l : List α} {i : Nat} (a : α) (h : i ≤ l.length) :
    l.insertIdx i a = l.take i ++ a :: l.drop i := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons b l =>
      have h' : i ≤ l.length := by simpa using h
      simp [List.insertIdx_succ_cons, ih h']

/-- Setting index `i` is cutting the list around it. -/
theorem set_eq_take_drop {α : Type} {l : List α} {i : Nat} (a : α) (h : i < l.length) :
    l.set i a = l.take i ++ a :: l.drop (i + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left_iff.mpr (fun hn => absurd h hn)]

/-- The children after a split, cut around the two halves. -/
theorem split_children_eq {α : Type} {cs : List α} {i : Nat} (y' z' : α) (h : i < cs.length) :
    (cs.set i y').insertIdx (i + 1) z' = cs.take i ++ y' :: z' :: cs.drop (i + 1) := by
  have hl : i + 1 ≤ (cs.set i y').length := by simp; omega
  rw [insertIdx_take_drop z' hl, set_eq_take_drop y' h]
  have ht : i = (cs.take i).length := by simp; omega
  have e1 : (cs.take i ++ y' :: cs.drop (i + 1)).take (i + 1) = cs.take i ++ [y'] := by
    rw [List.take_append, ← ht]
    simp
  have e2 : (cs.take i ++ y' :: cs.drop (i + 1)).drop (i + 1) = cs.drop (i + 1) := by
    rw [List.drop_append, ← ht]
    simp
  rw [e1, e2]
  simp

/-- A list cut around its element `i`. -/
theorem eq_take_getElem_drop {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    l = l.take i ++ l[i] :: l.drop (i + 1) := by
  rw [List.getElem_cons_drop h, List.take_append_drop]

/-! ## The children part of `Ordered` -/

/-- **The children of an ordered node** with keys `ks` within `(lo, hi)`: child `j` lies
between keys `j - 1` and `j`. -/
def Kids (lo hi : Option (BitVec 32)) (ks : List (BitVec 32)) (cs : List Tree) : Prop :=
  ∀ j (h : j < cs.length), Ordered (if j = 0 then lo else ks[j - 1]?)
    (if j = ks.length then hi else ks[j]?) cs[j]

/-- `Ordered` of a node, as its parts. -/
theorem ordered_node_iff {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} :
    Ordered lo hi (.node x l ks cs) ↔ (ks.Pairwise fun a b => a.toInt < b.toInt) ∧
      (∀ k ∈ ks, Within lo hi k) ∧ cs.length = (if l then 0 else ks.length + 1) ∧
      Kids lo hi ks cs := by
  constructor
  · intro h
    cases h with
    | mk hs hw hlen hc => exact ⟨hs, hw, hlen, hc⟩
  · rintro ⟨hs, hw, hlen, hc⟩
    exact .mk hs hw hlen hc

/-- A node without children has no children to order. -/
theorem kids_nil {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} : Kids lo hi ks [] :=
  fun _ h => absurd h (by simp)

/-- One child and no keys: the child lies within the node's bounds. -/
theorem kids_one {lo hi : Option (BitVec 32)} {c : Tree} :
    Kids lo hi [] [c] ↔ Ordered lo hi c := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simpa using h

/-- The lower bound of child `j + 1` below key `k`. -/
theorem lb_cons {lo : Option (BitVec 32)} {k : BitVec 32} {ks : List (BitVec 32)} (j : Nat) :
    (if j + 1 = 0 then lo else (k :: ks)[j + 1 - 1]?) =
      (if j = 0 then some k else ks[j - 1]?) := by
  cases j <;> simp

/-- The upper bound of child `j + 1` below key `k`. -/
theorem ub_cons {hi : Option (BitVec 32)} {k : BitVec 32} {ks : List (BitVec 32)} (j : Nat) :
    (if j + 1 = (k :: ks).length then hi else (k :: ks)[j + 1]?) =
      (if j = ks.length then hi else ks[j]?) := by
  simp

/-- **The cons rule of `Kids`**: the first child lies below the first key, the others form
the children of the remaining keys. -/
theorem kids_cons {lo hi : Option (BitVec 32)} {k : BitVec 32} {ks : List (BitVec 32)}
    {c : Tree} {cs : List Tree} :
    Kids lo hi (k :: ks) (c :: cs) ↔ Ordered lo (some k) c ∧ Kids (some k) hi ks cs := by
  constructor
  · intro h
    have e0 : Ordered (if 0 = 0 then lo else (k :: ks)[0 - 1]?)
        (if 0 = (k :: ks).length then hi else (k :: ks)[0]?) (c :: cs)[0] := h 0 (by simp)
    have e1 : (if 0 = (k :: ks).length then hi else (k :: ks)[0]?) = some k := by simp
    rw [e1] at e0
    refine ⟨e0, fun j hj => ?_⟩
    have e := h (j + 1) (by simp; omega)
    rwa [lb_cons, ub_cons] at e
  · rintro ⟨h0, h⟩ j hj
    cases j with
    | zero =>
      show Ordered (if 0 = 0 then lo else _) (if 0 = (k :: ks).length then hi else (k :: ks)[0]?) c
      simpa using h0
    | succ j =>
      have e := h j (by simpa using hj)
      rw [← lb_cons (lo := lo), ← ub_cons (hi := hi)] at e
      exact e

/-- **Cutting `Kids` at a key `m`**: with one child more than keys on the left. -/
theorem kids_append {L U : Option (BitVec 32)} {m : BitVec 32} {ks₁ ks₂ : List (BitVec 32)}
    {cs₁ cs₂ : List Tree} (hl : cs₁.length = ks₁.length + 1) :
    Kids L U (ks₁ ++ m :: ks₂) (cs₁ ++ cs₂) ↔ Kids L (some m) ks₁ cs₁ ∧ Kids (some m) U ks₂ cs₂ := by
  induction ks₁ generalizing L cs₁ with
  | nil =>
    obtain ⟨c, rfl⟩ : ∃ c, cs₁ = [c] := List.length_eq_one_iff.1 (by simpa using hl)
    show Kids L U (m :: ks₂) (c :: cs₂) ↔ _
    rw [kids_cons, kids_one]
  | cons k ks ih =>
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, cs₁ = c :: cs :=
      List.exists_cons_of_length_eq_add_one (by simpa using hl)
    have hl' : cs.length = ks.length + 1 := by simpa using hl
    show Kids L U (k :: (ks ++ m :: ks₂)) (c :: (cs ++ cs₂)) ↔ _
    rw [kids_cons, kids_cons, ih hl', and_assoc]

/-- Replacing child `j` by a tree within the same bounds. -/
theorem kids_set {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} {cs : List Tree}
    {j : Nat} {c' : Tree} (h : Kids lo hi ks cs)
    (hc : Ordered (if j = 0 then lo else ks[j - 1]?) (if j = ks.length then hi else ks[j]?) c') :
    Kids lo hi ks (cs.set j c') := by
  intro k hk
  rw [List.getElem_set]
  by_cases hjk : j = k
  · subst hjk
    simpa using hc
  · simpa [hjk] using h k (by simpa using hk)

/-! ## The two halves of a full child -/

/-- The median of a full node's keys is key `t - 1`. -/
theorem median_eq {ky : List (BitVec 32)} {t : Nat} (ht : 1 ≤ t) (hk : ky.length = 2 * t - 1) :
    ky.getD (t - 1) 0 = ky[t - 1]'(by omega) :=
  getD_of_lt _ (by omega)

/-- The keys of a full node, cut at the median. -/
theorem keys_cut {ky : List (BitVec 32)} {t : Nat} (ht : 1 ≤ t) (hk : ky.length = 2 * t - 1) :
    ky = ky.take (t - 1) ++ ky.getD (t - 1) 0 :: ky.drop t := by
  have h : t - 1 < ky.length := by omega
  have e : t - 1 + 1 = t := by omega
  rw [median_eq ht hk]
  conv => lhs; rw [eq_take_getElem_drop h]
  rw [e]

/-- The median is a key of the full node. -/
theorem median_mem {ky : List (BitVec 32)} {t : Nat} (ht : 1 ≤ t) (hk : ky.length = 2 * t - 1) :
    ky.getD (t - 1) 0 ∈ ky := by
  rw [median_eq ht hk]
  exact List.getElem_mem _

/-- Strictly increasing keys cut at the median: the halves are increasing, below and above
it. -/
theorem halves_pairwise {ky : List (BitVec 32)} {t : Nat} (ht : 1 ≤ t)
    (hk : ky.length = 2 * t - 1) (hs : ky.Pairwise fun a b => a.toInt < b.toInt) :
    ((ky.take (t - 1)).Pairwise fun a b => a.toInt < b.toInt) ∧
      (∀ a ∈ ky.take (t - 1), a.toInt < (ky.getD (t - 1) 0).toInt) ∧
      ((ky.drop t).Pairwise fun a b => a.toInt < b.toInt) ∧
      (∀ b ∈ ky.drop t, (ky.getD (t - 1) 0).toInt < b.toInt) := by
  have hs' : (ky.take (t - 1) ++ ky.getD (t - 1) 0 :: ky.drop t).Pairwise
      fun a b => a.toInt < b.toInt := keys_cut ht hk ▸ hs
  obtain ⟨hA, hB, hAB⟩ := List.pairwise_append.1 hs'
  obtain ⟨hm, hD⟩ := List.pairwise_cons.1 hB
  exact ⟨hA, fun a ha => hAB a ha _ (List.mem_cons_self ..), hD, hm⟩

/-- The keys of the halves are within the bounds of the halves. -/
theorem halves_within {L U : Option (BitVec 32)} {ky : List (BitVec 32)} {t : Nat} (ht : 1 ≤ t)
    (hk : ky.length = 2 * t - 1) (hs : ky.Pairwise fun a b => a.toInt < b.toInt)
    (hw : ∀ k ∈ ky, Within L U k) :
    (∀ a ∈ ky.take (t - 1), Within L (some (ky.getD (t - 1) 0)) a) ∧
      (∀ b ∈ ky.drop t, Within (some (ky.getD (t - 1) 0)) U b) := by
  obtain ⟨-, hlt, -, hgt⟩ := halves_pairwise ht hk hs
  refine ⟨fun a ha => ⟨(hw a (List.mem_of_mem_take ha)).1, fun h hh => ?_⟩,
    fun b hb => ⟨fun l hl => ?_, (hw b (List.mem_of_mem_drop hb)).2⟩⟩
  · obtain rfl : ky.getD (t - 1) 0 = h := Option.some.inj hh
    exact hlt a ha
  · obtain rfl : ky.getD (t - 1) 0 = l := Option.some.inj hl
    exact hgt b hb

/-- The children of the halves of a full node lie within the halves' bounds. -/
theorem halves_kids {L U : Option (BitVec 32)} {ly : Bool} {ky : List (BitVec 32)}
    {cy : List Tree} {t : Nat} (ht : 1 ≤ t) (hk : ky.length = 2 * t - 1)
    (hlen : cy.length = if ly then 0 else ky.length + 1) (hK : Kids L U ky cy) :
    Kids L (some (ky.getD (t - 1) 0)) (ky.take (t - 1)) (cy.take t) ∧
      Kids (some (ky.getD (t - 1) 0)) U (ky.drop t) (cy.drop t) := by
  cases ly
  · have hc : cy = cy.take t ++ cy.drop t := (List.take_append_drop t cy).symm
    have hl : (cy.take t).length = (ky.take (t - 1)).length + 1 := by simp at hlen ⊢; omega
    have hK' : Kids L U (ky.take (t - 1) ++ ky.getD (t - 1) 0 :: ky.drop t)
        (cy.take t ++ cy.drop t) := by rw [← keys_cut ht hk, ← hc]; exact hK
    exact (kids_append hl).1 hK'
  · have hc : cy = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    rw [hc, List.take_nil, List.drop_nil]
    exact ⟨kids_nil, kids_nil⟩

/-- **The halves of a full child are ordered**: the left one below the median, the right one
above it. -/
theorem halves_ordered {L U : Option (BitVec 32)} {y z : Nat} {ly : Bool}
    {ky : List (BitVec 32)} {cy : List Tree} {t : Nat} (ht : 1 ≤ t)
    (hk : ky.length = 2 * t - 1) (ho : Ordered L U (.node y ly ky cy)) :
    Ordered L (some (ky.getD (t - 1) 0)) (.node y ly (ky.take (t - 1)) (cy.take t)) ∧
      Ordered (some (ky.getD (t - 1) 0)) U (.node z ly (ky.drop t) (cy.drop t)) := by
  obtain ⟨hs, hw, hlen, hK⟩ := ordered_node_iff.1 ho
  obtain ⟨hA, -, hD, -⟩ := halves_pairwise ht hk hs
  obtain ⟨hwA, hwD⟩ := halves_within ht hk hs hw
  obtain ⟨hKA, hKD⟩ := halves_kids ht hk hlen hK
  have hlA : (cy.take t).length = if ly then 0 else (ky.take (t - 1)).length + 1 := by
    cases ly
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_take] at hlen ⊢
      omega
    · simp only [↓reduceIte, List.length_eq_zero_iff] at hlen ⊢
      rw [hlen, List.take_nil]
  have hlD : (cy.drop t).length = if ly then 0 else (ky.drop t).length + 1 := by
    cases ly
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_drop] at hlen ⊢
      omega
    · simp only [↓reduceIte, List.length_eq_zero_iff] at hlen ⊢
      rw [hlen, List.drop_nil]
  exact ⟨ordered_node_iff.2 ⟨hA, hwA, hlA, hKA⟩, ordered_node_iff.2 ⟨hD, hwD, hlD, hKD⟩⟩

/-! ## Splitting, abstractly -/

/-- **`Kids` after the split of child `i`**, for halves `y'` and `z'` that are ordered below
and above the median `m` whenever the child is ordered. -/
theorem kids_split {hi : Option (BitVec 32)} {m : BitVec 32} {y' z' : Tree} :
    ∀ (i : Nat) (lo : Option (BitVec 32)) (kx : List (BitVec 32)) (cs : List Tree)
      (hl : cs.length = kx.length + 1) (hlt : i < cs.length), Kids lo hi kx cs →
      (∀ L U, Ordered L U cs[i] → Ordered L (some m) y' ∧ Ordered (some m) U z') →
      Kids lo hi (kx.insertIdx i m) ((cs.set i y').insertIdx (i + 1) z')
  | 0, lo, [], [c], _, _, hK, hy => by
    obtain ⟨h1, h2⟩ := hy lo hi (kids_one.1 hK)
    show Kids lo hi [m] [y', z']
    exact kids_cons.2 ⟨h1, kids_one.2 h2⟩
  | 0, lo, k :: K, c :: C, _, _, hK, hy => by
    obtain ⟨hc, hC⟩ := kids_cons.1 hK
    obtain ⟨h1, h2⟩ := hy lo (some k) hc
    show Kids lo hi (m :: k :: K) (y' :: z' :: C)
    exact kids_cons.2 ⟨h1, kids_cons.2 ⟨h2, hC⟩⟩
  | i + 1, lo, k :: K, c :: C, hl, hi', hK, hy => by
    obtain ⟨hc, hC⟩ := kids_cons.1 hK
    have ih := kids_split i (some k) K C (by simpa using hl) (by simpa using hi') hC hy
    show Kids lo hi (k :: K.insertIdx i m) (c :: (C.set i y').insertIdx (i + 1) z')
    exact kids_cons.2 ⟨hc, ih⟩
  | 0, _, [], [], hl, _, _, _ => absurd hl (by simp)
  | 0, _, _ :: _, [], hl, _, _, _ => absurd hl (by simp)
  | 0, _, [], _ :: _ :: _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, _, _, [], _, hi', _, _ => absurd hi' (by simp)
  | i + 1, _, [], [_], _, hi', _, _ => absurd hi' (by simp)
  | _ + 1, _, [], _ :: _ :: _, hl, _, _, _ => absurd hl (by simp)

/-- The explicit form of `Tree.splitChild`. -/
theorem splitChild_eq {t z x : Nat} {l : Bool} {kx : List (BitVec 32)} {cs : List Tree} {i y : Nat}
    {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} (hi : i < cs.length)
    (hy : cs[i] = .node y ly ky cy) :
    (Tree.node x l kx cs).splitChild t z i = .node x l (kx.insertIdx i (ky.getD (t - 1) 0))
      ((cs.set i (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (i + 1)
        (.node z ly (ky.drop t) (cy.drop t))) := by
  simp [Tree.splitChild, List.getElem?_eq_getElem hi, hy]

/-- The page of a split node is unchanged. -/
theorem splitChild_page {t z : Nat} {X : Tree} {i : Nat} : (X.splitChild t z i).page = X.page := by
  obtain ⟨x, l, kx, cs⟩ := X
  cases h : cs[i]? with
  | none => simp [Tree.splitChild, h]
  | some c =>
    obtain ⟨y, ly, ky, cy⟩ := c
    simp [Tree.splitChild, h, Tree.page]

/-- The children of a split node, cut around the two halves. -/
theorem splitChild_children {t z : Nat} {cs : List Tree} {i y : Nat} {ly : Bool}
    {ky : List (BitVec 32)} {cy : List Tree} (hi : i < cs.length) :
    (cs.set i (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (i + 1)
        (.node z ly (ky.drop t) (cy.drop t)) =
      cs.take i ++ .node y ly (ky.take (t - 1)) (cy.take t) ::
        .node z ly (ky.drop t) (cy.drop t) :: cs.drop (i + 1) :=
  split_children_eq _ _ hi

/-- Below key `i - 1` of increasing keys means below all keys before `i`. -/
theorem lt_of_take {lo : Option (BitVec 32)} {kx : List (BitVec 32)} {i : Nat} {m : BitVec 32}
    (hs : kx.Pairwise fun a b => a.toInt < b.toInt) (hi : i ≤ kx.length)
    (hlo : ∀ l, (if i = 0 then lo else kx[i - 1]?) = some l → l.toInt < m.toInt) :
    ∀ a ∈ kx.take i, a.toInt < m.toInt := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ h : j < (kx.take i).length, (kx.take i)[j] = a :=
    List.getElem_of_mem ha
  have hji : j < i := by simp at hj; omega
  have hi0 : i ≠ 0 := by omega
  have hb : (kx[i - 1]'(by omega)).toInt < m.toInt := hlo _ (by simp [hi0])
  have hle : (kx[j]'(by omega)).toInt ≤ (kx[i - 1]'(by omega)).toInt := by
    rcases Nat.lt_or_ge j (i - 1) with h | h
    · exact le_of_lt (List.pairwise_iff_getElem.1 hs j (i - 1) (by omega) (by omega) h)
    · have e : j = i - 1 := by omega
      subst e
      exact le_refl _
  simp only [List.getElem_take]
  omega

/-- Above key `i` of increasing keys means above all keys from `i` on. -/
theorem gt_of_drop {hi' : Option (BitVec 32)} {kx : List (BitVec 32)} {i : Nat} {m : BitVec 32}
    (hs : kx.Pairwise fun a b => a.toInt < b.toInt) (hi : i ≤ kx.length)
    (hhi : ∀ h, (if i = kx.length then hi' else kx[i]?) = some h → m.toInt < h.toInt) :
    ∀ b ∈ kx.drop i, m.toInt < b.toInt := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ h : j < (kx.drop i).length, (kx.drop i)[j] = b :=
    List.getElem_of_mem hb
  have hil : i < kx.length := by simp at hj; omega
  have hb : m.toInt < kx[i].toInt := hhi _ (by simp [show i ≠ kx.length by omega, hil])
  have hij : i + j < kx.length := by simp at hj; omega
  have hle : kx[i].toInt ≤ kx[i + j].toInt := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      exact le_refl _
    · exact le_of_lt (List.pairwise_iff_getElem.1 hs i (i + j) hil (by simp at hj; omega) (by omega))
  simp only [List.getElem_drop]
  omega

/-- A key strictly between keys `i - 1` and `i` keeps the keys increasing when inserted at
`i`. -/
theorem pairwise_insertIdx {lo hi : Option (BitVec 32)} {kx : List (BitVec 32)} {i : Nat}
    {m : BitVec 32} (hs : kx.Pairwise fun a b => a.toInt < b.toInt) (hil : i ≤ kx.length)
    (hw : Within (if i = 0 then lo else kx[i - 1]?) (if i = kx.length then hi else kx[i]?) m) :
    (kx.insertIdx i m).Pairwise fun a b => a.toInt < b.toInt := by
  have hcut : kx = kx.take i ++ kx.drop i := (List.take_append_drop i kx).symm
  have hs' : (kx.take i ++ kx.drop i).Pairwise fun a b => a.toInt < b.toInt := hcut ▸ hs
  obtain ⟨hA, hD, hAD⟩ := List.pairwise_append.1 hs'
  have hlt : ∀ a ∈ kx.take i, a.toInt < m.toInt := lt_of_take hs hil hw.1
  have hgt : ∀ b ∈ kx.drop i, m.toInt < b.toInt := gt_of_drop hs hil hw.2
  rw [insertIdx_take_drop m hil]
  refine List.pairwise_append.2 ⟨hA, List.pairwise_cons.2 ⟨hgt, hD⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hlt a ha
  · exact hAD a ha b hb

/-- The number of children after a split. -/
theorem length_split_children {α : Type} {cs : List α} {i : Nat} (a b : α) (h : i < cs.length) :
    ((cs.set i a).insertIdx (i + 1) b).length = cs.length + 1 := by
  rw [split_children_eq a b h]
  simp
  omega

/-- **Splitting keeps the order** of a node whose child `i` is full. -/
theorem splitChild_ordered {lo hi : Option (BitVec 32)} {t z x : Nat} {kx : List (BitVec 32)}
    {cs : List Tree} {i y : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree}
    (ht : 1 ≤ t) (hic : i < cs.length) (hy : cs[i] = .node y ly ky cy)
    (hk : ky.length = 2 * t - 1) (ho : Ordered lo hi (.node x false kx cs)) :
    Ordered lo hi ((Tree.node x false kx cs).splitChild t z i) := by
  obtain ⟨hs, hw, hlen, hK⟩ := ordered_node_iff.1 ho
  have hlen' : cs.length = kx.length + 1 := by simpa using hlen
  have hil : i ≤ kx.length := by omega
  have hoy : Ordered (if i = 0 then lo else kx[i - 1]?) (if i = kx.length then hi else kx[i]?)
      (.node y ly ky cy) := hy ▸ hK i hic
  have hm : Within (if i = 0 then lo else kx[i - 1]?) (if i = kx.length then hi else kx[i]?)
      (ky.getD (t - 1) 0) := (ordered_node_iff.1 hoy).2.1 _ (median_mem ht hk)
  have hwm : Within lo hi (ky.getD (t - 1) 0) := ho.within_of_child hic hm
  rw [splitChild_eq hic hy]
  refine ordered_node_iff.2 ⟨pairwise_insertIdx hs hil hm, fun k hk' => ?_, ?_,
    kids_split i lo kx cs hlen' hic hK fun L U h => halves_ordered ht hk (hy ▸ h)⟩
  · rcases (List.mem_insertIdx hil).1 hk' with rfl | hk'
    · exact hwm
    · exact hw k hk'
  · rw [length_split_children _ _ hic]
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_insertIdx, hil]
    omega

/-- **The halves of a full child are balanced** at its height. -/
theorem halves_balanced {t d y z : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree}
    (ht : 2 ≤ t) (hk : ky.length = 2 * t - 1) (hb : Balanced t false d (.node y ly ky cy)) :
    Balanced t false d (.node y ly (ky.take (t - 1)) (cy.take t)) ∧
      Balanced t false d (.node z ly (ky.drop t) (cy.drop t)) := by
  have hA : (false = true ∨ t - 1 ≤ (ky.take (t - 1)).length) ∧
      (ky.take (t - 1)).length ≤ 2 * t - 1 := ⟨.inr (by simp; omega), by simp; omega⟩
  have hD : (false = true ∨ t - 1 ≤ (ky.drop t).length) ∧ (ky.drop t).length ≤ 2 * t - 1 :=
    ⟨.inr (by simp; omega), by simp; omega⟩
  cases hb with
  | leaf _ =>
    simp only [List.take_nil, List.drop_nil]
    exact ⟨.leaf hA, .leaf hD⟩
  | inner _ hc =>
    exact ⟨.inner hA fun c h => hc c (List.mem_of_mem_take h),
      .inner hD fun c h => hc c (List.mem_of_mem_drop h)⟩

/-- **Splitting keeps the balance** of a non-full node whose child `i` is full. -/
theorem splitChild_balanced {r : Bool} {t d z x : Nat} {kx : List (BitVec 32)} {cs : List Tree}
    {i y : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} (ht : 2 ≤ t)
    (hi : i < cs.length) (hlen : cs.length = kx.length + 1) (hy : cs[i] = .node y ly ky cy)
    (hk : ky.length = 2 * t - 1) (hkx : kx.length < 2 * t - 1)
    (hb : Balanced t r d (.node x false kx cs)) :
    Balanced t r d ((Tree.node x false kx cs).splitChild t z i) := by
  have hil : i ≤ kx.length := by omega
  have hlk : (kx.insertIdx i (ky.getD (t - 1) 0)).length = kx.length + 1 := by
    simp [List.length_insertIdx, hil]
  rw [splitChild_eq hi hy]
  cases hb with
  | inner hk0 hc =>
    have hyb : Balanced t false _ (.node y ly ky cy) := hy ▸ hc _ (List.getElem_mem hi)
    obtain ⟨h1, h2⟩ := halves_balanced (z := z) ht hk hyb
    refine .inner ⟨hk0.1.imp_right fun h => by omega, by omega⟩ fun c hc' => ?_
    have hl' : i + 1 ≤ (cs.set i (.node y ly (ky.take (t - 1)) (cy.take t))).length := by
      simp; omega
    rcases (List.mem_insertIdx hl').1 hc' with rfl | hc'
    · exact h2
    · rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
      · exact hc c hc'
      · exact h1

/-! ## Keys and pages of a split -/

/-- A key of a full node is in its left half, the median or its right half. -/
theorem mem_keys_cut {ky : List (BitVec 32)} {t : Nat} {k : BitVec 32} (ht : 1 ≤ t)
    (hk : ky.length = 2 * t - 1) :
    k ∈ ky ↔ k ∈ ky.take (t - 1) ∨ k = ky.getD (t - 1) 0 ∨ k ∈ ky.drop t := by
  have e : k ∈ ky ↔ k ∈ ky.take (t - 1) ++ ky.getD (t - 1) 0 :: ky.drop t := by
    rw [← keys_cut ht hk]
  rw [e, List.mem_append, List.mem_cons]

/-- A child is in the first `t` children or in the rest. -/
theorem mem_take_drop {α : Type} {l : List α} {t : Nat} {c : α} :
    c ∈ l ↔ c ∈ l.take t ∨ c ∈ l.drop t := by
  rw [← List.mem_append, List.take_append_drop]

/-- The pages of a node: its own and its children's. -/
theorem owns_node_iff {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} :
    Owns p (.node x l ks cs) ↔ p = x ∨ ∃ c ∈ cs, Owns p c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | here => exact .inl rfl
    | child hc h => exact .inr ⟨_, hc, h⟩
  · rcases h with rfl | ⟨c, hc, h⟩
    · exact .here
    · exact .child hc h

/-- Something holds of a member of an appended list. -/
theorem exists_mem_cut0 {α : Type} {P : α → Prop} {A C : List α} :
    (∃ c ∈ A ++ C, P c) ↔ (∃ c ∈ A, P c) ∨ ∃ c ∈ C, P c := by
  simp only [List.mem_append, or_and_right, exists_or]

/-- Something holds of a member of a list cut around one element. -/
theorem exists_mem_cut1 {α : Type} {P : α → Prop} {A C : List α} {a : α} :
    (∃ c ∈ A ++ a :: C, P c) ↔ (∃ c ∈ A, P c) ∨ P a ∨ ∃ c ∈ C, P c := by
  simp only [List.mem_append, List.mem_cons, or_and_right, exists_or, exists_eq_left]

/-- Something holds of a member of a list cut around two elements. -/
theorem exists_mem_cut2 {α : Type} {P : α → Prop} {A C : List α} {a b : α} :
    (∃ c ∈ A ++ a :: b :: C, P c) ↔ (∃ c ∈ A, P c) ∨ P a ∨ P b ∨ ∃ c ∈ C, P c := by
  simp only [List.mem_append, List.mem_cons, or_and_right, exists_or, exists_eq_left]

/-- Something holds of a member of a list or of its first `t` elements or the rest. -/
theorem exists_mem_take_drop {α : Type} {P : α → Prop} {l : List α} (t : Nat) :
    (∃ c ∈ l, P c) ↔ (∃ c ∈ l.take t, P c) ∨ ∃ c ∈ l.drop t, P c := by
  rw [← exists_mem_cut0]
  rw [List.take_append_drop]

/-- Propositional rearrangements for the halves and the split. -/
theorem prop_halves (a b c d e : Prop) : ((a ∨ b) ∨ c ∨ d ∨ e) ↔ (a ∨ c ∨ d) ∨ b ∨ e := by
  tauto

theorem prop_halves_owns (a b c d : Prop) : ((a ∨ b) ∨ c ∨ d) ↔ (a ∨ b ∨ d) ∨ c := by
  tauto

theorem prop_split_inTree {m K A b c C Y : Prop} (hh : (b ∨ m ∨ c) ↔ Y) :
    ((m ∨ K) ∨ A ∨ b ∨ c ∨ C) ↔ (K ∨ A ∨ Y ∨ C) := by
  rw [← hh]
  tauto

theorem prop_split_owns {X A b c C Y z : Prop} (hh : (b ∨ c) ↔ Y ∨ z) :
    (X ∨ A ∨ b ∨ c ∨ C) ↔ ((X ∨ A ∨ Y ∨ C) ∨ z) := by
  tauto

theorem prop_set (K A C Y Q : Prop) : (K ∨ A ∨ (Y ∨ Q) ∨ C) ↔ (K ∨ A ∨ Y ∨ C) ∨ Q := by
  tauto

theorem prop_set_owns (X b A C : Prop) : (X ∨ A ∨ b ∨ C) ↔ (X ∨ b ∨ A ∨ C) := by
  tauto

/-- The keys of the halves and the median are the keys of the full node. -/
theorem halves_inTree {y z t : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree}
    {k : BitVec 32} (ht : 1 ≤ t) (hk : ky.length = 2 * t - 1) :
    (InTree k (.node y ly (ky.take (t - 1)) (cy.take t)) ∨ k = ky.getD (t - 1) 0 ∨
      InTree k (.node z ly (ky.drop t) (cy.drop t))) ↔ InTree k (.node y ly ky cy) := by
  rw [inTree_node_iff, inTree_node_iff, inTree_node_iff, mem_keys_cut ht hk,
    exists_mem_take_drop (l := cy) t]
  exact prop_halves _ _ _ _ _

/-- The pages of the halves are the pages of the full node and `z`. -/
theorem halves_owns {y z t p : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} :
    (Owns p (.node y ly (ky.take (t - 1)) (cy.take t)) ∨
      Owns p (.node z ly (ky.drop t) (cy.drop t))) ↔ Owns p (.node y ly ky cy) ∨ p = z := by
  rw [owns_node_iff, owns_node_iff, owns_node_iff, exists_mem_take_drop (l := cy) t]
  exact prop_halves_owns _ _ _ _

/-- **Splitting keeps the keys.** -/
theorem splitChild_inTree {t z x : Nat} {l : Bool} {kx : List (BitVec 32)} {cs : List Tree}
    {i y : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} {k : BitVec 32}
    (ht : 1 ≤ t) (hi : i < cs.length) (hlen : cs.length = kx.length + 1)
    (hy : cs[i] = .node y ly ky cy) (hk : ky.length = 2 * t - 1) :
    InTree k ((Tree.node x l kx cs).splitChild t z i) ↔ InTree k (.node x l kx cs) := by
  have hil : i ≤ kx.length := by omega
  have hcs : cs = cs.take i ++ .node y ly ky cy :: cs.drop (i + 1) := hy ▸ eq_take_getElem_drop hi
  have hmy : k = ky.getD (t - 1) 0 → InTree k (.node y ly ky cy) :=
    fun h => .here (h ▸ median_mem ht hk)
  have hh := halves_inTree (z := z) (cy := cy) (k := k) (y := y) (ly := ly) ht hk
  rw [splitChild_eq hi hy, splitChild_children hi, inTree_node_iff, inTree_node_iff,
    List.mem_insertIdx hil, exists_mem_cut2]
  conv => rhs; rw [hcs, exists_mem_cut1]
  exact prop_split_inTree hh

/-- **Splitting adds the page `z`.** -/
theorem splitChild_owns {t z x : Nat} {l : Bool} {kx : List (BitVec 32)} {cs : List Tree}
    {i y : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} {p : Nat}
    (hi : i < cs.length) (hy : cs[i] = .node y ly ky cy) :
    Owns p ((Tree.node x l kx cs).splitChild t z i) ↔ Owns p (.node x l kx cs) ∨ p = z := by
  have hcs : cs = cs.take i ++ .node y ly ky cy :: cs.drop (i + 1) := hy ▸ eq_take_getElem_drop hi
  have hh := halves_owns (z := z) (cy := cy) (p := p) (y := y) (ly := ly) (ky := ky) (t := t)
  rw [splitChild_eq hi hy, splitChild_children hi, owns_node_iff, owns_node_iff, exists_mem_cut2]
  conv => rhs; rw [hcs, exists_mem_cut1]
  exact prop_split_owns hh

/-! ## Distinct pages of a split -/

/-- Two trees own disjoint pages. -/
abbrev Disj (c c' : Tree) : Prop := ∀ p, Owns p c → ¬ Owns p c'

/-- `Distinct` of a node, as its parts. -/
theorem distinct_node_iff {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} :
    Distinct (.node x l ks cs) ↔ (∀ c ∈ cs, ¬ Owns x c) ∧ cs.Pairwise Disj ∧
      ∀ c ∈ cs, Distinct c := by
  constructor
  · intro h
    cases h with
    | node hx hd hc => exact ⟨hx, hd, hc⟩
  · rintro ⟨hx, hd, hc⟩
    exact .node hx hd hc

/-- Fewer pages on the left keep disjointness. -/
theorem disj_mono {a a' b : Tree} (h : ∀ p, Owns p a' → Owns p a) (hd : Disj a b) : Disj a' b :=
  fun p hp => hd p (h p hp)

/-- Fewer pages on the right keep disjointness. -/
theorem disj_mono' {a b b' : Tree} (h : ∀ p, Owns p b' → Owns p b) (hd : Disj a b) :
    Disj a b' :=
  fun p hp hb => hd p hp (h p hb)

/-- The pages of the left half are pages of the full node. -/
theorem owns_left_half {y t p : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree}
    (h : Owns p (.node y ly (ky.take (t - 1)) (cy.take t))) : Owns p (.node y ly ky cy) := by
  rcases owns_node_iff.1 h with rfl | ⟨c, hc, hp⟩
  · exact .here
  · exact .child (List.mem_of_mem_take hc) hp

/-- **The halves of a full child have distinct pages**, disjoint from each other, when `z`
is not a page of the child. -/
theorem halves_distinct {y z t : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree}
    (hd : Distinct (.node y ly ky cy)) (hz : ∀ c ∈ cy, ¬ Owns z c) (hyz : y ≠ z) :
    Distinct (.node y ly (ky.take (t - 1)) (cy.take t)) ∧
      Distinct (.node z ly (ky.drop t) (cy.drop t)) ∧
      Disj (.node y ly (ky.take (t - 1)) (cy.take t)) (.node z ly (ky.drop t) (cy.drop t)) := by
  obtain ⟨hx, hpw, hc⟩ := distinct_node_iff.1 hd
  have hpw' : (cy.take t ++ cy.drop t).Pairwise Disj := by rw [List.take_append_drop]; exact hpw
  obtain ⟨hA, hD, hAD⟩ := List.pairwise_append.1 hpw'
  refine ⟨distinct_node_iff.2 ⟨fun c h => hx c (List.mem_of_mem_take h), hA,
      fun c h => hc c (List.mem_of_mem_take h)⟩,
    distinct_node_iff.2 ⟨fun c h => hz c (List.mem_of_mem_drop h), hD,
      fun c h => hc c (List.mem_of_mem_drop h)⟩, fun p h1 h2 => ?_⟩
  rcases owns_node_iff.1 h1 with rfl | ⟨c, hcA, hpc⟩ <;>
    rcases owns_node_iff.1 h2 with h | ⟨c', hcD, hpc'⟩
  · exact hyz h
  · exact hx c' (List.mem_of_mem_drop hcD) hpc'
  · exact hz c (List.mem_of_mem_take hcA) (h ▸ hpc)
  · exact hAD c hcA c' hcD p hpc hpc'

/-- Replacing one child by two smaller ones (pages of the old child, and `z` for the second)
keeps the children pairwise disjoint, `z` being no page of the other children. -/
theorem pairwise_split_mid {A C : List Tree} {y y' z' : Tree} {z : Nat}
    (hpw : (A ++ y :: C).Pairwise Disj) (h1 : ∀ p, Owns p y' → Owns p y)
    (h2 : ∀ p, Owns p z' → Owns p y ∨ p = z) (hz : ∀ c ∈ A ++ C, ¬ Owns z c)
    (hyz : Disj y' z') : (A ++ y' :: z' :: C).Pairwise Disj := by
  obtain ⟨hA, hyC, hAyC⟩ := List.pairwise_append.1 hpw
  obtain ⟨hyC1, hC⟩ := List.pairwise_cons.1 hyC
  have hz'b : ∀ b ∈ C, Disj z' b := fun b hb p hp hpb =>
    (h2 p hp).elim (fun h => hyC1 b hb p h hpb)
      (fun h => hz b (List.mem_append_right _ hb) (h ▸ hpb))
  have hy'b : ∀ b ∈ C, Disj y' b := fun b hb => disj_mono h1 (hyC1 b hb)
  have hay : ∀ a ∈ A, Disj a y' := fun a ha => disj_mono' h1 (hAyC a ha _ (List.mem_cons_self ..))
  have haz : ∀ a ∈ A, Disj a z' := fun a ha p hpa hpz => (h2 p hpz).elim
    (fun h => hAyC a ha _ (List.mem_cons_self ..) p hpa h)
    (fun h => hz a (List.mem_append_left _ ha) (h ▸ hpa))
  refine List.pairwise_append.2 ⟨hA, List.pairwise_cons.2 ⟨fun b hb => ?_,
    List.pairwise_cons.2 ⟨hz'b, hC⟩⟩, fun a ha b hb => ?_⟩
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact hyz
    · exact hy'b b hb
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact hay a ha
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact haz a ha
      · exact hAyC a ha b (List.mem_cons_of_mem _ hb)

/-- Membership in a list cut around two elements. -/
theorem mem_cut2 {α : Type} {A C : List α} {a b c : α} :
    c ∈ A ++ a :: b :: C ↔ c ∈ A ∨ c = a ∨ c = b ∨ c ∈ C := by
  simp only [List.mem_append, List.mem_cons]

/-- The other children of a node cut around child `i` are children of the node. -/
theorem mem_of_mem_cut {α : Type} {A C : List α} {a c : α} (h : c ∈ A ∨ c ∈ C) :
    c ∈ A ++ a :: C := by
  rcases h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- **Splitting keeps the pages distinct**, `z` being no page of the node. -/
theorem splitChild_distinct {t z x : Nat} {l : Bool} {kx : List (BitVec 32)} {cs : List Tree}
    {i y : Nat} {ly : Bool} {ky : List (BitVec 32)} {cy : List Tree} (hi : i < cs.length)
    (hy : cs[i] = .node y ly ky cy) (hd : Distinct (.node x l kx cs))
    (hz : ¬ Owns z (.node x l kx cs)) :
    Distinct ((Tree.node x l kx cs).splitChild t z i) := by
  obtain ⟨hx, hpw, hc⟩ := distinct_node_iff.1 hd
  have hcs : cs = cs.take i ++ .node y ly ky cy :: cs.drop (i + 1) := hy ▸ eq_take_getElem_drop hi
  have hY : Tree.node y ly ky cy ∈ cs := hy ▸ List.getElem_mem hi
  have hmem : ∀ c, c ∈ cs.take i ∨ c ∈ cs.drop (i + 1) → c ∈ cs :=
    fun c h => hcs ▸ mem_of_mem_cut h
  have hzy : ∀ c ∈ cy, ¬ Owns z c := fun c hcy h => hz (.child hY (.child hcy h))
  have hyz : y ≠ z := fun h => hz (h ▸ .child hY .here)
  obtain ⟨d1, d2, d3⟩ := halves_distinct (t := t) (ky := ky) (hc _ hY) hzy hyz
  have h2 : ∀ p, Owns p (.node z ly (ky.drop t) (cy.drop t)) → Owns p (.node y ly ky cy) ∨ p = z :=
    fun p h => (halves_owns (ky := ky)).1 (.inr h)
  have hzAC : ∀ c ∈ cs.take i ++ cs.drop (i + 1), ¬ Owns z c :=
    fun c h h' => hz (.child (hmem c (List.mem_append.1 h)) h')
  have hpw' : (cs.take i ++ .node y ly ky cy :: cs.drop (i + 1)).Pairwise Disj := hcs ▸ hpw
  rw [splitChild_eq hi hy, splitChild_children hi]
  refine distinct_node_iff.2 ⟨fun c h => ?_,
    pairwise_split_mid hpw' (fun p h => owns_left_half h) h2 hzAC d3, fun c h => ?_⟩
  · rcases mem_cut2.1 h with h | rfl | rfl | h
    · exact hx c (hmem c (.inl h))
    · exact fun h' => hx _ hY (owns_left_half h')
    · exact fun h' => (h2 x h').elim (hx _ hY) fun e => hz (e ▸ .here)
    · exact hx c (hmem c (.inr h))
  · rcases mem_cut2.1 h with h | rfl | rfl | h
    · exact hc c (hmem c (.inl h))
    · exact d1
    · exact d2
    · exact hc c (hmem c (.inr h))

/-! ## The parts of a split -/

/-- The left half keeps `t - 1` keys. -/
theorem length_left_keys {ky : List (BitVec 32)} {t : Nat} (hk : ky.length = 2 * t - 1) :
    (ky.take (t - 1)).length = t - 1 := by
  simp only [List.length_take]
  omega

/-- The right half gets `t - 1` keys. -/
theorem length_right_keys {ky : List (BitVec 32)} {t : Nat} (hk : ky.length = 2 * t - 1) :
    (ky.drop t).length = t - 1 := by
  simp only [List.length_drop]
  omega

/-- The left half of an inner node keeps `t` children. -/
theorem length_left_children {cy : List Tree} {t : Nat} (hc : cy.length = 2 * t) :
    (cy.take t).length = t := by
  simp only [List.length_take]
  omega

/-- The right half of an inner node gets `t` children. -/
theorem length_right_children {cy : List Tree} {t : Nat} (hc : cy.length = 2 * t) :
    (cy.drop t).length = t := by
  simp only [List.length_drop]
  omega

/-- The median is key `i` of the split node. -/
theorem median_key {kx : List (BitVec 32)} {i : Nat} {m : BitVec 32} (hi : i ≤ kx.length) :
    (kx.insertIdx i m)[i]? = some m := by
  have ht : (kx.take i).length = i := by simp; omega
  rw [insertIdx_take_drop m hi, List.getElem?_append_right (by omega), ht]
  simp

/-- The halves are children `i` and `i + 1` of the split node. -/
theorem split_children_get {α : Type} {cs : List α} {i : Nat} (y' z' : α) (h : i < cs.length) :
    ((cs.set i y').insertIdx (i + 1) z')[i]? = some y' ∧
      ((cs.set i y').insertIdx (i + 1) z')[i + 1]? = some z' := by
  rw [split_children_eq y' z' h]
  have ht : (cs.take i).length = i := by simp; omega
  constructor
  · rw [List.getElem?_append_right (by omega), ht]
    simp
  · rw [List.getElem?_append_right (by omega), ht]
    simp

/-! ## Replacing one child -/

/-- Replacing child `j` by a tree within its bounds keeps the order. -/
theorem ordered_set {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
    {cs : List Tree} {j : Nat} {c' : Tree} (ho : Ordered lo hi (.node x l ks cs))
    (hc : Ordered (if j = 0 then lo else ks[j - 1]?) (if j = ks.length then hi else ks[j]?) c') :
    Ordered lo hi (.node x l ks (cs.set j c')) := by
  obtain ⟨hs, hw, hlen, hK⟩ := ordered_node_iff.1 ho
  exact ordered_node_iff.2 ⟨hs, hw, by simpa using hlen, kids_set hK hc⟩

/-- Replacing a child by a tree balanced at the children's height keeps the balance. -/
theorem balanced_set {t d x : Nat} {r : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hb : Balanced t r (d + 1) (.node x false ks cs)) (hc : Balanced t false d c') :
    Balanced t r (d + 1) (.node x false ks (cs.set j c')) := by
  cases hb with
  | inner hk hcs =>
    refine .inner hk fun c h => ?_
    rcases List.mem_or_eq_of_mem_set h with h | rfl
    · exact hcs c h
    · exact hc

/-- Membership in a list with element `j` set. -/
theorem mem_set_iff {α : Type} {cs : List α} {j : Nat} {c c' : α} (hj : j < cs.length) :
    c ∈ cs.set j c' ↔ c ∈ cs.take j ∨ c = c' ∨ c ∈ cs.drop (j + 1) := by
  rw [set_eq_take_drop c' hj, List.mem_append, List.mem_cons]

/-- Replacing child `j` by a tree with the keys of the old child and those of `Q`. -/
theorem inTree_set {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} {Q : BitVec 32 → Prop} {k : BitVec 32} (hj : j < cs.length)
    (h : ∀ k, InTree k c' ↔ InTree k cs[j] ∨ Q k) :
    InTree k (.node x l ks (cs.set j c')) ↔ InTree k (.node x l ks cs) ∨ Q k := by
  have hcs : cs = cs.take j ++ cs[j] :: cs.drop (j + 1) := eq_take_getElem_drop hj
  rw [set_eq_take_drop c' hj, inTree_node_iff, inTree_node_iff, exists_mem_cut1, h k]
  conv => rhs; rw [hcs, exists_mem_cut1]
  exact prop_set _ _ _ _ _

/-- Replacing child `j`: the node's pages are its own, the new child's and the other
children's. -/
theorem owns_set {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hj : j < cs.length) :
    Owns p (.node x l ks (cs.set j c')) ↔
      p = x ∨ Owns p c' ∨ ∃ c ∈ cs.take j ++ cs.drop (j + 1), Owns p c := by
  rw [set_eq_take_drop c' hj, owns_node_iff, exists_mem_cut1, exists_mem_cut0]
  exact prop_set_owns _ _ _ _

/-- After replacing child `j`, a page is a page of the old node or of the new child. -/
theorem owns_set_old {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hj : j < cs.length) (h : Owns p (.node x l ks (cs.set j c'))) :
    Owns p (.node x l ks cs) ∨ Owns p c' := by
  rcases (owns_set hj).1 h with rfl | h | ⟨c, hc, hp⟩
  · exact .inl .here
  · exact .inr h
  · have hcs : cs = cs.take j ++ cs[j] :: cs.drop (j + 1) := eq_take_getElem_drop hj
    exact .inl (.child (hcs ▸ mem_of_mem_cut (List.mem_append.1 hc)) hp)

/-- The new child's pages are pages of the node. -/
theorem owns_set_new {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hj : j < cs.length) (h : Owns p c') : Owns p (.node x l ks (cs.set j c')) :=
  (owns_set hj).2 (.inr (.inl h))

/-- A page of the node that is not a page of the old child stays a page of the node. -/
theorem owns_set_keep {p x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hj : j < cs.length) (h : Owns p (.node x l ks cs)) (hn : ¬ Owns p cs[j]) :
    Owns p (.node x l ks (cs.set j c')) := by
  have hcs : cs = cs.take j ++ cs[j] :: cs.drop (j + 1) := eq_take_getElem_drop hj
  rcases owns_node_iff.1 h with rfl | ⟨c, hc, hp⟩
  · exact .here
  · refine (owns_set hj).2 (.inr (.inr ⟨c, ?_, hp⟩))
    rw [hcs] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact List.mem_append_left _ hc
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hp hn
      · exact List.mem_append_right _ hc

/-- **Replacing child `j` keeps the pages distinct** if the new child has distinct pages,
each a page of the old child or no page of the node. -/
theorem distinct_set {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    {c' : Tree} (hj : j < cs.length) (hd : Distinct (.node x l ks cs)) (hc : Distinct c')
    (hnew : ∀ p, Owns p c' → Owns p cs[j] ∨ ¬ Owns p (.node x l ks cs)) :
    Distinct (.node x l ks (cs.set j c')) := by
  obtain ⟨hx, hpw, hcs⟩ := distinct_node_iff.1 hd
  have hcut : cs = cs.take j ++ cs[j] :: cs.drop (j + 1) := eq_take_getElem_drop hj
  have hY : cs[j] ∈ cs := List.getElem_mem hj
  have hmem : ∀ c, c ∈ cs.take j ∨ c ∈ cs.drop (j + 1) → c ∈ cs :=
    fun c h => hcut ▸ mem_of_mem_cut h
  have hpw' : (cs.take j ++ cs[j] :: cs.drop (j + 1)).Pairwise Disj := hcut ▸ hpw
  obtain ⟨hA, hyC, hAyC⟩ := List.pairwise_append.1 hpw'
  obtain ⟨hyC1, hC⟩ := List.pairwise_cons.1 hyC
  have hcb : ∀ b, b ∈ cs.take j ∨ b ∈ cs.drop (j + 1) → Disj c' b := fun b hb p hp hpb =>
    (hnew p hp).elim (fun h => by
      rcases hb with hb | hb
      · exact hAyC b hb _ (List.mem_cons_self ..) p hpb h
      · exact hyC1 b hb p h hpb) (fun h => h (.child (hmem b hb) hpb))
  rw [set_eq_take_drop c' hj]
  refine distinct_node_iff.2 ⟨fun c h => ?_, List.pairwise_append.2 ⟨hA,
    List.pairwise_cons.2 ⟨fun b hb => hcb b (.inr hb), hC⟩, fun a ha b hb => ?_⟩, fun c h => ?_⟩
  · rcases List.mem_append.1 h with h | h
    · exact hx c (hmem c (.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact fun h' => (hnew x h').elim (hx _ hY) fun hn => hn .here
      · exact hx c (hmem c (.inr h))
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact fun p hpa hpc => hcb a (.inl ha) p hpc hpa
    · exact hAyC a ha b (List.mem_cons_of_mem _ hb)
  · rcases List.mem_append.1 h with h | h
    · exact hcs c (hmem c (.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact hc
      · exact hcs c (hmem c (.inr h))

end Silmaril.WasmSpec.BTree.V2
