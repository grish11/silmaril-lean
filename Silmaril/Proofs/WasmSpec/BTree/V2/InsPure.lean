module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Split
public import Silmaril.Proofs.WasmSpec.BTree.V2.SplitRepr
public import Silmaril.Proofs.WasmSpec.BTree.V2.Calls

/-!
# The B-tree library, version 2: subtrees in memory and their updates

`Sub B t φ lo hi r d X`: the metadata (`t` at `0`, the free pages `φ` at `8`) and a subtree
`X` in memory, ordered within `(lo, hi)`, balanced at height `d`, its pages distinct, valid
and disjoint from the free pages. `Upd B B' φ φ' X X' R`: an update of the subtree `X` (in
`B`) to `X'` (in `B'`) on the same page, taking pages only from the free list or beyond the
old memory, changing no byte outside page `0`, `X`'s pages and the free pages, adding the keys
`Q`. Updates compose (`Upd.trans`), and an update of child `j` is an update
of the node (`Upd.child`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm.Logic.Words

/-- **A subtree in memory with its allocator context.** -/
structure Sub (B : ByteArray) (t : Nat) (φ : List (BitVec 32)) (lo hi : Option (BitVec 32))
    (r : Bool) (d : Nat) (X : Tree) : Prop where
  ht : 2 ≤ t
  ht' : t ≤ 4045
  h0 : wd B 0 = BitVec.ofNat 32 t
  hsz : B.size % page = 0
  hfree : OBAnd B 8 16381 φ
  hfok : ∀ q ∈ φ, PageOK B q.toNat ∧ ¬ Owns q.toNat X
  hR : Repr B X
  ho : Ordered lo hi X
  hb : Balanced t r d X
  hd : Distinct X
  hpg : ∀ p, Owns p X → PageOK B p

/-- **An update of a subtree**: same root page, pages from the free list or beyond the old
memory, the free list shrinks, the root pointer word kept, no byte changed outside page `0`,
the old pages and the free pages; the keys `Q` added. -/
structure Upd (B B' : ByteArray) (φ φ' : List (BitVec 32)) (X X' : Tree)
    (Q : BitVec 32 → Prop) : Prop where
  same_page : X'.page = X.page
  sub : φ'.Sublist φ
  w4 : wd B' 4 = wd B 4
  size : B.size ≤ B'.size
  owns : ∀ p, Owns p X' → Owns p X ∨ (∃ q ∈ φ, q.toNat = p) ∨ B.size ≤ page * p
  frame : Unchanged B B' (Owned X φ)
  keys : ∀ k, InTree k X' ↔ InTree k X ∨ Q k

/-- A page is valid in a larger memory. -/
theorem PageOK.mono {B B' : ByteArray} {p : Nat} (h : PageOK B p) (hs : B.size ≤ B'.size) :
    PageOK B' p :=
  ⟨h.1, h.2.1, le_trans h.2.2 hs⟩

/-- A byte of the old memory is not on a page beyond it. -/
theorem not_fresh {B : ByteArray} {i : Nat} (hi : i < B.size) : ¬ B.size ≤ page * (i / page) := by
  simp only [page]
  omega

/-- The trivial update. -/
theorem Upd.refl (B : ByteArray) (φ : List (BitVec 32)) (X : Tree) : Upd B B φ φ X X fun _ => False :=
  ⟨rfl, List.Sublist.refl _, rfl, le_refl _, fun _ hp => .inl hp, Unchanged.refl _ _,
    fun _ => ⟨Or.inl, fun h => h.resolve_right id⟩⟩

/-- **Updates compose**, the first keeping the keys. -/
theorem Upd.trans {B B₁ B₂ : ByteArray} {φ φ₁ φ₂ : List (BitVec 32)} {X X₁ X₂ : Tree}
    {Q : BitVec 32 → Prop} (h₁ : Upd B B₁ φ φ₁ X X₁ fun _ => False)
    (h₂ : Upd B₁ B₂ φ₁ φ₂ X₁ X₂ Q) : Upd B B₂ φ φ₂ X X₂ Q := by
  have hφ : ∀ p, (∃ q ∈ φ₁, q.toNat = p) → ∃ q ∈ φ, q.toNat = p :=
    fun p ⟨q, hq, he⟩ => ⟨q, h₁.sub.subset hq, he⟩
  refine ⟨h₂.same_page.trans h₁.same_page, h₂.sub.trans h₁.sub, h₂.w4.trans h₁.w4, h₁.size.trans h₂.size,
    fun p hp => ?_, ⟨h₁.size.trans h₂.size, fun i hi hs => ?_⟩, fun k => ?_⟩
  · rcases h₂.owns p hp with h | h | h
    · rcases h₁.owns p h with h' | h' | h'
      · exact .inl h'
      · exact .inr (.inl h')
      · exact .inr (.inr h')
    · exact .inr (.inl (hφ p h))
    · exact .inr (.inr (le_trans h₁.size h))
  · show B₂.data.toList[i]? = B.data.toList[i]?
    have hs₁ : ¬ Owned X₁ φ₁ (i / page) := by
      rintro (h | h | h)
      · exact hs (.inl h)
      · rcases h₁.owns _ h with h' | h' | h'
        · exact hs (.inr (.inl h'))
        · exact hs (.inr (.inr h'))
        · exact not_fresh hi h'
      · exact hs (.inr (.inr (hφ _ h)))
    exact (h₂.frame.2 i (lt_of_lt_of_le hi h₁.size) hs₁).trans (h₁.frame.2 i hi hs)
  · rw [h₂.keys k, h₁.keys k, or_false]

/-- The lower bound of child `j`. -/
abbrev lob (lo : Option (BitVec 32)) (ks : List (BitVec 32)) (j : Nat) : Option (BitVec 32) :=
  if j = 0 then lo else ks[j - 1]?

/-- The upper bound of child `j`. -/
abbrev hib (hi : Option (BitVec 32)) (ks : List (BitVec 32)) (j : Nat) : Option (BitVec 32) :=
  if j = ks.length then hi else ks[j]?

/-- A child of a subtree, with its bounds and one level lower. -/
theorem Sub.child {B : ByteArray} {t : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)}
    {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree} {j : Nat}
    (hS : Sub B t φ lo hi r (d + 1) (.node x false ks cs)) (hj : j < cs.length) :
    Sub B t φ (lob lo ks j) (hib hi ks j) false d cs[j] := by
  have hm : cs[j] ∈ cs := List.getElem_mem hj
  have hb : Balanced t false d cs[j] := by
    cases hS.hb with
    | inner _ hc => exact hc _ hm
  exact ⟨hS.ht, hS.ht', hS.h0, hS.hsz, hS.hfree,
    fun q hq => ⟨(hS.hfok q hq).1, fun h => (hS.hfok q hq).2 (.child hm h)⟩, hS.hR.child hm,
    hS.ho.child hj, hb, hS.hd.child hm, fun p hp => hS.hpg p (.child hm hp)⟩

/-- Pages of the node outside child `j` are not pages of the child, nor free, nor `0`. -/
theorem Sub.not_owned_sibling {B : ByteArray} {t : Nat} {φ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {j p : Nat} (hS : Sub B t φ lo hi r d (.node x false ks cs)) (hj : j < cs.length)
    (hp : Owns p (.node x false ks cs)) (hn : ¬ Owns p cs[j]) : ¬ Owned cs[j] φ p := by
  rintro (h | h | ⟨q, hq, rfl⟩)
  · exact absurd (h ▸ (hS.hpg p hp).1) (by decide)
  · exact hn h
  · exact (hS.hfok q hq).2 hp

/-- The siblings of child `j` own no page of it. -/
theorem Sub.sibling_disjoint {B : ByteArray} {t : Nat} {φ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {i j p : Nat} (hS : Sub B t φ lo hi r d (.node x false ks cs)) (hi : i < cs.length)
    (hj : j < cs.length) (hij : i ≠ j) (hp : Owns p cs[i]) : ¬ Owned cs[j] φ p :=
  hS.not_owned_sibling hj (.child (List.getElem_mem hi) hp) (hS.hd.disjoint hi hj hij hp)

/-- The children of the node after replacing child `j` are in memory. -/
theorem Sub.replace_children {B₁ B₂ : ByteArray} {t : Nat} {φ₁ φ₂ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {j : Nat} {c' : Tree} {Q : BitVec 32 → Prop}
    (hS : Sub B₁ t φ₁ lo hi r d (.node x false ks cs)) (hj : j < cs.length) (hR' : Repr B₂ c')
    (hU : Upd B₁ B₂ φ₁ φ₂ cs[j] c' Q) : ∀ c ∈ cs.set j c', Repr B₂ c := by
  intro c hc
  rcases mem_set_ne hc with rfl | ⟨i, hi, hij, rfl⟩
  · exact hR'
  · exact (hS.hR.child (List.getElem_mem hi)).frame hU.frame fun p hp =>
      ⟨hS.sibling_disjoint hi hj hij hp, hS.hpg p (.child (List.getElem_mem hi) hp)⟩

/-- The pointers of the node are unchanged by replacing a child with one on the same page. -/
theorem ptrs_set {cs : List Tree} {j : Nat} {c' : Tree} (hj : j < cs.length)
    (hp : c'.page = cs[j].page) : (cs.set j c').map Tree.ptr = cs.map Tree.ptr := by
  rw [List.map_set]
  have e : c'.ptr = (cs.map Tree.ptr)[j]'(by simpa using hj) := by
    simp only [List.getElem_map, Tree.ptr, hp]
  rw [e, List.set_getElem_self]

/-- The node after replacing child `j` is in memory. -/
theorem Sub.replace_repr {B₁ B₂ : ByteArray} {t : Nat} {φ₁ φ₂ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {j : Nat} {c' : Tree} {Q : BitVec 32 → Prop}
    (hS : Sub B₁ t φ₁ lo hi r d (.node x false ks cs)) (hj : j < cs.length) (hR' : Repr B₂ c')
    (hU : Upd B₁ B₂ φ₁ φ₂ cs[j] c' Q) : Repr B₂ (.node x false ks (cs.set j c')) := by
  have hm : cs[j] ∈ cs := List.getElem_mem hj
  have hx : ¬ Owned cs[j] φ₁ x := hS.not_owned_sibling hj .here (hS.hd.root_not_child hm)
  have hn := node_frame hU.frame hx (hS.hpg x .here)
  have hl := hS.hR.leaf_iff
  refine .inner ?_ (hn.2.1 _ hl.2.2.1) ?_ (hS.replace_children hj hR' hU)
  · rw [hn.1]
    by_contra hc
    exact Bool.noConfusion (hl.1.2 hc)
  · rw [ptrs_set hj hU.same_page]
    exact hn.2.2 _ (hl.2.2.2 rfl)

/-- A page of a new child is a page of the old child, or not a page of the node. -/
theorem Sub.new_pages {B₁ B₂ : ByteArray} {t : Nat} {φ₁ φ₂ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {j : Nat} {c' : Tree} {Q : BitVec 32 → Prop}
    (hS : Sub B₁ t φ₁ lo hi r d (.node x false ks cs)) (hj : j < cs.length)
    (hU : Upd B₁ B₂ φ₁ φ₂ cs[j] c' Q) (p : Nat) (hp : Owns p c') : Owns p cs[j] ∨ ¬ Owns p (.node x false ks cs) := by
  rcases hU.owns p hp with h | ⟨q, hq, rfl⟩ | h
  · exact .inl h
  · exact .inr (hS.hfok q hq).2
  · refine .inr fun h' => ?_
    have := (hS.hpg p h').2.2
    simp only [page] at *
    omega

/-- **Replacing child `j` by an update of it** gives a subtree and an update of the node. -/
theorem Sub.replace {B₁ B₂ : ByteArray} {t : Nat} {φ₁ φ₂ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    {j : Nat} {c' : Tree} {Q : BitVec 32 → Prop}
    (hS : Sub B₁ t φ₁ lo hi r (d + 1) (.node x false ks cs)) (hj : j < cs.length)
    (hS' : Sub B₂ t φ₂ (lob lo ks j) (hib hi ks j) false d c')
    (hU : Upd B₁ B₂ φ₁ φ₂ cs[j] c' Q) :
    Sub B₂ t φ₂ lo hi r (d + 1) (.node x false ks (cs.set j c')) ∧
      Upd B₁ B₂ φ₁ φ₂ (.node x false ks cs) (.node x false ks (cs.set j c')) Q := by
  have hm : cs[j] ∈ cs := List.getElem_mem hj
  have hold : ∀ p, Owns p (.node x false ks (cs.set j c')) →
      Owns p (.node x false ks cs) ∨ Owns p c' := fun p hp => owns_set_old hj hp
  refine ⟨⟨hS'.ht, hS'.ht', hS'.h0, hS'.hsz, hS'.hfree, fun q hq => ⟨(hS'.hfok q hq).1, ?_⟩,
    hS.replace_repr hj hS'.hR hU, ordered_set hS.ho hS'.ho, balanced_set hS.hb hS'.hb,
    distinct_set hj hS.hd hS'.hd (hS.new_pages hj hU), fun p hp => ?_⟩,
    ⟨rfl, hU.sub, hU.w4, hU.size, fun p hp => ?_, hU.frame.mono fun p hp => ?_,
      fun k => inTree_set hj hU.keys⟩⟩
  · intro h
    rcases hold _ h with h' | h'
    · exact (hS.hfok q (hU.sub.subset hq)).2 h'
    · exact (hS'.hfok q hq).2 h'
  · rcases hold p hp with h' | h'
    · exact (hS.hpg p h').mono hU.size
    · exact hS'.hpg p h'
  · rcases hold p hp with h' | h'
    · exact .inl h'
    · rcases hU.owns p h' with h'' | h'' | h''
      · exact .inl (.child hm h'')
      · exact .inr (.inl h'')
      · exact .inr (.inr h'')
  · rcases hp with h | h | h
    · exact .inl h
    · exact .inr (.inl (.child hm h))
    · exact .inr (.inr h)

/-! ## The specification of `insert_nonfull` -/

/-- The precondition of `insert_nonfull(x, k)` on the memory: the subtree `X` at `x` with its
context, not full, and `k` within its bounds and not among its keys. -/
def NFPre (B : ByteArray) (t : Nat) (φ : List (BitVec 32)) (lo hi : Option (BitVec 32))
    (r : Bool) (d : Nat) (X : Tree) (k : BitVec 32) : Prop :=
  Sub B t φ lo hi r d X ∧ X.keys.length < 2 * t - 1 ∧ Within lo hi k ∧ ¬ InTree k X

open Silmaril.Wasm Silmaril.Wasm.Execution.Core in
/-- **`insert_nonfull(x, k)`**, for subtrees within the bounds `(lo, hi)`, of root flag `r`
and height `d`: returns `1` with `k` added, or `0` (a page allocation failed) with the same
keys; either way an update of the subtree (`Upd`) that is again a subtree (`Sub`). -/
def insNFSpec {H : Type} (a : Nat) (fi : FuncInst H) (lo hi : Option (BitVec 32)) (r : Bool)
    (d : Nat) : Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Resolved s fi.module ∧ ∃ (xv k : BitVec 32) (ma : Nat)
    (mt : MemoryType) (B : ByteArray) (t : Nat) (φ : List (BitVec 32)) (X : Tree),
    args = [.i32 xv, .i32 k] ∧ MemAt s fi.module ma mt B ∧ mt.address = .i32 ∧
    X.page = xv.toNat ∧ NFPre B t φ lo hi r d X k
  post s args s' o := ∀ (xv k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray) (t : Nat)
    (φ : List (BitVec 32)) (X : Tree), args = [.i32 xv, .i32 k] → MemAt s fi.module ma mt B →
    mt.address = .i32 → X.page = xv.toNat → NFPre B t φ lo hi r d X k →
    ∃ (b : BitVec 32) (mt' : MemoryType) (B' : ByteArray) (φ' : List (BitVec 32)) (X' : Tree),
      o = .normal [.i32 b] ∧ s' = s.setMem ma ⟨mt', B'⟩ ∧ mt'.address = .i32 ∧
      Sub B' t φ' lo hi r d X' ∧
      ((b = 1 ∧ Upd B B' φ φ' X X' (· = k)) ∨ (b = 0 ∧ Upd B B' φ φ' X X' fun _ => False))

end Silmaril.WasmSpec.BTree.V2
