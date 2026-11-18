module

public import Silmaril.Proofs.WasmSpec.BTree.V2.SplitChild
public import Silmaril.Proofs.WasmSpec.BTree.V2.Alloc
public import Silmaril.Proofs.WasmSpec.BTree.V2.InsPure
public import Silmaril.Proofs.WasmSpec.BTree.V2.Search
public import Silmaril.Proofs.WasmSpec.BTree.V2.Create

/-!
# The B-tree library, version 2: `btree_insert` by tactics

`btree_insert(k)` calls `btree_search` (returning `1` when `k` is a key), then grows a full
root (two calls of `alloc_node`, a new inner root page holding the old root as its only
child, `split_child`, and the new root pointer), then calls `insert_nonfull` on the root.
Each memory step is a `Step` of the tree (pages from the free list or beyond the old memory,
bytes outside page `0`, the tree's pages and the free pages unchanged); the result is a
B-tree of the old keys, plus `k` when `insert_nonfull` returns `1`. The proof assumes
`insert_nonfull`'s specification (`insNFSpec`), proved separately. Every-run total
correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Steps of the whole tree -/

/-- **A step of the tree** `T` (in `B`, free pages `φ`) to `X` (in `B'`, free pages `φ'`):
the free list shrinks, the memory grows, new pages come from the free list or beyond the old
memory, no byte outside page `0`, `T`'s pages and the free pages changes, and the keys `Q`
are added. Unlike `Upd`, the root page may change. -/
structure Step (B B' : ByteArray) (φ φ' : List (BitVec 32)) (T X : Tree)
    (Q : BitVec 32 → Prop) : Prop where
  sub : φ'.Sublist φ
  size : B.size ≤ B'.size
  owns : ∀ p, Owns p X → Owns p T ∨ (∃ q ∈ φ, q.toNat = p) ∨ B.size ≤ page * p
  frame : Unchanged B B' (Owned T φ)
  keys : ∀ k, InTree k X ↔ InTree k T ∨ Q k

/-- An update of the root subtree is a step. -/
theorem Step.ofUpd {B B' : ByteArray} {φ φ' : List (BitVec 32)} {T X : Tree}
    {Q : BitVec 32 → Prop} (h : Upd B B' φ φ' T X Q) : Step B B' φ φ' T X Q :=
  ⟨h.sub, h.size, h.owns, h.frame, h.keys⟩

/-- The pages a later step may change, seen from an earlier one. -/
theorem Step.owned {B B₁ : ByteArray} {φ φ₁ : List (BitVec 32)} {T X₁ : Tree}
    {Q : BitVec 32 → Prop} (h : Step B B₁ φ φ₁ T X₁ Q) {i : Nat} (hi : i < B.size)
    (hs : ¬ Owned T φ (i / page)) : ¬ Owned X₁ φ₁ (i / page) := by
  rintro (h' | h' | ⟨q, hq, he⟩)
  · exact hs (.inl h')
  · rcases h.owns _ h' with h'' | h'' | h''
    · exact hs (.inr (.inl h''))
    · exact hs (.inr (.inr h''))
    · exact not_fresh hi h''
  · exact hs (.inr (.inr ⟨q, h.sub.subset hq, he⟩))

/-- **Steps compose**, the first keeping the keys. -/
theorem Step.trans {B B₁ B₂ : ByteArray} {φ φ₁ φ₂ : List (BitVec 32)} {T X₁ X₂ : Tree}
    {Q : BitVec 32 → Prop} (h₁ : Step B B₁ φ φ₁ T X₁ fun _ => False)
    (h₂ : Step B₁ B₂ φ₁ φ₂ X₁ X₂ Q) : Step B B₂ φ φ₂ T X₂ Q := by
  refine ⟨h₂.sub.trans h₁.sub, h₁.size.trans h₂.size, fun p hp => ?_,
    ⟨h₁.size.trans h₂.size, fun i hi hs =>
      (h₂.frame.2 i (lt_of_lt_of_le hi h₁.size) (h₁.owned hi hs)).trans (h₁.frame.2 i hi hs)⟩,
    fun k => by rw [h₂.keys k, h₁.keys k, or_false]⟩
  rcases h₂.owns p hp with h | ⟨q, hq, he⟩ | h
  · rcases h₁.owns p h with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr h')
  · exact .inr (.inl ⟨q, h₁.sub.subset hq, he⟩)
  · exact .inr (.inr (le_trans h₁.size h))

/-- A balanced tree with at least `t - 1` keys is balanced below a root. -/
theorem Balanced.unroot {t d : Nat} {r : Bool} {T : Tree} (h : Balanced t r d T)
    (hk : t - 1 ≤ T.keys.length) : Balanced t false d T := by
  cases h with
  | leaf hk' => exact .leaf ⟨.inr hk, hk'.2⟩
  | inner hk' hc => exact .inner ⟨.inr hk, hk'.2⟩ hc

/-- The root pointer of a tree of valid pages, as a number. -/
theorem BTreeAt.root {B : ByteArray} {t : Nat} {T : Tree} {φ : List (BitVec 32)}
    (h : BTreeAt B t T φ) : (wd B 4).toNat = T.page := by
  rw [h.2.2.2.2.1]
  exact ptr_toNat (h.2.2.2.2.2.2.2.2.2.1 _ (Owns.root T))

/-- **A B-tree is determined by the memory**: its branching factor, tree and free pages. -/
theorem BTreeAt.unique {B : ByteArray} {t t' : Nat} {T T' : Tree} {φ φ' : List (BitVec 32)}
    (h : BTreeAt B t T φ) (h' : BTreeAt B t' T' φ') : t' = t ∧ T' = T ∧ φ' = φ := by
  have hpg := h.2.2.2.2.2.2.2.2.2.1
  have hpg' := h'.2.2.2.2.2.2.2.2.2.1
  have ht : t' = t := by
    have e := congrArg BitVec.toNat (h'.2.2.2.1.symm.trans h.2.2.2.1)
    rwa [toNat_ofNat_lt (by have := h'.2.1; omega), toNat_ofNat_lt (by have := h.2.1; omega)] at e
  have hT : T' = T := Repr.unique h'.2.2.2.2.2.1 h.2.2.2.2.2.1 (h'.root.symm.trans h.root)
    (fun p hp => by have := (hpg' p hp).2.1; omega) (fun p hp => by have := (hpg p hp).2.1; omega)
  exact ⟨ht, hT, h.2.2.2.2.2.2.2.2.2.2.1.1.1.unique h'.2.2.2.2.2.2.2.2.2.2.1.1.1⟩

/-- A B-tree is a root subtree with its allocator context. -/
theorem BTreeAt.sub {B : ByteArray} {t : Nat} {T : Tree} {φ : List (BitVec 32)}
    (h : BTreeAt B t T φ) : ∃ d, Sub B t φ none none true d T := by
  obtain ⟨ht, ht', hsz, h0, -, hR, ho, ⟨d, hb⟩, hd, hpg, hf, hfok⟩ := h
  exact ⟨d, ht, ht', h0, hsz, hf, hfok, hR, ho, hb, hd, hpg⟩

/-- A root subtree whose page is at `4` is a B-tree. -/
theorem Sub.btreeAt {B : ByteArray} {t d : Nat} {T : Tree} {φ : List (BitVec 32)}
    (h : Sub B t φ none none true d T) (h4 : wd B 4 = T.ptr) : BTreeAt B t T φ :=
  ⟨h.ht, h.ht', h.hsz, h.h0, h4, h.hR, h.ho, ⟨d, h.hb⟩, h.hd, h.hpg, h.hfree, h.hfok⟩

/-- **The end of `btree_insert`**: a step to a root subtree at `4` is a B-tree with the keys
added, and the memory frame of the specification. -/
theorem step_isBTree {B B' : ByteArray} {t d : Nat} {φ φ' : List (BitVec 32)} {T X : Tree}
    {Q : BitVec 32 → Prop} (h : Step B B' φ φ' T X Q) (hS : Sub B' t φ' none none true d X)
    (h4 : wd B' 4 = X.ptr) :
    IsBTree B' t (fun k' => InTree k' T ∨ Q k') ∧ Unchanged B B' (Owned T φ) :=
  ⟨⟨X, φ', hS.btreeAt h4, h.keys⟩, h.frame⟩

/-! ## Allocations -/

/-- A page of a B-tree is not page `0`. -/
theorem owns_ne_zero {B : ByteArray} {t : Nat} {T : Tree} {φ : List (BitVec 32)}
    (h : BTreeAt B t T φ) {p : Nat} (hp : Owns p T) : ¬ p = 0 := fun e =>
  absurd (e ▸ (h.2.2.2.2.2.2.2.2.2.1 p hp).1) (by decide)

/-- After an allocation, only page `0` of the old memory may have changed. -/
theorem AllocPost.unchanged_i {B B' : ByteArray} {φ φ' : List (BitVec 32)} {r : BitVec 32}
    (hA : AllocPost B φ r B' φ') : Unchanged B B' (· = 0) :=
  ⟨hA.2.1, fun i hi hs => hA.2.2.2.2.1 i hi (.inr (by simp only [page] at hs; omega))⟩

/-- After an allocation, the words at `0` and `4` are unchanged. -/
theorem AllocPost.wd_low_i {B B' : ByteArray} {φ φ' : List (BitVec 32)} {r : BitVec 32}
    (hA : AllocPost B φ r B' φ') (h8 : 8 ≤ B.size) {a : Nat} (ha : a + 4 ≤ 8) :
    wd B' a = wd B a :=
  wd_of_bytes (by omega) (by have := hA.2.1; omega) fun i _ h2 =>
    hA.2.2.2.2.1 i (by omega) (.inl (by omega))

/-- **An allocation keeps the B-tree** (with the new free list) and is a step. -/
theorem alloc_keeps {B B' : ByteArray} {t : Nat} {T : Tree} {φ φ' : List (BitVec 32)}
    {r : BitVec 32} (h : BTreeAt B t T φ) (hA : AllocPost B φ r B' φ') :
    BTreeAt B' t T φ' ∧ Step B B' φ φ' T T (fun _ => False) := by
  obtain ⟨ht, ht', hsz, h0, h4, hR, ho, hb, hd, hpg, hf, hfok⟩ := h
  have h8 : 8 ≤ B.size := by have := hf.1.1.2.2.2.2; omega
  have hU : Unchanged B B' (· = 0) := hA.unchanged_i
  have hR' : Repr B' T := hR.frame hU fun p hp =>
    ⟨owns_ne_zero ⟨ht, ht', hsz, h0, h4, hR, ho, hb, hd, hpg, hf, hfok⟩ hp, hpg p hp⟩
  refine ⟨⟨ht, ht', hA.1, (hA.wd_low_i h8 (by omega)).trans h0, (hA.wd_low_i h8 (le_refl _)).trans h4,
    hR', ho, hb, hd, fun p hp => (hpg p hp).mono hA.2.1, hA.2.2.1,
    fun q hq => ⟨hA.2.2.2.2.2.1 q hq, (hfok q (hA.2.2.2.1.subset hq)).2⟩⟩,
    ⟨hA.2.2.2.1, hA.2.1, fun p hp => .inl hp, hU.mono fun p hp => .inl hp,
      fun k => by rw [or_false]⟩⟩

/-- **A page from an allocation** that did not fail is valid, not free any more, not a page
of the tree, and was free or beyond the old memory. -/
theorem alloc_fresh_i {B B' : ByteArray} {t : Nat} {T : Tree} {φ φ' : List (BitVec 32)}
    {r : BitVec 32} (h : BTreeAt B t T φ) (hA : AllocPost B φ r B' φ') (hr : r ≠ -1) :
    PageOK B' r.toNat ∧ r ∉ φ' ∧ ¬ Owns r.toNat T ∧
      ((∃ q ∈ φ, q.toNat = r.toNat) ∨ B.size ≤ page * r.toNat) := by
  rcases hA.2.2.2.2.2.2 with e | ⟨hok, hn, hw⟩
  · exact absurd e hr
  · refine ⟨hok, hn, fun ho => ?_, hw.imp (fun hq => ⟨r, hq, rfl⟩) id⟩
    rcases hw with hq | hfr
    · exact (h.2.2.2.2.2.2.2.2.2.2.2 r hq).2 ho
    · have := (h.2.2.2.2.2.2.2.2.2.1 _ ho).2.2
      simp only [page] at *
      omega

/-! ## The callees -/

/-- The callees of `btree_insert`: `btree_search` (index 2), `alloc_node` (5), `split_child`
(6) and `insert_nonfull` (7), with their specifications. -/
structure ICtx (P : Profile) (host : HostSemantics H) (s : Store H) (mi : ModuleInst) : Type where
  res : Resolved s mi
  aS : Nat
  fiS : FuncInst H
  hS : mi.funcs[2]? = some aS
  hfS : s.funcs[aS]? = some fiS
  hSS : TFSpecAt P host aS (searchSpec aS fiS)
  hmS : fiS.module = mi
  aA : Nat
  fiA : FuncInst H
  hA : mi.funcs[5]? = some aA
  hfA : s.funcs[aA]? = some fiA
  hAS : TFSpecAt P host aA (allocSpecI32 aA fiA)
  hmA : fiA.module = mi
  aX : Nat
  fiX : FuncInst H
  hX : mi.funcs[6]? = some aX
  hfX : s.funcs[aX]? = some fiX
  hXS : TFSpecAt P host aX (splitSpec aX fiX)
  hmX : fiX.module = mi
  aN : Nat
  fiN : FuncInst H
  hN : mi.funcs[7]? = some aN
  hfN : s.funcs[aN]? = some fiN
  hNS : ∀ lo hi r d, TFSpecAt P host aN (insNFSpec aN fiN lo hi r d)
  hmN : fiN.module = mi

/-- The callees of `btree_insert`, from `Resolved` and `insert_nonfull`'s specification. -/
noncomputable def ICtx.ofResolved {s : Store H} {mi : ModuleInst} (hres : Resolved s mi)
    (hNF : ∀ (a' : Nat) (fi' : FuncInst H), fi'.code = .wasm insertNonfullFunc →
      HasArity fi' 2 1 → ∀ lo hi r d, TFSpecAt P host a' (insNFSpec a' fi' lo hi r d)) :
    ICtx P host s mi :=
  let e := Classical.choose_spec (Classical.choose_spec (hres.get (j := 2) (by decide)))
  let a := Classical.choose_spec (Classical.choose_spec (hres.get (j := 5) (by decide)))
  let x := Classical.choose_spec (Classical.choose_spec (hres.get (j := 6) (by decide)))
  let n := Classical.choose_spec (Classical.choose_spec (hres.get (j := 7) (by decide)))
  ⟨hres, _, _, e.1, e.2.1, search_valid e.2.2.2.1 e.2.2.2.2, e.2.2.1, _, _, a.1, a.2.1,
    alloc_valid a.2.2.2.1 a.2.2.2.2, a.2.2.1, _, _, x.1, x.2.1, split_valid x.2.2.2.1 x.2.2.2.2,
    x.2.2.1, _, _, n.1, n.2.1, hNF _ _ n.2.2.2.1 n.2.2.2.2, n.2.2.1⟩

/-! ## The call of `insert_nonfull` -/

/-- What the body's postcondition must accept: the result `b` with a memory holding a B-tree of
the old keys, plus `k` when `b = 1`, and the memory frame. -/
def InsQ (s : Store H) (ma : Nat) (B : ByteArray) (t : Nat) (T : Tree) (φ : List (BitVec 32))
    (k : BitVec 32) (Q : Post H) : Prop :=
  ∀ (b : BitVec 32) (mt' : MemoryType) (B' : ByteArray), mt'.address = .i32 →
    Unchanged B B' (Owned T φ) →
    ((b = 1 ∧ IsBTree B' t fun k' => InTree k' T ∨ k' = k) ∨
      (b = 0 ∧ IsBTree B' t fun k' => InTree k' T)) →
    (∀ F, Q (s.setMem ma ⟨mt', B'⟩) F (.normal [.i32 b])) ∧
      ∀ F, Q (s.setMem ma ⟨mt', B'⟩) F (.ret [.i32 b])

/-- After `insert_nonfull` on the root: a B-tree with the keys. -/
theorem nf_result {B B₁ B' : ByteArray} {t d : Nat} {φ φ₁ φ' : List (BitVec 32)} {T X X' : Tree}
    {Q : BitVec 32 → Prop} (hstep : Step B B₁ φ φ₁ T X fun _ => False)
    (h4 : wd B₁ 4 = X.ptr) (hS : Sub B' t φ' none none true d X') (hU : Upd B₁ B' φ₁ φ' X X' Q) :
    IsBTree B' t (fun k' => InTree k' T ∨ Q k') ∧ Unchanged B B' (Owned T φ) := by
  have hp : X'.ptr = X.ptr := by rw [Tree.ptr, Tree.ptr, hU.same_page]
  exact step_isBTree (hstep.trans (Step.ofUpd hU)) hS (by rw [hU.w4, h4, hp])

/-- **The final call** `insert_nonfull(r, k)` on the root subtree `X`, a step of `T`. -/
theorem ins_final {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt mt₁ : MemoryType}
    {B B₁ : ByteArray} {t d : Nat} {φ φ₁ : List (BitVec 32)} {T X : Tree}
    (c : ICtx P host s₀ mi) (hm : MemAt s₀ mi ma mt B) (h32 : mt₁.address = .i32)
    {k rv sv zv : BitVec 32} (hx : X.page = rv.toNat) (hpre : NFPre B₁ t φ₁ none none true d X k)
    (h4 : wd B₁ 4 = X.ptr) (hstep : Step B B₁ φ φ₁ T X fun _ => False) {Q : Post H}
    (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host (s₀.setMem ma ⟨mt₁, B₁⟩) (fr mi [k, rv, sv, zv])
      (vals ([] : List Val).reverse ++ expression [lget 1, lget 0, call 7]) Q := by
  have hmN : MemAt (s₀.setMem ma ⟨mt₁, B₁⟩) c.fiN.module ma mt₁ B₁ := by
    rw [c.hmN]; exact MemAt.setMemT hm mt₁ B₁
  have hres : Resolved (s₀.setMem ma ⟨mt₁, B₁⟩) c.fiN.module := by
    rw [c.hmN]; exact c.res.setMem _ _
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 rv, .i32 k]) (by simpa [Idx.toNat] using c.hN) c.hfN
    (c.hNS none none true d) ⟨c.hfN, hres, rv, k, ma, mt₁, B₁, t, φ₁, X, rfl, hmN, h32, hx, hpre⟩
    fun s' o hp => ?_
  obtain ⟨b, mt', B', φ', X', ho, hs, h32', hS, hb⟩ := hp rv k ma mt₁ B₁ t φ₁ X rfl hmN h32 hx hpre
  refine ⟨b, ho, ?_⟩
  rw [hs, setMem_setMem]
  refine w_end (m := .total) (rs := [Val.i32 b]) ?_
  rcases hb with ⟨rfl, hU⟩ | ⟨rfl, hU⟩
  · obtain ⟨hB, hF⟩ := nf_result hstep h4 hS hU
    exact (hQ 1 mt' B' h32' hF (.inl ⟨rfl, hB⟩)).1 _
  · obtain ⟨hB, hF⟩ := nf_result hstep h4 hS hU
    exact (hQ 0 mt' B' h32' hF (.inr ⟨rfl, by simpa using hB⟩)).1 _

/-! ## The code -/

/-- The stores building the new root and the split (after the two allocations). -/
abbrev rootArm : List Instr := [lget 2, c32 65536, imul, c32 0, istore,
  lget 2, c32 65536, imul, c32 0, .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
  lget 2, c32 65536, imul, c32 1, .intStore .i32 none ⟨0⟩ ⟨2, 32768⟩,
  lget 2, c32 65536, imul, lget 1, .intStore .i32 none ⟨0⟩ ⟨2, 32772⟩,
  lget 2, c32 0, lget 3, call 6,
  c32 4, lget 2, istore,
  lget 2, lset 1]

/-- The arm growing a full root. -/
abbrev fullArm : List Instr := [call 5, lset 2, lget 2, c32 4294967295, .intRelOp .i32 .eq,
  .if_ .empty [c32 0, .return_] [],
  call 5, lset 3, lget 3, c32 4294967295, .intRelOp .i32 .eq, .if_ .empty [c32 0, .return_] []] ++
  rootArm

/-- After the search: load the root, test whether it is full. -/
abbrev insPart2 : List Instr := [c32 4, iload, lset 1,
  lget 1, c32 65536, imul, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, c32 0, iload, c32 2, imul, c32 1, isub,
  .intRelOp .i32 .eq, .if_ .empty fullArm [], lget 1, lget 0, call 7]

theorem insertFunc_body : insertFunc.body =
    [lget 0, call 2, .if_ .empty [c32 1, .return_] []] ++ insPart2 := rfl

theorem forCall_insert (mi : ModuleInst) (k : BitVec 32) :
    Frame.forCall mi [.i32 k] insertFunc.locals = fr mi [k, 0, 0, 0] := rfl

/-! ## The new root -/

/-- The four stores building the new root page at `P`: inner, no keys, one child `v`. -/
abbrev rootMem (B : ByteArray) (P : Nat) (v : BitVec 32) : ByteArray :=
  wr (wr (wr (wr B P 0#32) (P + ((4 : Fin (2 ^ 64)) : Nat)) 0#32)
    (P + ((32768 : Fin (2 ^ 64)) : Nat)) 1#32) (P + ((32772 : Fin (2 ^ 64)) : Nat)) v

/-- The stores of the new root change only its page, and write its four words. -/
theorem rootMem_facts {B : ByteArray} {s : Nat} (v : BitVec 32) (hs : page * (s + 1) ≤ B.size) :
    Agree B (rootMem B (page * s) v) (fun j => page * s ≤ j ∧ j < page * s + page) ∧
      wd (rootMem B (page * s) v) (page * s) = 0#32 ∧
      wd (rootMem B (page * s) v) (page * s + 4) = 0#32 ∧
      wd (rootMem B (page * s) v) (page * s + 32768) = 1#32 ∧
      wd (rootMem B (page * s) v) (page * s + 32772) = v := by
  have e4 : ((4 : Fin (2 ^ 64)) : Nat) = 4 := rfl
  have e1 : ((32768 : Fin (2 ^ 64)) : Nat) = 32768 := rfl
  have e2 : ((32772 : Fin (2 ^ 64)) : Nat) = 32772 := rfl
  simp only [page] at hs ⊢
  simp only [rootMem, e4, e1, e2]
  have h1 : SameOutside B (wr B (65536 * s) 0#32) (65536 * s) 65536 :=
    sameOutside_wr _ (by omega) (le_refl _) (by omega)
  have h2 := sameOutside_wr (B := wr B (65536 * s) 0#32) (p := 65536 * s) (len := 65536)
    (a := 65536 * s + 4) 0#32 (by rw [h1.1]; omega) (by omega) (by omega)
  have h3 := sameOutside_wr (B := wr (wr B (65536 * s) 0#32) (65536 * s + 4) 0#32) (p := 65536 * s)
    (len := 65536) (a := 65536 * s + 32768) 1#32 (by rw [h2.1, h1.1]; omega) (by omega) (by omega)
  have h4 := sameOutside_wr (B := wr (wr (wr B (65536 * s) 0#32) (65536 * s + 4) 0#32)
    (65536 * s + 32768) 1#32) (p := 65536 * s) (len := 65536) (a := 65536 * s + 32772) v
    (by rw [h3.1, h2.1, h1.1]; omega) (by omega) (by omega)
  refine ⟨SameOutside.agree (h1.trans (h2.trans (h3.trans h4))), ?_, ?_, ?_, ?_⟩
  · rw [wd_wr_ne _ (by rw [h3.1, h2.1, h1.1]; omega) (by omega),
      wd_wr_ne _ (by rw [h2.1, h1.1]; omega) (by omega), wd_wr_ne _ (by rw [h1.1]; omega) (by omega),
      wd_wr_same _ (by omega)]
  · rw [wd_wr_ne _ (by rw [h3.1, h2.1, h1.1]; omega) (by omega),
      wd_wr_ne _ (by rw [h2.1, h1.1]; omega) (by omega), wd_wr_same _ (by rw [h1.1]; omega)]
  · rw [wd_wr_ne _ (by rw [h3.1, h2.1, h1.1]; omega) (by omega),
      wd_wr_same _ (by rw [h2.1, h1.1]; omega)]
  · rw [wd_wr_same _ (by rw [h3.1, h2.1, h1.1]; omega)]


/-- The stores of the new root change only page `s`. -/
theorem rootMem_unchanged {B : ByteArray} {s : Nat} (v : BitVec 32) (hs : page * (s + 1) ≤ B.size) :
    Unchanged B (rootMem B (page * s) v) (· = s) ∧ (rootMem B (page * s) v).size = B.size :=
  ⟨(rootMem_facts v hs).1.unchanged fun _ hj => div_page hj.1 hj.2, (rootMem_facts v hs).1.1⟩

/-- **The new root in memory**: an inner node at page `s` with no keys and the old root `T` as
its only child. -/
theorem newroot_repr {B : ByteArray} {t s : Nat} {T : Tree} {φ : List (BitVec 32)}
    (hbt : BTreeAt B t T φ) (hs : PageOK B s) (hsT : ¬ Owns s T) :
    Repr (rootMem B (page * s) T.ptr) (.node s false [] [T]) := by
  obtain ⟨-, w0, w4, w1, w2⟩ := rootMem_facts T.ptr hs.2.2
  obtain ⟨hU, hsz⟩ := rootMem_unchanged T.ptr hs.2.2
  have hb := hs.2.2
  have h32 := hs.2.1
  have hpg := hbt.2.2.2.2.2.2.2.2.2.1
  have hT : Repr (rootMem B (page * s) T.ptr) T := hbt.2.2.2.2.2.1.frame hU fun p hp =>
    ⟨fun e => hsT (e ▸ hp), hpg p hp⟩
  have hw : words (rootMem B (page * s) T.ptr) (page * s + 32768 + 4) 1 = [T.ptr] := by
    simp only [words, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero]
    rw [show page * s + 32768 + 4 = page * s + 32772 by omega, w2]
  have hP : BA (rootMem B (page * s) T.ptr) (page * s + 32768) 8091 ([T].map Tree.ptr) :=
    ⟨by rw [w1]; rfl, by simpa using hw, by simp, by simp only [page, int32Max] at *; omega,
      by rw [hsz]; simp only [page] at *; omega⟩
  refine .inner w0 (OBAnd.empty w4 (by rw [hsz]; simp only [page] at *; omega)
    (by simp only [page, int32Max] at *; omega)) hP fun c hc => ?_
  rw [List.mem_singleton.1 hc]
  exact hT


/-- A full inner root has `2 t` children. -/
theorem full_children {lo hi : Option (BitVec 32)} {t : Nat} {T : Tree} (ho : Ordered lo hi T)
    (hfull : T.keys.length = 2 * t - 1) (ht : 2 ≤ t) : T.leaf = false → T.children.length = 2 * t := by
  intro hl
  obtain ⟨x, l, ks, cs⟩ := T
  have hl' : l = false := hl
  subst hl'
  have hk : ks.length = 2 * t - 1 := hfull
  cases ho with
  | mk _ _ hlen _ =>
    show cs.length = 2 * t
    simp only [Bool.false_eq_true, ↓reduceIte] at hlen
    omega

/-- The new root is ordered without bounds. -/
theorem newroot_ordered {s : Nat} {T : Tree} (ho : Ordered none none T) :
    Ordered none none (.node s false [] [T]) := by
  refine .mk List.Pairwise.nil (fun _ h => absurd h List.not_mem_nil) (by simp) fun i hi => ?_
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  simpa using ho

/-- The new root has distinct pages. -/
theorem newroot_distinct {s : Nat} {T : Tree} (hd : Distinct T) (hsT : ¬ Owns s T) :
    Distinct (.node s false [] [T]) :=
  .node (fun c hc => by rw [List.mem_singleton.1 hc]; exact hsT) (List.pairwise_singleton _ _)
    fun c hc => by rw [List.mem_singleton.1 hc]; exact hd

/-- The pages of the new root: `s` and the old root's. -/
theorem newroot_owns {s p : Nat} {T : Tree} (h : Owns p (.node s false [] [T])) :
    p = s ∨ Owns p T := by
  rcases owns_node_iff.1 h with h | ⟨c, hc, hp⟩
  · exact .inl h
  · exact .inr (List.mem_singleton.1 hc ▸ hp)

/-- **The precondition of the root split.** -/
theorem newroot_splitPre {B : ByteArray} {t s z : Nat} {T : Tree} {φ : List (BitVec 32)}
    (hbt : BTreeAt B t T φ) (hs : PageOK B s) (hsT : ¬ Owns s T) (hz : PageOK B z)
    (hzT : ¬ Owns z T) (hsz : s ≠ z) (hfull : T.keys.length = 2 * t - 1) :
    SplitPre (rootMem B (page * s) T.ptr) t (.node s false [] [T]) 0 z := by
  have hrep := newroot_repr hbt hs hsT
  obtain ⟨ht, ht', -, h0, -, hR, ho, -, hd, hpg, -, -⟩ := hbt
  obtain ⟨A, -⟩ := rootMem_facts T.ptr hs.2.2
  have hsize : (rootMem B (page * s) T.ptr).size = B.size := A.1
  have hw0 : wd (rootMem B (page * s) T.ptr) 0 = wd B 0 := A.wd_eq fun j h1 h2 hr => by
    have := hs.1; simp only [page] at *; omega
  refine ⟨ht, ht', hw0.trans h0, rfl, hrep, newroot_distinct hd hsT,
    ⟨none, none, newroot_ordered ho⟩, fun p hp => ?_, hz.mono hsize.ge, fun h => ?_,
    by show 0 < 2 * t - 1; omega, rfl, T, rfl, hfull, full_children ho hfull ht⟩
  · rcases newroot_owns hp with rfl | hp
    · exact hs.mono hsize.ge
    · exact (hpg p hp).mono hsize.ge
  · rcases newroot_owns h with e | h
    · exact hsz e.symm
    · exact hzT h


/-- The keys of the new root: those of the old root. -/
theorem newroot_inTree {s : Nat} {T : Tree} {k : BitVec 32} :
    InTree k (.node s false [] [T]) ↔ InTree k T := by
  rw [inTree_node_iff]
  simp

/-- **The split new root**: on page `s`, ordered, balanced one level higher, distinct, its pages
`s`, `z` and the old root's, its keys the old root's, one key. -/
theorem newroot_x1 {t s z d : Nat} {T : Tree} (ht : 2 ≤ t) (hfull : T.keys.length = 2 * t - 1)
    (ho : Ordered none none T) (hb : Balanced t true d T) (hd : Distinct T) (hsT : ¬ Owns s T)
    (hzT : ¬ Owns z T) (hsz : s ≠ z) :
    ((Tree.node s false [] [T]).splitChild t z 0).page = s ∧
      Ordered none none ((Tree.node s false [] [T]).splitChild t z 0) ∧
      Balanced t true (d + 1) ((Tree.node s false [] [T]).splitChild t z 0) ∧
      Distinct ((Tree.node s false [] [T]).splitChild t z 0) ∧
      (∀ p, Owns p ((Tree.node s false [] [T]).splitChild t z 0) → p = s ∨ Owns p T ∨ p = z) ∧
      (∀ k, InTree k ((Tree.node s false [] [T]).splitChild t z 0) ↔ InTree k T) ∧
      ((Tree.node s false [] [T]).splitChild t z 0).keys.length = 1 := by
  obtain ⟨y, ly, ky, cy⟩ := T
  have hi : 0 < [Tree.node y ly ky cy].length := by simp
  have hy : [Tree.node y ly ky cy][0] = .node y ly ky cy := rfl
  have hk : ky.length = 2 * t - 1 := hfull
  have hbn : Balanced t true (d + 1) (.node s false [] [.node y ly ky cy]) :=
    .inner ⟨.inl rfl, Nat.zero_le _⟩ fun c hc => by
      rw [List.mem_singleton.1 hc]; exact hb.unroot (by show t - 1 ≤ ky.length; omega)
  refine ⟨splitChild_page, splitChild_ordered (by omega) hi hy hk (newroot_ordered ho),
    splitChild_balanced ht hi rfl hy hk (by simp; omega) hbn,
    splitChild_distinct hi hy (newroot_distinct hd hsT) fun h => ?_, fun p hp => ?_,
    fun k => (splitChild_inTree (by omega) hi rfl hy hk).trans newroot_inTree, ?_⟩
  · rcases newroot_owns h with e | h
    · exact hsz e.symm
    · exact hzT h
  · rcases (splitChild_owns hi hy).1 hp with h | h
    · rcases newroot_owns h with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rw [splitChild_eq hi hy]
    simp [Tree.keys]


/-- **The memory after the root split and the new root pointer**: only pages `0`, `s`, the old
root's and `z` changed; the branching factor and the free list kept; the root pointer `sv`;
the split root in memory. -/
theorem newroot_mem {B₂ B₄ : ByteArray} {t s z : Nat} {T X₁ : Tree} {φ₂ : List (BitVec 32)}
    {sv : BitVec 32} (hbt : BTreeAt B₂ t T φ₂) (hs : PageOK B₂ s) (hz1 : 1 ≤ z)
    (hU4 : Unchanged (rootMem B₂ (page * s) T.ptr) B₄ (fun p => p = s ∨ p = T.page ∨ p = z))
    (hsz4 : B₄.size = (rootMem B₂ (page * s) T.ptr).size) (hR4 : Repr B₄ X₁)
    (hpgX : ∀ p, Owns p X₁ → PageOK B₂ p) :
    Unchanged B₂ (wr B₄ 4 sv) (fun p => p = 0 ∨ p = s ∨ p = T.page ∨ p = z) ∧
      (wr B₄ 4 sv).size = B₂.size ∧ wd (wr B₄ 4 sv) 0 = wd B₂ 0 ∧ wd (wr B₄ 4 sv) 4 = sv ∧
      OBAnd (wr B₄ 4 sv) 8 16381 φ₂ ∧ Repr (wr B₄ 4 sv) X₁ := by
  obtain ⟨hU3, hsz3⟩ := rootMem_unchanged T.ptr hs.2.2
  have hf := hbt.2.2.2.2.2.2.2.2.2.2.1
  have h8 : 8 + 4 + 4 * 16381 ≤ B₂.size := hf.1.1.2.2.2.2
  have hT1 : 1 ≤ T.page := (hbt.2.2.2.2.2.2.2.2.2.1 _ (Owns.root T)).1
  have hs1 : 1 ≤ s := hs.1
  have hb4 : 4 + 4 ≤ B₄.size := by rw [hsz4, hsz3]; omega
  have hso : SameOutside B₄ (wr B₄ 4 sv) 4 4 := sameOutside_wr sv hb4 (le_refl _) (le_refl _)
  have hU5 : Unchanged B₄ (wr B₄ 4 sv) (· = 0) :=
    SameOutside.unchanged hso fun i h1 h2 => by simp only [page]; omega
  have hsz : B₄.size = B₂.size := hsz4.trans hsz3
  refine ⟨(hU3.mono fun p h => .inr (.inl h)).trans ((hU4.mono fun p h => .inr h).trans
    (hU5.mono fun p h => .inl h)), hso.1.trans (hsz4.trans hsz3), ?_, wd_wr_same sv hb4, ?_, ?_⟩
  · rw [wd_wr_ne sv hb4 (by omega)]
    exact (hU4.wd_eq (by rw [hsz3]; omega) fun i h1 h2 => by simp only [page]; omega).trans
      (hU3.wd_eq (by omega) fun i h1 h2 => by simp only [page]; omega)
  · exact ((hf.frame hU3 fun i h1 h2 => by simp only [page]; omega).frame hU4
      fun i h1 h2 => by simp only [page]; omega).agree (SameOutside.agree hso)
      fun i h1 h2 hr => by omega
  · exact hR4.frame hU5 fun p hp => ⟨by have := (hpgX p hp).1; omega,
      (hpgX p hp).mono hsz.ge⟩


/-- A node with one key is not full. -/
theorem one_lt_keys {t : Nat} (ht : 2 ≤ t) : 1 < 2 * t - 1 := by omega

/-- A page that was free or beyond the old memory is a page the step may change. -/
theorem fresh_owned {B : ByteArray} {T : Tree} {φ : List (BitVec 32)} {p i : Nat}
    (hf : (∃ q ∈ φ, q.toNat = p) ∨ B.size ≤ page * p) (hi : i < B.size)
    (hn : ¬ Owned T φ (i / page)) : ¬ i / page = p := by
  rintro rfl
  rcases hf with h | h
  · exact hn (.inr (.inr h))
  · exact not_fresh hi h

/-- **The split new root is ready for `insert_nonfull`**: a non-full root subtree whose page is
at `4`, a key-preserving step of the old tree. -/
theorem newroot_ready {B B₂ B₄ : ByteArray} {t s z : Nat} {T : Tree} {φ φ₂ : List (BitVec 32)}
    {sv k : BitVec 32} (hbt : BTreeAt B₂ t T φ₂) (hstep : Step B B₂ φ φ₂ T T fun _ => False)
    (hk : ¬ InTree k T) (hfull : T.keys.length = 2 * t - 1) (hsv : sv.toNat = s)
    (hs : PageOK B₂ s) (hz : PageOK B₂ z) (hsT : ¬ Owns s T) (hzT : ¬ Owns z T) (hsz : s ≠ z)
    (hsφ : ∀ q ∈ φ₂, q.toNat ≠ s) (hzφ : ∀ q ∈ φ₂, q.toNat ≠ z)
    (hsf : (∃ q ∈ φ, q.toNat = s) ∨ B.size ≤ page * s)
    (hzf : (∃ q ∈ φ, q.toNat = z) ∨ B.size ≤ page * z)
    (hU4 : Unchanged (rootMem B₂ (page * s) T.ptr) B₄ (fun p => p = s ∨ p = T.page ∨ p = z))
    (hsz4 : B₄.size = (rootMem B₂ (page * s) T.ptr).size)
    (hR4 : Repr B₄ ((Tree.node s false [] [T]).splitChild t z 0)) :
    ∃ d, NFPre (wr B₄ 4 sv) t φ₂ none none true d ((Tree.node s false [] [T]).splitChild t z 0) k ∧
      wd (wr B₄ 4 sv) 4 = ((Tree.node s false [] [T]).splitChild t z 0).ptr ∧
      ((Tree.node s false [] [T]).splitChild t z 0).page = sv.toNat ∧
      Step B (wr B₄ 4 sv) φ φ₂ T ((Tree.node s false [] [T]).splitChild t z 0) fun _ => False := by
  obtain ⟨d, hS⟩ := hbt.sub
  obtain ⟨hp1, ho1, hb1, hd1, hown, hkeys, hlen⟩ :=
    newroot_x1 (d := d) hS.ht hfull hS.ho hS.hb hS.hd hsT hzT hsz
  have hpgX : ∀ p, Owns p ((Tree.node s false [] [T]).splitChild t z 0) → PageOK B₂ p :=
    fun p hp => by rcases hown p hp with rfl | h | rfl; exacts [hs, hS.hpg p h, hz]
  obtain ⟨hU5, hsz5, hw0, hw4, hf5, hR5⟩ := newroot_mem (sv := sv) hbt hs hz.1 hU4 hsz4 hR4 hpgX
  have hptr : ((Tree.node s false [] [T]).splitChild t z 0).ptr = sv := by
    apply BitVec.eq_of_toNat_eq
    have hok : PageOK B₂ ((Tree.node s false [] [T]).splitChild t z 0).page := by rw [hp1]; exact hs
    rw [ptr_toNat hok, hp1, hsv]
  have hkl : ((Tree.node s false [] [T]).splitChild t z 0).keys.length < 2 * t - 1 := by
    rw [hlen]; exact one_lt_keys hS.ht
  refine ⟨d + 1, ⟨⟨hS.ht, hS.ht', hw0.trans hS.h0, by rw [hsz5]; exact hS.hsz, hf5,
    fun q hq => ⟨(hS.hfok q hq).1.mono hsz5.ge, fun ho => ?_⟩, hR5, ho1, hb1, hd1,
    fun p hp => (hpgX p hp).mono hsz5.ge⟩, hkl,
    ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩,
    fun h => hk ((hkeys k).1 h)⟩, by rw [hw4, hptr], hp1.trans hsv.symm,
    ⟨hstep.sub, by rw [hsz5]; exact hstep.size, fun p hp => ?_, ⟨by rw [hsz5]; exact hstep.size,
      fun i hi hn => ?_⟩, fun k => by rw [hkeys k, or_false]⟩⟩
  · rcases hown _ ho with h | h | h
    · exact hsφ q hq h
    · exact (hS.hfok q hq).2 h
    · exact hzφ q hq h
  · rcases hown p hp with rfl | h | rfl
    · exact hsf.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
    · exact .inl h
    · exact hzf.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  · refine (hU5.2 i (lt_of_lt_of_le hi hstep.size) ?_).trans (hstep.frame.2 i hi hn)
    rintro (h | h | h | h)
    · exact hn (.inl h)
    · exact fresh_owned hsf hi hn h
    · exact hn (.inr (.inl (h ▸ Owns.root T)))
    · exact fresh_owned hzf hi hn h


/-- **The new root**: build it on page `sv` with the old root as its only child, split that
child into `zv`, set the root pointer, then `insert_nonfull` (`ins_final`). -/
theorem ins_root {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt mt₂ : MemoryType} {B B₂ : ByteArray}
    {t : Nat} {T : Tree} {φ φ₂ : List (BitVec 32)} (c : ICtx P host s₀ mi)
    (hm : MemAt s₀ mi ma mt B) (h32 : mt₂.address = .i32) (hbt : BTreeAt B₂ t T φ₂)
    (hstep : Step B B₂ φ φ₂ T T fun _ => False) {k sv zv : BitVec 32} (hk : ¬ InTree k T)
    (hfull : T.keys.length = 2 * t - 1) (hs : PageOK B₂ sv.toNat) (hz : PageOK B₂ zv.toNat)
    (hsT : ¬ Owns sv.toNat T) (hzT : ¬ Owns zv.toNat T) (hsz : sv.toNat ≠ zv.toNat)
    (hsφ : ∀ q ∈ φ₂, q.toNat ≠ sv.toNat) (hzφ : ∀ q ∈ φ₂, q.toNat ≠ zv.toNat)
    (hsf : (∃ q ∈ φ, q.toNat = sv.toNat) ∨ B.size ≤ page * sv.toNat)
    (hzf : (∃ q ∈ φ, q.toNat = zv.toNat) ∨ B.size ≤ page * zv.toNat)
    {Q : Post H} (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host (s₀.setMem ma ⟨mt₂, B₂⟩) (fr mi [k, T.ptr, sv, zv]) (vals [] ++ expression rootArm)
      (armPostT P host [] (expression [lget 1, lget 0, call 7]) Q) := by
  have hs0 : (sv * 65536#32).toNat = 65536 * sv.toNat := addr0_of rfl hs.2.1
  have hs0' : (sv * 65536#32).toNat = page * sv.toNat := hs0
  have hssz : 65536 * (sv.toNat + 1) ≤ B₂.size := hs.2.2
  have hm2 : MemAt (s₀.setMem ma ⟨mt₂, B₂⟩) mi ma mt₂ B₂ := MemAt.setMemT hm mt₂ B₂
  wbegin
  wrun
  rw [setMem_setMem, setMem_setMem, setMem_setMem, setMem_setMem]
  rw [hs0']
  change TWP P host (s₀.setMem ma ⟨mt₂, rootMem B₂ (page * sv.toNat) T.ptr⟩) _ _ _
  have hpre : SplitPre (rootMem B₂ (page * sv.toNat) T.ptr) t (.node sv.toNat false [] [T])
      (0#32 : BitVec 32).toNat zv.toNat := newroot_splitPre hbt hs hsT hz hzT hsz hfull
  have hmX : MemAt (s₀.setMem ma ⟨mt₂, rootMem B₂ (page * sv.toNat) T.ptr⟩) c.fiX.module ma mt₂
      (rootMem B₂ (page * sv.toNat) T.ptr) := by
    rw [c.hmX]; exact MemAt.setMemT hm _ _
  have hresX : Resolved (s₀.setMem ma ⟨mt₂, rootMem B₂ (page * sv.toNat) T.ptr⟩) c.fiX.module := by
    rw [c.hmX]; exact c.res.setMem _ _
  refine t_call (rs := []) (args := [.i32 sv, .i32 0#32, .i32 zv]) (by simpa [Idx.toNat] using c.hX)
    c.hfX c.hXS ⟨c.hfX, hresX, sv, 0#32, zv, ma, mt₂, _, t, _, rfl, hmX, rfl, hpre⟩ fun s' o hp => ?_
  obtain ⟨ho, B₄, hs4, hsz4, hR4, hU4⟩ := hp sv 0#32 zv ma mt₂ _ t _ rfl hmX rfl hpre
  refine ⟨ho, ?_⟩
  rw [hs4, setMem_setMem]
  have hm4 : MemAt (s₀.setMem ma ⟨mt₂, B₄⟩) mi ma mt₂ B₄ := MemAt.setMemT hm _ _
  have hb4 : 8 ≤ B₄.size := by
    rw [hsz4, (rootMem_unchanged T.ptr hs.2.2).2]; have := hs.1; simp only [page] at *; omega
  wrun
  rw [setMem_setMem, show (4#32 : BitVec 32).toNat = 4 from rfl]
  obtain ⟨d, hpre', h4, hx, hst⟩ := newroot_ready (sv := sv) (k := k) hbt hstep hk hfull rfl hs hz
    hsT hzT hsz hsφ hzφ hsf hzf hU4 hsz4 hR4
  exact t_armEnd (ins_final c hm h32 hx hpre' h4 hst hQ)
/-- Return `0` after a failed allocation: the tree and its keys are intact. -/
theorem ins_ret0 {s₀ : Store H} {ma : Nat} {B B' : ByteArray} {t : Nat} {T : Tree}
    {φ φ' : List (BitVec 32)} {k : BitVec 32} {Q : Post H} (hQ : InsQ s₀ ma B t T φ k Q)
    {mt' : MemoryType} (h32 : mt'.address = .i32) (hbt : BTreeAt B' t T φ')
    (hst : Step B B' φ φ' T T fun _ => False) {f : Frame} {rest rest' : List Admin} :
    TWP P host (s₀.setMem ma ⟨mt', B'⟩) f (vals [] ++ expression [c32 0, .return_])
      (armPostT P host [] rest (armPostT P host [] rest' Q)) := by
  wbegin
  wrun
  exact t_ret (armPostT_ret (armPostT_ret
    ((hQ 0 mt' B' h32 hst.frame (.inr ⟨rfl, T, φ', hbt, fun _ => Iff.rfl⟩)).2 _)))

/-- The pages for the root split, from the two allocations: valid in the memory after them,
distinct, no longer free, and free or beyond the original memory. -/
theorem two_pages {B B₁ B₂ : ByteArray} {φ φ₁ φ₂ : List (BitVec 32)} {sv zv : BitVec 32}
    (hsub : φ₁.Sublist φ) (hsize : B.size ≤ B₁.size) (hs : PageOK B₁ sv.toNat) (hsφ : sv ∉ φ₁)
    (hsub₂ : φ₂.Sublist φ₁) (hsize₂ : B₁.size ≤ B₂.size) (hzφ : zv ∉ φ₂)
    (hzf : (∃ q ∈ φ₁, q.toNat = zv.toNat) ∨ B₁.size ≤ page * zv.toNat) :
    PageOK B₂ sv.toNat ∧ sv.toNat ≠ zv.toNat ∧ (∀ q ∈ φ₂, q.toNat ≠ sv.toNat) ∧
      (∀ q ∈ φ₂, q.toNat ≠ zv.toNat) ∧
      ((∃ q ∈ φ, q.toNat = zv.toNat) ∨ B.size ≤ page * zv.toNat) := by
  refine ⟨hs.mono hsize₂, fun e => ?_, fun q hq e => hsφ ?_, fun q hq e => hzφ ?_, ?_⟩
  · rcases hzf with ⟨q, hq, hqe⟩ | h
    · exact hsφ (BitVec.eq_of_toNat_eq (hqe.trans e.symm) ▸ hq)
    · have := hs.2.2
      simp only [page] at *
      omega
  · exact BitVec.eq_of_toNat_eq e ▸ hsub₂.subset hq
  · exact BitVec.eq_of_toNat_eq e ▸ hq
  · rcases hzf with ⟨q, hq, hqe⟩ | h
    · exact .inl ⟨q, hsub.subset hq, hqe⟩
    · exact .inr (le_trans hsize h)

/-- **The second allocation** (the page `zv` for the right half), then `ins_root`. -/
theorem ins_alloc2 {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt mt₁ : MemoryType} {B B₁ : ByteArray}
    {t : Nat} {T : Tree} {φ φ₁ : List (BitVec 32)} (c : ICtx P host s₀ mi)
    (hm : MemAt s₀ mi ma mt B) (h32 : mt₁.address = .i32) (hbt : BTreeAt B₁ t T φ₁)
    (hstep : Step B B₁ φ φ₁ T T fun _ => False) {k sv : BitVec 32} (hk : ¬ InTree k T)
    (hfull : T.keys.length = 2 * t - 1) (hs : PageOK B₁ sv.toNat) (hsT : ¬ Owns sv.toNat T)
    (hsφ : sv ∉ φ₁) (hsf : (∃ q ∈ φ, q.toNat = sv.toNat) ∨ B.size ≤ page * sv.toNat)
    {Q : Post H} (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host (s₀.setMem ma ⟨mt₁, B₁⟩) (fr mi [k, T.ptr, sv, 0]) (vals [] ++ expression
      ([call 5, lset 3, lget 3, c32 4294967295, .intRelOp .i32 .eq,
        .if_ .empty [c32 0, .return_] []] ++ rootArm))
      (armPostT P host [] (expression [lget 1, lget 0, call 7]) Q) := by
  have hmA : MemAt (s₀.setMem ma ⟨mt₁, B₁⟩) c.fiA.module ma mt₁ B₁ := by
    rw [c.hmA]; exact MemAt.setMemT hm _ _
  have hf := hbt.2.2.2.2.2.2.2.2.2.2.1
  have hpgφ : ∀ q ∈ φ₁, PageOK B₁ q.toNat := fun q hq => (hbt.2.2.2.2.2.2.2.2.2.2.2 q hq).1
  wbegin
  refine t_call1 (rs := []) (args := []) (by simpa [Idx.toNat] using c.hA) c.hfA c.hAS
    ⟨c.hfA, ma, mt₁, B₁, φ₁, rfl, hmA, h32, hbt.2.2.1, hf, hpgφ⟩ fun s' o hp => ?_
  obtain ⟨r, mt₂, B₂, φ₂, ho, hs2, h32', hA⟩ := hp ma mt₁ B₁ φ₁ rfl hmA h32 hbt.2.2.1 hf hpgφ
  refine ⟨r, ho, ?_⟩
  rw [hs2, setMem_setMem]
  obtain ⟨hbt2, hst2⟩ := alloc_keeps hbt hA
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · exact ins_ret0 hQ h32' hbt2 (hstep.trans hst2)
  · have hr : r ≠ -1 := fun e => by rw [e, ← minus_one] at hc; simp at hc
    obtain ⟨hz, hzφ, hzT, hzf⟩ := alloc_fresh_i hbt hA hr
    obtain ⟨hs2', hsz, hsφ2, hzφ2, hzf'⟩ := two_pages hstep.sub hstep.size hs hsφ hst2.sub hst2.size
      hzφ hzf
    exact t_armEnd (ins_root c hm h32' hbt2 (hstep.trans hst2) hk hfull hs2' hz hsT hzT hsz hsφ2 hzφ2
      hsf hzf' hQ)
/-- **The first allocation** (the page `sv` for the new root), then `ins_alloc2`. -/
theorem ins_alloc1 {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {T : Tree} {φ : List (BitVec 32)} (c : ICtx P host s₀ mi)
    (hm : MemAt s₀ mi ma mt B) (h32 : mt.address = .i32) (hbt : BTreeAt B t T φ) {k : BitVec 32}
    (hk : ¬ InTree k T) (hfull : T.keys.length = 2 * t - 1) {Q : Post H}
    (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host s₀ (fr mi [k, T.ptr, 0, 0]) (vals [] ++ expression fullArm)
      (armPostT P host [] (expression [lget 1, lget 0, call 7]) Q) := by
  have hmA : MemAt s₀ c.fiA.module ma mt B := by rw [c.hmA]; exact hm
  have hf := hbt.2.2.2.2.2.2.2.2.2.2.1
  have hpgφ : ∀ q ∈ φ, PageOK B q.toNat := fun q hq => (hbt.2.2.2.2.2.2.2.2.2.2.2 q hq).1
  wbegin
  refine t_call1 (rs := []) (args := []) (by simpa [Idx.toNat] using c.hA) c.hfA c.hAS
    ⟨c.hfA, ma, mt, B, φ, rfl, hmA, h32, hbt.2.2.1, hf, hpgφ⟩ fun s' o hp => ?_
  obtain ⟨r, mt₁, B₁, φ₁, ho, hs1, h32', hA⟩ := hp ma mt B φ rfl hmA h32 hbt.2.2.1 hf hpgφ
  refine ⟨r, ho, ?_⟩
  rw [hs1]
  obtain ⟨hbt1, hst1⟩ := alloc_keeps hbt hA
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · exact ins_ret0 hQ h32' hbt1 hst1
  · have hr : r ≠ -1 := fun e => by rw [e, ← minus_one] at hc; simp at hc
    obtain ⟨hs, hsφ, hsT, hsf⟩ := alloc_fresh_i hbt hA hr
    exact t_armEnd (ins_alloc2 c hm h32' hbt1 hst1 hk hfull hs hsT hsφ hsf hQ)

/-- The empty step. -/
theorem Step.refl (B : ByteArray) (φ : List (BitVec 32)) (T : Tree) :
    Step B B φ φ T T fun _ => False :=
  ⟨List.Sublist.refl _, le_refl _, fun _ h => .inl h, Unchanged.refl _ _, fun _ => by rw [or_false]⟩

/-- The keys of a tree in memory, as a bounded array. -/
theorem Repr.keysBA {B : ByteArray} {T : Tree} (h : Repr B T) :
    BA B (page * T.page + 4) 8090 T.keys := by
  obtain ⟨x, l, ks, cs⟩ := T
  exact h.leaf_iff.2.2.1.1.1

/-- A balanced node has at most `2 t - 1` keys. -/
theorem Balanced.keys_le {t d : Nat} {r : Bool} {T : Tree} (h : Balanced t r d T) :
    T.keys.length ≤ 2 * t - 1 := by
  cases h with
  | leaf hk => exact hk.2
  | inner hk _ => exact hk.2

/-- **After the search found nothing**: load the root, grow it if it is full
(`ins_alloc1`), then `insert_nonfull` (`ins_final`). -/
theorem ins_part2 {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {T : Tree} {φ : List (BitVec 32)} (c : ICtx P host s₀ mi)
    (hm : MemAt s₀ mi ma mt B) (h32 : mt.address = .i32) (hbt : BTreeAt B t T φ) {k : BitVec 32}
    (hk : ¬ InTree k T) {Q : Post H} (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host s₀ (fr mi [k, 0, 0, 0]) (vals ([] : List Val).reverse ++ expression insPart2) Q := by
  obtain ⟨d, hS⟩ := hbt.sub
  have hroot : (wd B 4).toNat = T.page := hbt.root
  have hpg : PageOK B T.page := hbt.2.2.2.2.2.2.2.2.2.1 _ (Owns.root T)
  have h8 : 8 + 4 + 4 * 16381 ≤ B.size := hS.hfree.1.1.2.2.2.2
  have hra : (wd B 4 * 65536#32).toNat = 65536 * T.page := addr0_of hroot hpg.2.1
  have hsz : 65536 * (T.page + 1) ≤ B.size := hpg.2.2
  have hK : BA B (page * T.page + 4) 8090 T.keys := hS.hR.keysBA
  have hkl : T.keys.length ≤ 2 * t - 1 := hS.hb.keys_le
  have hlen : wd B ((wd B 4 * 65536#32).toNat + ((4 : Fin (2 ^ 64)) : Nat)) =
      BitVec.ofNat 32 T.keys.length := by rw [hra]; exact hK.1
  have htw : wd B 0 * 2#32 - 1#32 = BitVec.ofNat 32 (2 * t - 1) := by
    rw [hS.h0]; have := hS.ht; have := hS.ht'; apply BitVec.eq_of_toNat_eq
    rw [toNat_ofNat_lt (by omega)]; bv_omega
  have h4 : wd B 4 = T.ptr := hbt.2.2.2.2.1
  wbegin
  wrun
  rw [show (4#32 : BitVec 32).toNat = 4 from rfl]
  wrun
  rw [show (0#32 : BitVec 32).toNat = 0 from rfl, hlen, htw, h4]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · have he : BitVec.ofNat 32 T.keys.length = BitVec.ofNat 32 (2 * t - 1) := by simpa using hc
    have hfull : T.keys.length = 2 * t - 1 := by
      have e := congrArg BitVec.toNat he
      rwa [toNat_ofNat_lt (by have := hS.ht'; omega), toNat_ofNat_lt (by have := hS.ht'; omega)] at e
    exact ins_alloc1 c hm h32 hbt hk hfull hQ
  · have hne : BitVec.ofNat 32 T.keys.length ≠ BitVec.ofNat 32 (2 * t - 1) := by simpa using hc
    have hlt : T.keys.length < 2 * t - 1 := lt_of_le_of_ne hkl fun e => hne (by rw [e])
    rw [← hm.setMem_self]
    exact t_armEnd (ins_final c hm h32 (rv := T.ptr) (ptr_toNat hpg).symm
      ⟨hS, hlt, ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩, hk⟩ h4
      (Step.refl B φ T) hQ)

/-- **The body of `btree_insert`**: `btree_search`, returning `1` if `k` is a key, else
`ins_part2`. -/
theorem insert_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {T : Tree} {φ : List (BitVec 32)} (c : ICtx P host s₀ mi)
    (hm : MemAt s₀ mi ma mt B) (h32 : mt.address = .i32) (hbt : BTreeAt B t T φ) {k : BitVec 32}
    {Q : Post H} (hQ : InsQ s₀ ma B t T φ k Q) :
    TWP P host s₀ (fr mi [k, 0, 0, 0]) (vals [] ++ expression
      ([lget 0, call 2, .if_ .empty [c32 1, .return_] []] ++ insPart2)) Q := by
  have hmS : MemAt s₀ c.fiS.module ma mt B := by rw [c.hmS]; exact hm
  have hresS : Resolved s₀ c.fiS.module := by rw [c.hmS]; exact c.res
  have hB : IsBTree B t fun k => InTree k T := ⟨T, φ, hbt, fun _ => Iff.rfl⟩
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 k]) (by simpa [Idx.toNat] using c.hS) c.hfS c.hSS
    ⟨c.hfS, hresS, k, ma, mt, B, t, _, rfl, hmS, hB⟩ fun s' o hp => ?_
  obtain ⟨b, ho, h1, h0⟩ := hp.2 k ma mt B t _ rfl hmS hB
  refine ⟨b, ho, ?_⟩
  rw [hp.1]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · show TWP P host s₀ _ _ (armPostT P host [] _ Q)
    have hk : InTree k T := by
      by_contra hn
      exact hc (h0 hn)
    have hkeys : IsBTree B t fun k' => InTree k' T ∨ k' = k :=
      ⟨T, φ, hbt, fun k' => ⟨fun h => .inl h, fun h => h.elim id fun e => e ▸ hk⟩⟩
    have hq : ∀ F, Q s₀ F (.ret [.i32 1]) := by
      have h := (hQ 1 mt B h32 (Unchanged.refl _ _) (.inl ⟨rfl, hkeys⟩)).2
      rwa [hm.setMem_self] at h
    wbegin
    wrun
    exact t_ret (armPostT_ret (hq _))
  · have hk : ¬ InTree k T := fun h => by rw [h1 h] at hc; exact absurd hc (by decide)
    exact t_armEnd (ins_part2 c hm h32 hbt hk hQ)

/-- The postcondition of `btree_insert` for an outcome `ins_body` allows: the tree and the
free pages are determined by the memory. -/
theorem insert_post {a : Nat} {fi : FuncInst H} {s : Store H} {k : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {t : Nat} {T : Tree} {φ : List (BitVec 32)}
    (hm : MemAt s fi.module ma mt B) (hbt : BTreeAt B t T φ) {b : BitVec 32} {mt' : MemoryType}
    {B' : ByteArray} (h32 : mt'.address = .i32) (hU : Unchanged B B' (Owned T φ))
    (hres : (b = 1 ∧ IsBTree B' t fun k' => InTree k' T ∨ k' = k) ∨
      (b = 0 ∧ IsBTree B' t fun k' => InTree k' T)) :
    (insertSpec a fi).post s [.i32 k] (s.setMem ma ⟨mt', B'⟩) (.normal [.i32 b]) := by
  intro k' ma' mt'' B'' t' T' φ' hargs hm' _ hbt'
  have hk : k' = k := i32_inj (List.cons.inj hargs).1
  subst hk
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  obtain ⟨rfl, rfl, rfl⟩ := hbt.unique hbt'
  exact ⟨b, mt', B', rfl, rfl, h32, hU, hres⟩

/-- **`btree_insert` meets `insertSpec`**, given `insert_nonfull`'s specification. -/
theorem insert_valid_of {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm insertFunc)
    (har : HasArity fi 1 1)
    (hNF : ∀ (a' : Nat) (fi' : FuncInst H), fi'.code = .wasm insertNonfullFunc →
      HasArity fi' 2 1 → ∀ lo hi r d, TFSpecAt P host a' (insNFSpec a' fi' lo hi r d)) :
    TFSpecAt P host a (insertSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, -, k, ma, mt, B, t, κ, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨hf, hres, k, ma, mt, B, t, κ, hargs, hm, h32, T, φ, hbt, hκ⟩ f vs₀
    rw [hargs, forCall_insert, insertFunc_body, hrs]
    exact insert_body (ICtx.ofResolved hres hNF) hm h32 hbt fun b mt' B' h32' hU hr =>
      ⟨fun _ => bodyPostT_normal rfl (insert_post hm hbt h32' hU hr),
        fun _ => bodyPostT_ret (insert_post hm hbt h32' hU hr)⟩

end Silmaril.WasmSpec.BTree.V2
