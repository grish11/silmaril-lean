module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Calls
public import Silmaril.Proofs.WasmSpec.BTree.V2.Trees
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# The B-tree library, version 2: `btree_search` by tactics

The descent loop of `btree_search` has the invariant "page `x` holds a subtree `T'` of height
`d`, ordered within some bounds and balanced, and `k ∈ κ` iff `k` is a key of `T'`" (`At`),
and the variant "the least such height" (`SV`). Each iteration calls `oba_find` and
`oba_get` with the total call rule (`t_call1`) and their proved specifications; a key found
returns `1`, a leaf returns `0`, and otherwise the loop descends into child `i` (the
`oba_find` index), which holds `k` iff the node does (`inTree_child_iff`), at height `d - 1`.
Every-run total correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The loop body of `btree_search`. -/
abbrev searchLoop : List Instr := [
  lget 1, c32 65536, imul, c32 4, iadd, lset 3,
  lget 3, lget 0, call 1, lset 2,
  lget 2, lget 3, iload, iltu,
  .if_ .empty [lget 3, lget 2, call 0, lget 0, .intRelOp .i32 .eq,
    .if_ .empty [c32 1, .return_] []] [],
  lget 1, c32 65536, imul, iload,
  .if_ .empty [c32 0, .return_] [],
  lget 1, c32 65536, imul, c32 32768, iadd, lget 2, call 0, lset 1,
  br 0]

theorem searchFunc_body : searchFunc.body =
    [c32 4, iload, lset 1, .block .empty [.loop .empty searchLoop], c32 0] := rfl

theorem forCall_search (mi : ModuleInst) (k : BitVec 32) :
    Frame.forCall mi [.i32 k] searchFunc.locals = fr mi [k, 0, 0, 0] := rfl

/-- **The descent invariant's subtree**: page `x` holds a subtree of height `d`, ordered within
some bounds, balanced, its pages valid, holding `k` iff `κ` does. -/
def At (B : ByteArray) (t : Nat) (k : BitVec 32) (κ : BitVec 32 → Prop) (x d : Nat) : Prop :=
  ∃ (T : Tree) (lo hi : Option (BitVec 32)) (r : Bool), Repr B T ∧ T.page = x ∧
    Ordered lo hi T ∧ Balanced t r d T ∧ (∀ p, Owns p T → PageOK B p) ∧ (κ k ↔ InTree k T)

/-- **The loop invariant of `btree_search`**: the store is unchanged and local `x` is a page
holding a subtree as in `At`. -/
def SInv (s₀ : Store H) (mi : ModuleInst) (B : ByteArray) (t : Nat) (k : BitVec 32)
    (κ : BitVec 32 → Prop) (s : Store H) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ x i ks : BitVec 32, f = fr mi [k, x, i, ks] ∧ ∃ d, At B t k κ x.toNat d

/-- **The variant**: the least height of a subtree at page `x` as in `At`. -/
noncomputable def SV (B : ByteArray) (t : Nat) (k : BitVec 32) (κ : BitVec 32 → Prop)
    (_ : Store H) (f : Frame) : Nat :=
  sInf {d | At B t k κ (loc f 1) d}

/-- The callees of `btree_search` and the memory. -/
structure SCtx (P : Profile) (host : HostSemantics H) (s₀ : Store H) (mi : ModuleInst)
    (ma : Nat) (mt : MemoryType) (B : ByteArray) : Type where
  aG : Nat
  fiG : FuncInst H
  aF : Nat
  fiF : FuncInst H
  hG : mi.funcs[0]? = some aG
  hfG : s₀.funcs[aG]? = some fiG
  hGS : TFSpecAt P host aG (getSpec aG fiG)
  hmG : fiG.module = mi
  hF : mi.funcs[1]? = some aF
  hfF : s₀.funcs[aF]? = some fiF
  hFS : TFSpecAt P host aF (findSpec aF fiF)
  hmF : fiF.module = mi
  hm : MemAt s₀ mi ma mt B

/-- A page's address as an `i32`. -/
theorem page_addr {x : BitVec 32} (hx : x.toNat < 32768) (c : Nat) (hc : c < 65536) :
    (x * 65536#32 + BitVec.ofNat 32 c).toNat = page * x.toNat + c := by
  show _ = 65536 * x.toNat + c
  have h1 : (x * 65536#32).toNat = x.toNat * 65536 := by
    rw [BitVec.toNat_mul]
    have : (65536#32).toNat = 65536 := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat 32 c).toNat = c := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, h1, h2]
  exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)

/-- A page's address as an `i32`, with no offset. -/
theorem page_addr0 {x : BitVec 32} (hx : x.toNat < 32768) :
    (x * 65536#32).toNat = page * x.toNat := by
  have h := page_addr hx 0 (by omega)
  simpa using h

/-- A child's pointer is its page, for a valid page. -/
theorem ptr_toNat {B : ByteArray} {T : Tree} (h : PageOK B T.page) : T.ptr.toNat = T.page := by
  rw [Tree.ptr, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := h.2.1; omega)

/-- `oba_find`'s index of an inner node is a child index, below `2 ^ 32`. -/
theorem child_index {B : ByteArray} {x : Nat} {kk : List (BitVec 32)} {cs : List Tree}
    {lo hi : Option (BitVec 32)} {k : BitVec 32} {j : Nat}
    (hR : Repr B (.node x false kk cs)) (ho : Ordered lo hi (.node x false kk cs))
    (hF : FindsAt kk k j) : j < cs.length ∧ (BitVec.ofNat 32 j).toNat = j := by
  have hlen : cs.length = kk.length + 1 := by
    cases ho with
    | mk _ _ hlen _ => simpa using hlen
  have hcap : cs.length ≤ 8091 := by
    cases hR with
    | inner _ _ hP _ => simpa using hP.2.2.1
  have hj : j < cs.length := by have := hF.1; omega
  refine ⟨hj, ?_⟩
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The descent step**: child `j` of an inner node, `j` the `oba_find` index of a key `k`
that is not among the node's keys, is a subtree as in `At`, one level lower. -/
theorem child_at {B : ByteArray} {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop} {x : Nat}
    {kk : List (BitVec 32)} {cs : List Tree} {lo hi : Option (BitVec 32)} {r : Bool} {d' j : Nat}
    (hR : Repr B (.node x false kk cs)) (ho : Ordered lo hi (.node x false kk cs))
    (hb : Balanced t r (d' + 1) (.node x false kk cs))
    (hpages : ∀ p, Owns p (.node x false kk cs) → PageOK B p)
    (hiff : κ k ↔ InTree k (.node x false kk cs)) (hF : FindsAt kk k j) (hnot : k ∉ kk)
    (hj : j < cs.length) : At B t k κ cs[j].ptr.toNat d' := by
  have hmem : cs[j] ∈ cs := List.getElem_mem hj
  have hcR : Repr B cs[j] := by
    cases hR with
    | inner _ _ _ hcR => exact hcR _ hmem
  have hcb : Balanced t false d' cs[j] := by
    cases hb with
    | inner _ hc => exact hc _ hmem
  have hco : Ordered (if j = 0 then lo else kk[j - 1]?) (if j = kk.length then hi else kk[j]?)
      cs[j] := by
    cases ho with
    | mk _ _ _ hcs => exact hcs j hj
  have hpt : cs[j].ptr.toNat = cs[j].page := ptr_toNat (hpages _ (.child hmem (Owns.root _)))
  exact ⟨cs[j], _, _, false, hcR, hpt.symm, hco, hcb, fun p hp => hpages p (.child hmem hp),
    hiff.trans (inTree_child_iff ho hF hnot hj)⟩

/-- At a leaf, `btree_search` returns `0`. -/
theorem search_leaf {s : Store H} {f : Frame} {Inv : Store H → Frame → Prop}
    {V : Store H → Frame → Nat} {v : Nat} {rest rest' : List Admin} {Q : Post H}
    (hQ : Q s f (.ret [.i32 0])) :
    TWP P host s f (vals [] ++ expression [c32 0, .return_])
      (armPostT P host [] rest (whilePostT P host Inv V v rest' Q)) := by
  wbegin
  wrun
  exact t_ret (armPostT_ret (whilePostT_ret hQ))

/-- At an inner node, `btree_search` reads child `j`'s page with `oba_get` and repeats the
loop with it. -/
theorem search_descend {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop}
    (c : SCtx P host s mi ma mt B) {Q : Post H} {x keys : BitVec 32} {j d' : Nat}
    {cs : List Tree} (hx32 : x.toNat < 32768)
    (hP : BA B (page * x.toNat + 32768) 8091 (cs.map Tree.ptr)) (hj : j < cs.length)
    (hjn : (BitVec.ofNat 32 j).toNat = j) (hAt : At B t k κ cs[j].ptr.toNat d') :
    TWP P host s (fr mi [k, x, BitVec.ofNat 32 j, keys]) (vals ([] : List Val).reverse ++
      expression [lget 1, c32 65536, imul, c32 32768, iadd, lget 2, call 0, lset 1, br 0])
      (whilePostT P host (SInv s mi B t k κ) (SV B t k κ) (d' + 1) [.plain (c32 0)] Q) := by
  have hxp : (x * 65536#32 + 32768#32).toNat = page * x.toNat + 32768 :=
    page_addr hx32 32768 (by omega)
  have hP' : BA B (x * 65536#32 + 32768#32).toNat 8091 (cs.map Tree.ptr) := by rwa [hxp]
  have hjl : (BitVec.ofNat 32 j).toNat < (cs.map Tree.ptr).length := by simpa [hjn] using hj
  have hm : MemAt s c.fiG.module ma mt B := by rw [c.hmG]; exact c.hm
  have hv : (cs.map Tree.ptr).getD (BitVec.ofNat 32 j).toNat 0 = cs[j].ptr := by simp [hjn, hj]
  have hloc : loc (fr mi [k, cs[j].ptr, BitVec.ofNat 32 j, keys]) 1 = cs[j].ptr.toNat := by
    rw [loc_fr (by simp)]; rfl
  have hlt : SV B t k κ s (fr mi [k, cs[j].ptr, BitVec.ofNat 32 j, keys]) < d' + 1 := by
    show sInf _ < _
    rw [hloc]
    exact lt_of_le_of_lt (Nat.sInf_le hAt) (Nat.lt_succ_self _)
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 (x * 65536#32 + 32768#32), .i32 (BitVec.ofNat 32 j)])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt, B, 8091, _, rfl, hm, hP', hjl⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt B 8091 _ rfl (hp.1 ▸ hm) hP' hjl, ?_⟩
  rw [hv, hp.1]
  wrun
  exact t_br (whilePostT_cont ⟨rfl, _, _, _, rfl, d', hAt⟩ hlt)

/-- The end of the loop body: the leaf test and the descent. -/
abbrev searchTail : List Instr := [lget 1, c32 65536, imul, iload, .if_ .empty [c32 0, .return_] [],
  lget 1, c32 65536, imul, c32 32768, iadd, lget 2, call 0, lset 1, br 0]

/-- After the comparison with key `j`: return `0` at a leaf, else descend into child `j`. -/
theorem search_tail {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop} (c : SCtx P host s mi ma mt B) {Q : Post H}
    (hQ0 : ¬ κ k → ∀ F, Q s F (.ret [.i32 0])) {x keys : BitVec 32} {j : Nat} {l : Bool}
    {kk : List (BitVec 32)} {cs : List Tree} {lo hi : Option (BitVec 32)} {r : Bool} {d₀ : Nat}
    (hR : Repr B (.node x.toNat l kk cs)) (ho : Ordered lo hi (.node x.toNat l kk cs))
    (hb : Balanced t r d₀ (.node x.toNat l kk cs))
    (hpages : ∀ p, Owns p (.node x.toNat l kk cs) → PageOK B p)
    (hiff : κ k ↔ InTree k (.node x.toNat l kk cs)) (hF : FindsAt kk k j)
    (hne : ∀ h : j < kk.length, kk[j] ≠ k) :
    TWP P host s (fr mi [k, x, BitVec.ofNat 32 j, keys]) (vals ([] : List Val).reverse ++
      expression searchTail)
      (whilePostT P host (SInv s mi B t k κ) (SV B t k κ) d₀ [.plain (c32 0)] Q) := by
  have hpok : PageOK B x.toNat := hpages _ .here
  have hx0 : (x * 65536#32).toNat = 65536 * x.toNat := page_addr0 hpok.2.1
  have hsz : 65536 * (x.toNat + 1) ≤ B.size := hpok.2.2
  have hm : MemAt s mi ma mt B := c.hm
  have hnot : k ∉ kk := not_mem_of_findsAt (by cases ho; assumption) hF hne
  wbegin
  wrun
  rw [hx0]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨rfl, rfl⟩ : l = true ∧ cs = [] := by
      cases hR with
      | leaf => exact ⟨rfl, rfl⟩
      | inner hl => exact absurd hl hc
    exact search_leaf (hQ0 (fun h => hnot (inTree_leaf.1 (hiff.1 h))) _)
  · show TWP P host s _ _ (armPostT P host [] _ _)
    obtain rfl : l = false := by
      cases hR with
      | leaf hl => exact absurd hc hl
      | inner => rfl
    obtain ⟨hj, hjn⟩ : j < cs.length ∧ (BitVec.ofNat 32 j).toNat = j := child_index hR ho hF
    obtain ⟨d', rfl⟩ : ∃ d', d₀ = d' + 1 := by
      cases hb with
      | inner _ _ => exact ⟨_, rfl⟩
    have hP : BA B (page * x.toNat + 32768) 8091 (cs.map Tree.ptr) := by
      cases hR with
      | inner _ _ hP _ => exact hP
    exact t_armEnd (search_descend c hpok.2.1 hP hj hjn
      (child_at hR ho hb hpages hiff hF hnot hj))

/-- Key `j` of the node, when there is one: `1` if it is `k`. -/
theorem search_hit {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop} (c : SCtx P host s mi ma mt B) {Q : Post H}
    (hQ1 : κ k → ∀ F, Q s F (.ret [.i32 1])) (hQ0 : ¬ κ k → ∀ F, Q s F (.ret [.i32 0]))
    {x : BitVec 32} {j : Nat} {l : Bool} {kk : List (BitVec 32)} {cs : List Tree}
    {lo hi : Option (BitVec 32)} {r : Bool} {d₀ : Nat}
    (hR : Repr B (.node x.toNat l kk cs)) (ho : Ordered lo hi (.node x.toNat l kk cs))
    (hb : Balanced t r d₀ (.node x.toNat l kk cs))
    (hpages : ∀ p, Owns p (.node x.toNat l kk cs) → PageOK B p)
    (hiff : κ k ↔ InTree k (.node x.toNat l kk cs)) (hF : FindsAt kk k j)
    (hK : BA B (x * 65536#32 + 4#32).toNat 8090 kk) (hjl : j < kk.length)
    (hjn : (BitVec.ofNat 32 j).toNat = j) :
    TWP P host s (fr mi [k, x, BitVec.ofNat 32 j, x * 65536#32 + 4#32]) (vals [] ++ expression
      [lget 3, lget 2, call 0, lget 0, .intRelOp .i32 .eq, .if_ .empty [c32 1, .return_] []])
      (armPostT P host [] (expression searchTail)
        (whilePostT P host (SInv s mi B t k κ) (SV B t k κ) d₀ [.plain (c32 0)] Q)) := by
  have hm : MemAt s c.fiG.module ma mt B := by rw [c.hmG]; exact c.hm
  have hjl' : (BitVec.ofNat 32 j).toNat < kk.length := by rwa [hjn]
  have hv : kk.getD (BitVec.ofNat 32 j).toNat 0 = kk[j] := by rw [hjn, getD_of_lt _ hjl]
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 (x * 65536#32 + 4#32), .i32 (BitVec.ofNat 32 j)])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt, B, 8090, kk, rfl, hm, hK, hjl'⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt B 8090 kk rfl (hp.1 ▸ hm) hK hjl', ?_⟩
  rw [hv, hp.1]
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · have hk : κ k := hiff.2 (.here ((show kk[j] = k by simpa using hc) ▸ List.getElem_mem hjl))
    wbegin
    wrun
    exact t_ret (armPostT_ret (armPostT_ret (whilePostT_ret (hQ1 hk _))))
  · have hne : kk[j] ≠ k := by simpa using hc
    exact t_armEnd (t_armEnd (search_tail c hQ0 hR ho hb hpages hiff hF fun _ => hne))

/-- After `oba_find` returned `j`: compare key `j`, then the leaf test and the descent. -/
theorem search_cmp {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop} (c : SCtx P host s mi ma mt B) {Q : Post H}
    (hQ1 : κ k → ∀ F, Q s F (.ret [.i32 1])) (hQ0 : ¬ κ k → ∀ F, Q s F (.ret [.i32 0]))
    {x i : BitVec 32} {j : Nat} {l : Bool} {kk : List (BitVec 32)} {cs : List Tree}
    {lo hi : Option (BitVec 32)} {r : Bool} {d₀ : Nat}
    (hR : Repr B (.node x.toNat l kk cs)) (ho : Ordered lo hi (.node x.toNat l kk cs))
    (hb : Balanced t r d₀ (.node x.toNat l kk cs))
    (hpages : ∀ p, Owns p (.node x.toNat l kk cs) → PageOK B p)
    (hiff : κ k ↔ InTree k (.node x.toNat l kk cs)) (hF : FindsAt kk k j)
    (hK : BA B (x * 65536#32 + 4#32).toNat 8090 kk) :
    TWP P host s (fr mi [k, x, i, x * 65536#32 + 4#32])
      (vals [Val.i32 (BitVec.ofNat 32 j)].reverse ++ expression
      ([lset 2, lget 2, lget 3, iload, iltu, .if_ .empty [lget 3, lget 2, call 0, lget 0,
        .intRelOp .i32 .eq, .if_ .empty [c32 1, .return_] []] []] ++ searchTail))
      (whilePostT P host (SInv s mi B t k κ) (SV B t k κ) d₀ [.plain (c32 0)] Q) := by
  have hm : MemAt s mi ma mt B := c.hm
  have hjn : (BitVec.ofNat 32 j).toNat = j := by
    have : kk.length ≤ 8090 := hK.2.2.1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hF.1; omega)
  have hlen : (wd B (x * 65536#32 + 4#32).toNat).toNat = kk.length := hK.len
  have hb4 : (x * 65536#32 + 4#32).toNat + 4 ≤ B.size := by have := hK.2.2.2.2; omega
  wbegin
  wrun
  rw [hlen, hjn]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · exact search_hit c hQ1 hQ0 hR ho hb hpages hiff hF hK (by simpa using hc) hjn
  · have hjl : ¬ j < kk.length := by simpa using hc
    exact t_armEnd (search_tail c hQ0 hR ho hb hpages hiff hF fun h => absurd h hjl)

/-- The loop body at a node: `oba_find`, then `search_cmp`. -/
theorem search_node {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop}
    (c : SCtx P host s mi ma mt B) {Q : Post H} (hQ1 : κ k → ∀ F, Q s F (.ret [.i32 1]))
    (hQ0 : ¬ κ k → ∀ F, Q s F (.ret [.i32 0])) {x i ks : BitVec 32} {l : Bool}
    {kk : List (BitVec 32)} {cs : List Tree} {lo hi : Option (BitVec 32)} {r : Bool} {d₀ : Nat}
    (hR : Repr B (.node x.toNat l kk cs)) (ho : Ordered lo hi (.node x.toNat l kk cs))
    (hb : Balanced t r d₀ (.node x.toNat l kk cs))
    (hpages : ∀ p, Owns p (.node x.toNat l kk cs) → PageOK B p)
    (hiff : κ k ↔ InTree k (.node x.toNat l kk cs)) :
    TWP P host s (fr mi [k, x, i, ks]) (vals [] ++ expression searchLoop)
      (whilePostT P host (SInv s mi B t k κ) (SV B t k κ) d₀ [.plain (c32 0)] Q) := by
  have hpok : PageOK B x.toNat := hpages _ .here
  have hka : (x * 65536#32 + 4#32).toNat = page * x.toNat + 4 := page_addr hpok.2.1 4 (by omega)
  have hK : OBA B (x * 65536#32 + 4#32).toNat 8090 kk := by
    rw [hka]
    cases hR <;> exact (by assumption : OBAnd _ _ _ _).1
  have hm : MemAt s c.fiF.module ma mt B := by rw [c.hmF]; exact c.hm
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 (x * 65536#32 + 4#32), .i32 k])
    (by simpa [Idx.toNat] using c.hF) c.hfF c.hFS ⟨c.hfF, _, _, ma, mt, B, 8090, kk, rfl, hm, hK⟩
    fun s' o hp => ?_
  obtain ⟨j, hF, ho'⟩ := hp.2 _ _ ma mt B 8090 kk rfl (hp.1 ▸ hm) hK
  refine ⟨_, ho', ?_⟩
  rw [hp.1]
  exact search_cmp c hQ1 hQ0 hR ho hb hpages hiff hF hK.1

/-- **One iteration of `btree_search`'s loop**, at the least height of the invariant. -/
theorem search_iter {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {t : Nat} {k : BitVec 32} {κ : BitVec 32 → Prop}
    (c : SCtx P host s₀ mi ma mt B) {Q : Post H} (hQ1 : κ k → ∀ F, Q s₀ F (.ret [.i32 1]))
    (hQ0 : ¬ κ k → ∀ F, Q s₀ F (.ret [.i32 0])) {s : Store H} {f : Frame}
    (hI : SInv s₀ mi B t k κ s f) :
    TWP P host s f (vals [] ++ expression searchLoop)
      (whilePostT P host (SInv s₀ mi B t k κ) (SV B t k κ) (SV B t k κ s f) [.plain (c32 0)] Q) := by
  obtain ⟨hs, x, i, ks, hf, d, hAt⟩ := hI
  have hV : SV B t k κ s f = sInf {d | At B t k κ x.toNat d} := by
    rw [hf]
    simp only [SV, loc_fr (L := [k, x, i, ks]) (k := 1) (by simp)]
    rfl
  have hmin : At B t k κ x.toNat (sInf {d | At B t k κ x.toNat d}) :=
    Nat.sInf_mem (s := {d | At B t k κ x.toNat d}) ⟨d, hAt⟩
  rw [hV]
  obtain ⟨⟨y, l, kk, cs⟩, lo, hi, r, hR, hpg, ho, hb, hpages, hiff⟩ := hmin
  obtain rfl : y = x.toNat := hpg
  rw [hs, hf]
  exact search_node c hQ1 hQ0 hR ho hb hpages hiff

/-- The postcondition of `btree_search`: the answer for `κ` is the answer for every key set of
the same memory (the tree is determined by the memory). -/
theorem search_post {a : Nat} {fi : FuncInst H} {s : Store H} {k : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {t : Nat} {T : Tree} {φ : List (BitVec 32)}
    (hm : MemAt s fi.module ma mt B) (hbt : BTreeAt B t T φ) {b : BitVec 32}
    (hb : (InTree k T → b = 1) ∧ (¬ InTree k T → b = 0)) :
    (searchSpec a fi).post s [.i32 k] s (.normal [.i32 b]) := by
  refine ⟨rfl, fun k' ma' mt' B' t' κ' hargs hm' ⟨T', φ', hbt', hκ'⟩ => ⟨b, rfl, ?_⟩⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain rfl := i32_inj hargs
  obtain ⟨-, -, rfl⟩ := hm'.unique hm
  have hT : T = T' := by
    obtain ⟨-, -, -, -, h4, hR, -, -, -, hpg, -, -⟩ := hbt
    obtain ⟨-, -, -, -, h4', hR', -, -, -, hpg', -, -⟩ := hbt'
    refine Repr.unique hR hR' ?_ (fun p hp => by have := (hpg p hp).2.1; omega)
      (fun p hp => by have := (hpg' p hp).2.1; omega)
    have e1 := (hpg _ (Owns.root T)).2.1
    have e2 := (hpg' _ (Owns.root T')).2.1
    have := congrArg BitVec.toNat (h4.symm.trans h4')
    simp only [Tree.ptr, BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  subst hT
  exact ⟨fun h => hb.1 ((hκ' k').2 h), fun h => hb.2 fun h' => h ((hκ' k').1 h')⟩

/-- The body of `btree_search`: load the root page, then the loop. -/
theorem search_body {fi : FuncInst H} {s : Store H} {k : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {t : Nat} {κ : BitVec 32 → Prop} {T : Tree}
    {φ : List (BitVec 32)} (c : SCtx P host s fi.module ma mt B) (hbt : BTreeAt B t T φ)
    (hκ : ∀ k, InTree k T ↔ κ k) {Q : Post H}
    (hQ : ∀ b : BitVec 32, (InTree k T → b = 1) → (¬ InTree k T → b = 0) → ∀ F,
      Q s F (.ret [.i32 b])) :
    TWP P host s (fr fi.module [k, 0, 0, 0]) (vals [] ++ expression
      [c32 4, iload, lset 1, .block .empty [.loop .empty searchLoop], c32 0]) Q := by
  obtain ⟨-, -, -, -, h4, hR, ho, ⟨d, hb⟩, -, hpg, hfree, -⟩ := hbt
  have hm : MemAt s fi.module ma mt B := c.hm
  have h8 : 8 + 4 + 4 * 16381 ≤ B.size := hfree.1.1.2.2.2.2
  have hroot : (wd B 4).toNat = T.page := by
    rw [h4]
    exact ptr_toNat (hpg _ (Owns.root T))
  have hAt : At B t k κ (wd B 4).toNat d :=
    ⟨T, none, none, true, hR, hroot.symm, ho, hb, hpg, (hκ k).symm⟩
  wbegin
  wrun
  exact t_while (Inv := SInv s fi.module B t k κ) (V := SV B t k κ)
    ⟨rfl, _, _, _, rfl, d, hAt⟩ (fun _ _ hI => search_iter c
      (fun h => hQ 1 (fun _ => rfl) (fun h' => absurd ((hκ k).2 h) h'))
      (fun h => hQ 0 (fun h' => absurd ((hκ k).1 h') h) (fun _ => rfl)) hI)

/-- The callees of `btree_search`, from `Resolved`. -/
noncomputable def SCtx.ofResolved {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} (hres : Resolved s mi) (hm : MemAt s mi ma mt B) :
    SCtx P host s mi ma mt B :=
  let g := Classical.choose_spec (Classical.choose_spec (hres.get (j := 0) (by decide)))
  let f := Classical.choose_spec (Classical.choose_spec (hres.get (j := 1) (by decide)))
  ⟨_, _, _, _, g.1, g.2.1, get_valid g.2.2.2.1 g.2.2.2.2, g.2.2.1, f.1, f.2.1,
    find_valid f.2.2.2.1 f.2.2.2.2, f.2.2.1, hm⟩

/-- **`btree_search` meets `searchSpec`.** -/
theorem search_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm searchFunc)
    (har : HasArity fi 1 1) : TFSpecAt P host a (searchSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, -, k, ma, mt, B, t, κ, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨hf, hres, k, ma, mt, B, t, κ, hargs, hm, T, φ, hbt, hκ⟩ f vs₀
    rw [hargs, forCall_search, searchFunc_body, hrs]
    exact search_body (SCtx.ofResolved hres hm) hbt hκ fun b h1 h0 F =>
      bodyPostT_ret (search_post hm hbt ⟨h1, h0⟩)

/-- **`SearchSpec`, by tactics.** -/
theorem searchSpec_tactic : SearchSpec := fun _ _ _ _ hcode har => search_valid hcode har

end Silmaril.WasmSpec.BTree.V2
