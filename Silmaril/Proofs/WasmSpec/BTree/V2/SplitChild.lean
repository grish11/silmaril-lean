module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Search
public import Silmaril.Proofs.WasmSpec.BTree.V2.SplitRepr
public import Silmaril.Proofs.WasmSpec.BTree.V2.Arrays
public import Silmaril.Proofs.WasmSpec.BTree.V2.Split

/-!
# The B-tree library, version 2: `split_child` by tactics

`split_child(x, i, z)` runs straight-line code with calls of `oba_get`, `ba_copy` and
`ba_insert` and one `if`; the memory after each write agrees with the previous one outside
the written cells (`Agree`), so every fact about the three pages it writes (the node `x`, its
full child `y`, the new node `z`) is carried to the end, where `split_repr` assembles the split
tree. Every-run total correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A small natural number as an `i32`. -/
theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- The address of offset `c` of page `n`, as an `i32` computed from `v = n`. -/
theorem addr_of {v : BitVec 32} {n : Nat} (hv : v.toNat = n) (hn : n < 32768) (c : Nat)
    (hc : c < 65536) : (v * 65536#32 + BitVec.ofNat 32 c).toNat = page * n + c := by
  subst hv
  exact page_addr hn c hc

/-- The address of page `n`, as an `i32` computed from `v = n`. -/
theorem addr0_of {v : BitVec 32} {n : Nat} (hv : v.toNat = n) (hn : n < 32768) :
    (v * 65536#32).toNat = page * n := by
  subst hv
  exact page_addr0 hn

/-- The callees of `split_child`: `oba_get` (index 0), `ba_insert` (3), `ba_copy` (4). -/
structure XCtx (P : Profile) (host : HostSemantics H) (s : Store H) (mi : ModuleInst) : Type where
  aG : Nat
  fiG : FuncInst H
  hG : mi.funcs[0]? = some aG
  hfG : s.funcs[aG]? = some fiG
  hGS : TFSpecAt P host aG (getSpec aG fiG)
  hmG : fiG.module = mi
  aI : Nat
  fiI : FuncInst H
  hI : mi.funcs[3]? = some aI
  hfI : s.funcs[aI]? = some fiI
  hIS : TFSpecAt P host aI (baInsertSpec aI fiI)
  hmI : fiI.module = mi
  aC : Nat
  fiC : FuncInst H
  hC : mi.funcs[4]? = some aC
  hfC : s.funcs[aC]? = some fiC
  hCS : TFSpecAt P host aC (baCopySpec aC fiC)
  hmC : fiC.module = mi

/-- **The data of a split**: the inner node `x` (keys `kx`, children `cs`) in memory `B`,
ordered, distinct, its pages valid, with room for a key; its child `i` at page `y`, full;
the free page `z`; the branching factor `t` at `0`. -/
structure SData (B : ByteArray) (t x i z y : Nat) (ly : Bool) (kx ky : List (BitVec 32))
    (cs cy : List Tree) : Prop where
  ht : 2 ≤ t
  ht' : t ≤ 4045
  h0 : wd B 0 = BitVec.ofNat 32 t
  hR : Repr B (.node x false kx cs)
  hd : Distinct (.node x false kx cs)
  hpg : ∀ p, Owns p (.node x false kx cs) → PageOK B p
  hzok : PageOK B z
  hz : ¬ Owns z (.node x false kx cs)
  hkx : kx.length < 2 * t - 1
  hlen : cs.length = kx.length + 1
  hi : i < cs.length
  hy : cs[i] = .node y ly ky cy
  hky : ky.length = 2 * t - 1
  hcy : ly = false → cy.length = 2 * t

namespace SData

variable {B : ByteArray} {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)}
  {cs cy : List Tree}

theorem mem_y (h : SData B t x i z y ly kx ky cs cy) : Tree.node y ly ky cy ∈ cs :=
  h.hy ▸ List.getElem_mem h.hi

theorem xok (h : SData B t x i z y ly kx ky cs cy) : PageOK B x := h.hpg x .here

theorem yok (h : SData B t x i z y ly kx ky cs cy) : PageOK B y := h.hpg y (.child h.mem_y .here)

theorem x_ne_y (h : SData B t x i z y ly kx ky cs cy) : x ≠ y := fun e =>
  h.hd.root_not_child h.mem_y (e ▸ .here)

theorem x_ne_z (h : SData B t x i z y ly kx ky cs cy) : x ≠ z := fun e => h.hz (e ▸ .here)

theorem y_ne_z (h : SData B t x i z y ly kx ky cs cy) : y ≠ z := fun e =>
  h.hz (e ▸ .child h.mem_y .here)

theorem x_leaf (h : SData B t x i z y ly kx ky cs cy) : wd B (page * x) = 0 := by
  have hl := h.hR.leaf_iff.1
  by_contra hc
  exact Bool.noConfusion (hl.2 hc)

theorem x_keys (h : SData B t x i z y ly kx ky cs cy) : OBAnd B (page * x + 4) 8090 kx :=
  h.hR.leaf_iff.2.2.1

theorem x_ptrs (h : SData B t x i z y ly kx ky cs cy) :
    BA B (page * x + 32768) 8091 (cs.map Tree.ptr) :=
  h.hR.leaf_iff.2.2.2 rfl

theorem y_repr (h : SData B t x i z y ly kx ky cs cy) : Repr B (.node y ly ky cy) :=
  h.hR.child h.mem_y

theorem y_keys (h : SData B t x i z y ly kx ky cs cy) : OBAnd B (page * y + 4) 8090 ky :=
  h.y_repr.leaf_iff.2.2.1

theorem y_ptrs (h : SData B t x i z y ly kx ky cs cy) (hl : ly = false) :
    BA B (page * y + 32768) 8091 (cy.map Tree.ptr) :=
  h.y_repr.leaf_iff.2.2.2 hl

/-- Child `i`'s pointer is `y`. -/
theorem y_ptr (h : SData B t x i z y ly kx ky cs cy) :
    (cs.map Tree.ptr).getD i 0 = BitVec.ofNat 32 y := by
  have hi : i < (cs.map Tree.ptr).length := by simpa using h.hi
  rw [getD_of_lt _ hi, List.getElem_map, h.hy]
  rfl

end SData

/-- Strictly increasing keys have no duplicates. -/
theorem nodup_of_strict {ks : List (BitVec 32)} (hs : ks.Pairwise fun a b => a.toInt < b.toInt) :
    ks.Nodup :=
  hs.imp fun h e => by rw [e] at h; exact lt_irrefl _ h

/-- The end of `split_child`: shrink the child's keys, insert `z` into the node's pointers;
the memory then holds the split tree. -/
theorem split_end {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B4 B5 : ByteArray}
    {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    (c : XCtx P host s mi) (h : SData B t x i z y ly kx ky cs cy) (hm : MemAt s mi ma mt B)
    {xv iv zv : BitVec 32} (hxv : xv.toNat = x) (hiv : iv.toNat = i) (hzv : zv.toNat = z)
    (A4 : Agree B B4 fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)) ∨
      (page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091)) ∨
      (page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4))
    (A45 : Agree B4 B5 fun j => page * x + 4 ≤ j ∧ j < page * x + 4 + (4 + 4 * 8090))
    (hzl4 : wd B4 (page * z) = wd B (page * y)) (hzk4 : BA B4 (page * z + 4) 8090 (ky.drop t))
    (hzp4 : ly = false → BA B4 (page * z + 32768) 8091 ((cy.drop t).map Tree.ptr))
    (hyp4 : ly = false → BA B4 (page * y + 32768) 8091 ((cy.take t).map Tree.ptr))
    (hk5 : BA B5 (page * x + 4) 8090 (kx.insertIdx i (ky.getD (t - 1) 0)))
    (hsx : (kx.insertIdx i (ky.getD (t - 1) 0)).Pairwise fun a b => a.toInt < b.toInt)
    {Q : Post H}
    (hfin : ∀ B', B'.size = B.size → Repr B' ((Tree.node x false kx cs).splitChild t z i) →
      Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z) → ∀ F, Q (s.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host (s.setMem ma ⟨mt, B5⟩) (fr mi [xv, iv, zv, BitVec.ofNat 32 t, xv * 65536#32,
        BitVec.ofNat 32 y * 65536#32, zv * 65536#32])
      (vals [] ++ expression [lget 5, lget 3, c32 1, isub, .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
        lget 4, c32 32768, iadd, lget 1, c32 1, iadd, lget 2, call 3]) Q := by
  have hx32 : x < 32768 := h.xok.2.1
  have hy32 : y < 32768 := h.yok.2.1
  have hyv : (BitVec.ofNat 32 y).toNat = y := toNat_ofNat_lt (by omega)
  have hy0 : (BitVec.ofNat 32 y * 65536#32).toNat = page * y := addr0_of hyv hy32
  have hxp : (xv * 65536#32 + 32768#32).toNat = page * x + 32768 := addr_of hxv hx32 32768 (by omega)
  have htm : (BitVec.ofNat 32 t - 1#32).toNat = t - 1 := by have := h.ht; have := h.ht'; bv_omega
  have hxne := h.x_ne_y
  have hxz := h.x_ne_z
  have hyz := h.y_ne_z
  have hysz : page * (y + 1) ≤ B.size := h.yok.2.2
  have hsz5 : B5.size = B.size := A45.1.trans A4.1
  have hm5 : MemAt (s.setMem ma ⟨mt, B5⟩) mi ma mt B5 := hm.setMem B5
  have hb6 : (BitVec.ofNat 32 y * 65536#32).toNat + 4 + 4 ≤ B5.size := by
    rw [hy0, hsz5]; simp only [page] at *; omega
  have ha6 : (BitVec.ofNat 32 y * 65536#32).toNat + ((4 : Fin (2 ^ 64)) : Nat) = page * y + 4 := by
    rw [hy0]; rfl
  have htv : BitVec.ofNat 32 t - 1#32 = BitVec.ofNat 32 (t - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [htm, toNat_ofNat_lt (by have := h.ht'; omega)]
  have hky5 : BA B5 (page * y + 4) 8090 ky := h.y_keys.1.1.agree (A4.trans A45) (by
    intro j h1 h2 hr; simp only [page] at *; omega)
  have hcs5 : BA B5 (page * x + 32768) 8091 (cs.map Tree.ptr) := h.x_ptrs.agree (A4.trans A45) (by
    intro j h1 h2 hr; simp only [page] at *; omega)
  have hyk6 : BA (wr B5 (page * y + 4) (BitVec.ofNat 32 (t - 1))) (page * y + 4) 8090 (ky.take (t - 1)) :=
    hky5.truncate (by rw [h.hky]; omega)
  have A56 : Agree B5 (wr B5 (page * y + 4) (BitVec.ofNat 32 (t - 1))) fun j =>
      page * y + 4 ≤ j ∧ j < page * y + 4 + 4 :=
    SameOutside.agree (sameOutside_wr _ (by simp only [page] at *; omega) (le_refl _) (le_refl _))
  generalize hB6 : wr B5 (page * y + 4) (BitVec.ofNat 32 (t - 1)) = B6 at hyk6 A56
  wbegin
  wrun
  rw [ha6, htv, hB6, setMem_setMem]
  have hm6 : MemAt (s.setMem ma ⟨mt, B6⟩) c.fiI.module ma mt B6 := by rw [c.hmI]; exact hm.setMem B6
  have hcs6 : BA B6 (xv * 65536#32 + 32768#32).toNat 8091 (cs.map Tree.ptr) := by
    rw [hxp]
    exact hcs5.agree A56 (by intro j h1 h2 hr; simp only [page] at *; omega)
  have hi1 : (iv + 1#32).toNat = i + 1 := by have := h.hi; have := h.hlen; have := h.hkx; have := h.ht'; bv_omega
  have hile : (iv + 1#32).toNat ≤ (cs.map Tree.ptr).length := by
    rw [hi1]; have := h.hi; simp only [List.length_map]; omega
  have hilt : (cs.map Tree.ptr).length < 8091 := by
    have := h.hlen; have := h.hkx; have := h.ht'; simp; omega
  refine t_call (rs := []) (args := [.i32 (xv * 65536#32 + 32768#32), .i32 (iv + 1#32), .i32 zv])
    (by simpa [Idx.toNat] using c.hI) c.hfI c.hIS ⟨c.hfI, _, _, _, ma, mt, B6, 8091, _, rfl, hm6, hcs6, hile, hilt⟩
    fun s' o hp => ?_
  obtain ⟨ho, B7, hs7, hp7, hso7⟩ := hp _ _ _ ma mt B6 8091 _ rfl hm6 hcs6 hile hilt
  refine ⟨ho, ?_⟩
  rw [hs7, setMem_setMem]
  have A67 : Agree B6 B7 fun j => page * x + 32768 ≤ j ∧ j < page * x + 32768 + (4 + 4 * 8091) := by
    have := SameOutside.agree hso7; rwa [hxp] at this
  have A47 := (A45.trans A56).trans A67
  have A07 := A4.trans A47
  have hzv' : zv = BitVec.ofNat 32 z := by
    apply BitVec.eq_of_toNat_eq; rw [hzv, toNat_ofNat_lt (by have := h.hzok.2.1; omega)]
  have hxp7 : BA B7 (page * x + 32768) 8091 ((cs.map Tree.ptr).insertIdx (i + 1) (BitVec.ofNat 32 z)) := by
    rw [hxp, hi1, hzv'] at hp7; exact hp7
  have hxk7 : OBAnd B7 (page * x + 4) 8090 (kx.insertIdx i (ky.getD (t - 1) 0)) :=
    ⟨⟨hk5.agree (A56.trans A67) (by intro j h1 h2 hr; simp only [page] at *; omega),
      sortedS_of_strict hsx⟩, nodup_of_strict hsx⟩
  have hyk7 : OBAnd B7 (page * y + 4) 8090 (ky.take (t - 1)) := h.y_keys.of_sublist (List.take_sublist _ _)
    (hyk6.agree A67 (by intro j h1 h2 hr; simp only [page] at *; omega))
  have hzk7 : OBAnd B7 (page * z + 4) 8090 (ky.drop t) := h.y_keys.of_sublist (List.drop_sublist _ _)
    (hzk4.agree A47 (by intro j h1 h2 hr; simp only [page] at *; omega))
  have hU : Unchanged B B7 fun p => p = x ∨ p = y ∨ p = z :=
    A07.unchanged (by intro j hr; simp only [page] at *; omega)
  have hR7 := split_repr h.hR h.hd h.hpg h.hz h.hi h.hy hU
    ((A07.wd_eq (by intro j h1 h2 hr; simp only [page] at *; omega)).trans h.x_leaf) hxk7 hxp7
    (A07.wd_eq (by intro j h1 h2 hr; simp only [page] at *; omega)) hyk7
    (fun hl => (hyp4 hl).agree A47 (by intro j h1 h2 hr; simp only [page] at *; omega))
    ((A47.wd_eq (by intro j h1 h2 hr; simp only [page] at *; omega)).trans hzl4) hzk7
    (fun hl => (hzp4 hl).agree A47 (by intro j h1 h2 hr; simp only [page] at *; omega))
  exact w_end (m := .total) (rs := []) (hfin B7 A07.1 hR7 hU _)
/-- After the `if` of `split_child`: insert the median into the node's keys, then
`split_end`. -/
theorem split_mid {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B4 : ByteArray}
    {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    (c : XCtx P host s mi) (h : SData B t x i z y ly kx ky cs cy) (hm : MemAt s mi ma mt B)
    {xv iv zv : BitVec 32} (hxv : xv.toNat = x) (hiv : iv.toNat = i) (hzv : zv.toNat = z)
    (A4 : Agree B B4 fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)) ∨
      (page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091)) ∨
      (page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4))
    (hzl4 : wd B4 (page * z) = wd B (page * y)) (hzk4 : BA B4 (page * z + 4) 8090 (ky.drop t))
    (hzp4 : ly = false → BA B4 (page * z + 32768) 8091 ((cy.drop t).map Tree.ptr))
    (hyp4 : ly = false → BA B4 (page * y + 32768) 8091 ((cy.take t).map Tree.ptr))
    (hsx : (kx.insertIdx i (ky.getD (t - 1) 0)).Pairwise fun a b => a.toInt < b.toInt)
    {Q : Post H}
    (hfin : ∀ B', B'.size = B.size → Repr B' ((Tree.node x false kx cs).splitChild t z i) →
      Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z) → ∀ F, Q (s.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host (s.setMem ma ⟨mt, B4⟩) (fr mi [xv, iv, zv, BitVec.ofNat 32 t, xv * 65536#32,
        BitVec.ofNat 32 y * 65536#32, zv * 65536#32])
      (vals [] ++ expression [lget 4, c32 4, iadd, lget 1, lget 5, c32 4, iadd, lget 3, c32 1, isub,
        call 0, call 3, lget 5, lget 3, c32 1, isub, .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
        lget 4, c32 32768, iadd, lget 1, c32 1, iadd, lget 2, call 3]) Q := by
  have hx32 : x < 32768 := h.xok.2.1
  have hy32 : y < 32768 := h.yok.2.1
  have hyv : (BitVec.ofNat 32 y).toNat = y := toNat_ofNat_lt (by omega)
  have htv : (BitVec.ofNat 32 t).toNat = t := toNat_ofNat_lt (by have := h.ht'; omega)
  have hxa : (xv * 65536#32 + 4#32).toNat = page * x + 4 := addr_of hxv hx32 4 (by omega)
  have hya : (BitVec.ofNat 32 y * 65536#32 + 4#32).toNat = page * y + 4 := addr_of hyv hy32 4 (by omega)
  have hm4 : MemAt (s.setMem ma ⟨mt, B4⟩) mi ma mt B4 := hm.setMem B4
  have hxne := h.x_ne_y
  have hxz := h.x_ne_z
  have hyz := h.y_ne_z
  have hky4 : BA B4 (page * y + 4) 8090 ky := h.y_keys.1.1.agree A4 (by
    intro j h1 h2 hr; simp only [page] at *; omega)
  have hkx4 : BA B4 (page * x + 4) 8090 kx := h.x_keys.1.1.agree A4 (by
    intro j h1 h2 hr; simp only [page] at *; omega)
  have htm : (BitVec.ofNat 32 t - 1#32).toNat = t - 1 := by have := h.ht; bv_omega
  have hmed : (BitVec.ofNat 32 t - 1#32).toNat < ky.length := by rw [htm, h.hky]; have := h.ht; omega
  have hmG : MemAt (s.setMem ma ⟨mt, B4⟩) c.fiG.module ma mt B4 := by rw [c.hmG]; exact hm4
  have hgA : BA B4 (BitVec.ofNat 32 y * 65536#32 + 4#32).toNat 8090 ky := by rw [hya]; exact hky4
  wbegin
  wrun
  refine t_call1 (rs := [.i32 iv, .i32 (xv * 65536#32 + 4#32)])
    (args := [.i32 (BitVec.ofNat 32 y * 65536#32 + 4#32), .i32 (BitVec.ofNat 32 t - 1#32)])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt, B4, 8090, ky, rfl, hmG, hgA, hmed⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt B4 8090 ky rfl (hp.1 ▸ hmG) hgA hmed, ?_⟩
  rw [hp.1, htm]
  have hmI : MemAt (s.setMem ma ⟨mt, B4⟩) c.fiI.module ma mt B4 := by rw [c.hmI]; exact hm4
  have hkxA : BA B4 (xv * 65536#32 + 4#32).toNat 8090 kx := by rw [hxa]; exact hkx4
  have hile : iv.toNat ≤ kx.length := by have := h.hi; have := h.hlen; omega
  have hklt : kx.length < 8090 := by have := h.hkx; have := h.ht'; omega
  refine t_call (rs := []) (args := [.i32 (xv * 65536#32 + 4#32), .i32 iv, .i32 (ky.getD (t - 1) 0)])
    (by simpa [Idx.toNat] using c.hI) c.hfI c.hIS ⟨c.hfI, _, _, _, ma, mt, B4, 8090, kx, rfl, hmI, hkxA, hile, hklt⟩
    fun s' o hp => ?_
  obtain ⟨ho, B5, hs5, hk5, hso5⟩ := hp _ _ _ ma mt B4 8090 kx rfl hmI hkxA hile hklt
  refine ⟨ho, ?_⟩
  rw [hs5, setMem_setMem]
  have A45 : Agree B4 B5 fun j => page * x + 4 ≤ j ∧ j < page * x + 4 + (4 + 4 * 8090) := by
    have := SameOutside.agree hso5; rwa [hxa] at this
  rw [hxa, hiv] at hk5
  exact split_end c h hm hxv hiv hzv A4 A45 hzl4 hzk4 hzp4 hyp4 hk5 hsx hfin
/-- The inner case of `split_child`'s `if`: copy the child's last `t` pointers to `z`, then
shrink the child's pointers to `t`. -/
theorem split_inner {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B2 : ByteArray}
    {t x i z y : Nat} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    (c : XCtx P host s mi) (h : SData B t x i z y false kx ky cs cy) (hm : MemAt s mi ma mt B)
    {xv iv zv : BitVec 32} (hzv : zv.toNat = z)
    (A2 : Agree B B2 fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)))
    {rest : List Admin} {Q : Post H}
    (hk : ∀ B4, Agree B B4 (fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)) ∨
      (page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091)) ∨
      (page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4)) →
      Agree B2 B4 (fun j => (page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091)) ∨
      (page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4)) →
      BA B4 (page * z + 32768) 8091 ((cy.drop t).map Tree.ptr) →
      BA B4 (page * y + 32768) 8091 ((cy.take t).map Tree.ptr) →
      TWP P host (s.setMem ma ⟨mt, B4⟩) (fr mi [xv, iv, zv, BitVec.ofNat 32 t, xv * 65536#32,
        BitVec.ofNat 32 y * 65536#32, zv * 65536#32]) (vals ([] : List Val).reverse ++ rest) Q) :
    TWP P host (s.setMem ma ⟨mt, B2⟩) (fr mi [xv, iv, zv, BitVec.ofNat 32 t, xv * 65536#32,
        BitVec.ofNat 32 y * 65536#32, zv * 65536#32])
      (vals [] ++ expression [lget 5, c32 32772, iadd, lget 3, c32 4, imul, iadd, lget 6, c32 32768,
        iadd, lget 3, call 4, lget 5, lget 3, .intStore .i32 none ⟨0⟩ ⟨2, 32768⟩])
      (armPostT P host [] rest Q) := by
  have hz32 : z < 32768 := h.hzok.2.1
  have hy32 : y < 32768 := h.yok.2.1
  have hyv : (BitVec.ofNat 32 y).toNat = y := toNat_ofNat_lt (by omega)
  have htv : (BitVec.ofNat 32 t).toNat = t := toNat_ofNat_lt (by have := h.ht'; omega)
  have hsrc : (BitVec.ofNat 32 y * 65536#32 + 32772#32 + BitVec.ofNat 32 t * 4#32).toNat =
      page * y + 32772 + 4 * t := by
    have := h.ht'; simp only [page]; bv_omega
  have hdst : (zv * 65536#32 + 32768#32).toNat = page * z + 32768 := addr_of hzv hz32 32768 (by omega)
  have hsz2 : B2.size = B.size := A2.1
  have hysz : page * (y + 1) ≤ B.size := h.yok.2.2
  have hzsz : page * (z + 1) ≤ B.size := h.hzok.2.2
  have hxne := h.x_ne_y
  have hyz := h.y_ne_z
  have ht' := h.ht'
  have hcy : cy.length = 2 * t := h.hcy rfl
  have hmC : MemAt (s.setMem ma ⟨mt, B2⟩) c.fiC.module ma mt B2 := by rw [c.hmC]; exact hm.setMem B2
  have b1 : (BitVec.ofNat 32 t).toNat ≤ 8091 := by rw [htv]; omega
  have b2 : (BitVec.ofNat 32 y * 65536#32 + 32772#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t).toNat ≤ B2.size := by
    rw [hsrc, htv, hsz2]; simp only [page] at *; omega
  have b3 : (BitVec.ofNat 32 y * 65536#32 + 32772#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t).toNat ≤ int32Max := by
    rw [hsrc, htv]; simp only [page, int32Max] at *; omega
  have b4 : (zv * 65536#32 + 32768#32).toNat + 4 + 4 * 8091 ≤ B2.size := by
    rw [hdst, hsz2]; simp only [page] at *; omega
  have b5 : (zv * 65536#32 + 32768#32).toNat + 4 + 4 * 8091 ≤ int32Max := by
    rw [hdst]; simp only [page, int32Max] at *; omega
  have b6 : (BitVec.ofNat 32 y * 65536#32 + 32772#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t).toNat ≤ (zv * 65536#32 + 32768#32).toNat ∨
      (zv * 65536#32 + 32768#32).toNat + 4 + 4 * 8091 ≤
        (BitVec.ofNat 32 y * 65536#32 + 32772#32 + BitVec.ofNat 32 t * 4#32).toNat := by
    rw [hsrc, htv, hdst]; simp only [page] at *; omega
  wbegin
  wrun
  refine t_call (rs := []) (args := [.i32 (BitVec.ofNat 32 y * 65536#32 + 32772#32 +
      BitVec.ofNat 32 t * 4#32), .i32 (zv * 65536#32 + 32768#32), .i32 (BitVec.ofNat 32 t)])
    (by simpa [Idx.toNat] using c.hC) c.hfC c.hCS
    ⟨c.hfC, _, _, _, ma, mt, B2, 8091, rfl, hmC, b1, b2, b3, b4, b5, b6⟩ fun s' o hp => ?_
  obtain ⟨ho, B3, hs3, hc3, hso3⟩ := hp _ _ _ ma mt B2 8091 rfl hmC b1 b2 b3 b4 b5 b6
  refine ⟨ho, ?_⟩
  rw [hs3, setMem_setMem]
  rw [hsrc, htv, hdst] at hc3
  have A23 : Agree B2 B3 fun j => page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091) := by
    have := SameOutside.agree hso3; rwa [hdst] at this
  have hyp : BA B (page * y + 32768) 8091 (cy.map Tree.ptr) := h.y_ptrs rfl
  have hcw : words B2 (page * y + 32772 + 4 * t) t = (cy.drop t).map Tree.ptr := by
    have hw : words B (page * y + 32768 + 4) (2 * t) = cy.map Tree.ptr := by
      have := hyp.2.1; rwa [List.length_map, hcy] at this
    rw [A2.words_eq (by intro j h1 h2 hr; simp only [page] at *; omega), List.map_drop, ← hw,
      words_drop (by omega), show 2 * t - t = t by omega]
  rw [hcw] at hc3
  have hy3 : BA B3 (page * y + 32768) 8091 (cy.map Tree.ptr) :=
    hyp.agree (A2.trans A23) (by intro j h1 h2 hr; simp only [page] at *; omega)
  have hyp4 : BA (wr B3 (page * y + 32768) (BitVec.ofNat 32 t)) (page * y + 32768) 8091
      ((cy.take t).map Tree.ptr) := by
    rw [List.map_take]; exact hy3.truncate (by simp; omega)
  have A34 : Agree B3 (wr B3 (page * y + 32768) (BitVec.ofNat 32 t)) fun j =>
      page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4 :=
    SameOutside.agree (sameOutside_wr _ (by have := hy3.2.2.2.2; omega) (le_refl _) (le_refl _))
  have hzp4 := hc3.agree A34 (by intro j h1 h2 hr; simp only [page] at *; omega)
  wstep; wnorm
  wstep; wnorm
  have ha4 : effAddr (BitVec.ofNat 32 y * 65536#32).toNat ⟨2, 32768⟩ = page * y + 32768 := by
    rw [effAddr, addr0_of hyv hy32]; rfl
  have hb : effAddr (BitVec.ofNat 32 y * 65536#32).toNat ⟨2, 32768⟩ + 4 ≤ B3.size := by
    rw [ha4, hso3.1, hsz2]; simp only [page] at *; omega
  refine w_store (m := .total) (hm.setMem B3) hb fun _ _ => ?_
  rw [ha4, setMem_setMem]
  generalize wr B3 (page * y + 32768) (BitVec.ofNat 32 t) = B4 at hyp4 A34 hzp4 ⊢
  exact t_armEnd (hk B4 ((A2.trans (A23.trans A34)).mono fun j hj => by omega)
    (A23.trans A34) hzp4 hyp4)
/-- The suffix of `split_child` after the copy of the keys. -/
abbrev splitSuffix : List Instr := [lget 4, c32 4, iadd, lget 1, lget 5, c32 4, iadd, lget 3, c32 1,
  isub, call 0, call 3, lget 5, lget 3, c32 1, isub, .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
  lget 4, c32 32768, iadd, lget 1, c32 1, iadd, lget 2, call 3]

/-- The `if` of `split_child` (copy the pointers when the child is inner), then the suffix. -/
theorem split_if {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B2 : ByteArray}
    {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    (c : XCtx P host s mi) (h : SData B t x i z y ly kx ky cs cy) (hm : MemAt s mi ma mt B)
    {xv iv zv : BitVec 32} (hxv : xv.toNat = x) (hiv : iv.toNat = i) (hzv : zv.toNat = z)
    (A2 : Agree B B2 fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)))
    (hzl2 : wd B2 (page * z) = wd B (page * y)) (hzk2 : BA B2 (page * z + 4) 8090 (ky.drop t))
    (hsx : (kx.insertIdx i (ky.getD (t - 1) 0)).Pairwise fun a b => a.toInt < b.toInt)
    {Q : Post H}
    (hfin : ∀ B', B'.size = B.size → Repr B' ((Tree.node x false kx cs).splitChild t z i) →
      Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z) → ∀ F, Q (s.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host (s.setMem ma ⟨mt, B2⟩) (fr mi [xv, iv, zv, BitVec.ofNat 32 t, xv * 65536#32,
        BitVec.ofNat 32 y * 65536#32, zv * 65536#32])
      (vals [] ++ expression ([lget 5, iload, ieqz, .if_ .empty [lget 5, c32 32772, iadd, lget 3,
        c32 4, imul, iadd, lget 6, c32 32768, iadd, lget 3, call 4, lget 5, lget 3,
        .intStore .i32 none ⟨0⟩ ⟨2, 32768⟩] []] ++ splitSuffix)) Q := by
  have hy32 : y < 32768 := h.yok.2.1
  have hy0 : (BitVec.ofNat 32 y * 65536#32).toNat = page * y := addr0_of (toNat_ofNat_lt (by omega)) hy32
  have hb : (BitVec.ofNat 32 y * 65536#32).toNat + 4 ≤ B2.size := by
    rw [hy0, A2.1]; have := h.yok.2.2; simp only [page] at *; omega
  have hyl2 : wd B2 (page * y) = wd B (page * y) := A2.wd_eq (by
    have := h.y_ne_z; intro j h1 h2 hr; simp only [page] at *; omega)
  have hm2 : MemAt (s.setMem ma ⟨mt, B2⟩) mi ma mt B2 := hm.setMem B2
  have hl := h.y_repr.leaf_iff.1
  have A4 := A2.mono (R' := fun j => (page * z ≤ j ∧ j < page * z + 4) ∨
      (page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090)) ∨
      (page * z + 32768 ≤ j ∧ j < page * z + 32768 + (4 + 4 * 8091)) ∨
      (page * y + 32768 ≤ j ∧ j < page * y + 32768 + 4)) fun j hj => by omega
  wbegin
  wrun
  rw [hy0, hyl2]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · show TWP P host _ _ _ (armPostT P host [] _ Q)
    obtain rfl : ly = false := by
      cases ly
      · rfl
      · exact absurd (by simpa using hc) (hl.1 rfl)
    refine split_inner c h hm hzv A2 fun B4 A4' A24 hzp4 hyp4 => ?_
    have hyz : y ≠ z := h.y_ne_z
    have hzl4 : wd B4 (page * z) = wd B (page * y) :=
      (A24.wd_eq (by intro j h1 h2 hr; simp only [page] at *; omega)).trans hzl2
    have hzk4 : BA B4 (page * z + 4) 8090 (ky.drop t) :=
      hzk2.agree A24 (by intro j h1 h2 hr; simp only [page] at *; omega)
    exact split_mid c h hm hxv hiv hzv A4' hzl4 hzk4 (fun _ => hzp4) (fun _ => hyp4) hsx hfin
  · have hly : ly = true := hl.2 (by simpa using hc)
    exact t_armEnd (split_mid c h hm hxv hiv hzv A4 hzl2 hzk2 (fun e => Bool.noConfusion (hly ▸ e))
      (fun e => Bool.noConfusion (hly ▸ e)) hsx hfin)

/-- **The body of `split_child`**: read `t`, the child's page `y`, copy the leaf indicator and
the last `t - 1` keys to `z`, then `split_if`. -/
theorem split_body {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)} {cs cy : List Tree}
    (c : XCtx P host s mi) (h : SData B t x i z y ly kx ky cs cy) (hm : MemAt s mi ma mt B)
    {xv iv zv : BitVec 32} (hxv : xv.toNat = x) (hiv : iv.toNat = i) (hzv : zv.toNat = z)
    (hsx : (kx.insertIdx i (ky.getD (t - 1) 0)).Pairwise fun a b => a.toInt < b.toInt)
    {Q : Post H}
    (hfin : ∀ B', B'.size = B.size → Repr B' ((Tree.node x false kx cs).splitChild t z i) →
      Unchanged B B' (fun p => p = x ∨ p = y ∨ p = z) → ∀ F, Q (s.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host s (fr mi [xv, iv, zv, 0, 0, 0, 0])
      (vals [] ++ expression ([c32 0, iload, lset 3, lget 0, c32 65536, imul, lset 4, lget 4,
        c32 32768, iadd, lget 1, call 0, c32 65536, imul, lset 5, lget 2, c32 65536, imul, lset 6,
        lget 6, lget 5, iload, istore, lget 5, c32 8, iadd, lget 3, c32 4, imul, iadd, lget 6,
        c32 4, iadd, lget 3, c32 1, isub, call 4] ++ [lget 5, iload, ieqz, .if_ .empty [lget 5,
        c32 32772, iadd, lget 3, c32 4, imul, iadd, lget 6, c32 32768, iadd, lget 3, call 4,
        lget 5, lget 3, .intStore .i32 none ⟨0⟩ ⟨2, 32768⟩] []] ++ splitSuffix)) Q := by
  have hx32 : x < 32768 := h.xok.2.1
  have hy32 : y < 32768 := h.yok.2.1
  have hz32 : z < 32768 := h.hzok.2.1
  have hxsz : page * (x + 1) ≤ B.size := h.xok.2.2
  have hxp : (xv * 65536#32 + 32768#32).toNat = page * x + 32768 := addr_of hxv hx32 32768 (by omega)
  have hmG : MemAt s c.fiG.module ma mt B := by rw [c.hmG]; exact hm
  have hgA : BA B (xv * 65536#32 + 32768#32).toNat 8091 (cs.map Tree.ptr) := by rw [hxp]; exact h.x_ptrs
  have hgi : iv.toNat < (cs.map Tree.ptr).length := by rw [hiv]; simpa using h.hi
  have h4 : 4 + 4 ≤ B.size := by simp only [page] at *; omega
  wbegin
  wrun
  rw [show (0#32 : BitVec 32).toNat = 0 from rfl, h.h0]
  refine t_call1 (rs := []) (args := [.i32 (xv * 65536#32 + 32768#32), .i32 iv])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt, B, 8091, _, rfl, hmG, hgA, hgi⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt B 8091 _ rfl (hp.1 ▸ hmG) hgA hgi, ?_⟩
  rw [hp.1, hiv, h.y_ptr]
  have hyv : (BitVec.ofNat 32 y).toNat = y := toNat_ofNat_lt (by omega)
  have hy0 : (BitVec.ofNat 32 y * 65536#32).toNat = 65536 * y := addr0_of hyv hy32
  have hz0 : (zv * 65536#32).toNat = 65536 * z := addr0_of hzv hz32
  have hysz : 65536 * (y + 1) ≤ B.size := h.yok.2.2
  have hzsz : 65536 * (z + 1) ≤ B.size := h.hzok.2.2
  wrun
  rw [hy0, hz0]
  have hyz : y ≠ z := h.y_ne_z
  have ht := h.ht
  have ht' := h.ht'
  have A01 : Agree B (wr B (65536 * z) (wd B (65536 * y))) fun j =>
      page * z ≤ j ∧ j < page * z + 4 :=
    SameOutside.agree (sameOutside_wr _ (by omega) (le_refl _) (le_refl _))
  have hky : BA B (page * y + 4) 8090 ky := h.y_keys.1.1
  have hz1 : wd (wr B (65536 * z) (wd B (65536 * y))) (65536 * z) = wd B (65536 * y) :=
    wd_wr_same _ (by omega)
  generalize wr B (65536 * z) (wd B (65536 * y)) = B1 at A01 hz1 ⊢
  have hsrc : (BitVec.ofNat 32 y * 65536#32 + 8#32 + BitVec.ofNat 32 t * 4#32).toNat =
      65536 * y + 8 + 4 * t := by bv_omega
  have hdst : (zv * 65536#32 + 4#32).toNat = 65536 * z + 4 := addr_of hzv hz32 4 (by omega)
  have hn : (BitVec.ofNat 32 t - 1#32).toNat = t - 1 := by bv_omega
  have hsz1 : B1.size = B.size := A01.1
  have b1 : (BitVec.ofNat 32 t - 1#32).toNat ≤ 8090 := by omega
  have b2 : (BitVec.ofNat 32 y * 65536#32 + 8#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t - 1#32).toNat ≤ B1.size := by omega
  have b3 : (BitVec.ofNat 32 y * 65536#32 + 8#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t - 1#32).toNat ≤ int32Max := by simp only [int32Max]; omega
  have b4 : (zv * 65536#32 + 4#32).toNat + 4 + 4 * 8090 ≤ B1.size := by omega
  have b5 : (zv * 65536#32 + 4#32).toNat + 4 + 4 * 8090 ≤ int32Max := by simp only [int32Max]; omega
  have b6 : (BitVec.ofNat 32 y * 65536#32 + 8#32 + BitVec.ofNat 32 t * 4#32).toNat +
      4 * (BitVec.ofNat 32 t - 1#32).toNat ≤ (zv * 65536#32 + 4#32).toNat ∨
      (zv * 65536#32 + 4#32).toNat + 4 + 4 * 8090 ≤
        (BitVec.ofNat 32 y * 65536#32 + 8#32 + BitVec.ofNat 32 t * 4#32).toNat := by omega
  have hmC : MemAt (s.setMem ma ⟨mt, B1⟩) c.fiC.module ma mt B1 := by rw [c.hmC]; exact hm.setMem B1
  refine t_call (rs := []) (args := [.i32 (BitVec.ofNat 32 y * 65536#32 + 8#32 +
      BitVec.ofNat 32 t * 4#32), .i32 (zv * 65536#32 + 4#32), .i32 (BitVec.ofNat 32 t - 1#32)])
    (by simpa [Idx.toNat] using c.hC) c.hfC c.hCS
    ⟨c.hfC, _, _, _, ma, mt, B1, 8090, rfl, hmC, b1, b2, b3, b4, b5, b6⟩ fun s' o hp => ?_
  obtain ⟨ho, B2, hs2, hc2, hso2⟩ := hp _ _ _ ma mt B1 8090 rfl hmC b1 b2 b3 b4 b5 b6
  refine ⟨ho, ?_⟩
  rw [hs2, setMem_setMem]
  rw [hsrc, hn, hdst] at hc2
  have A12 : Agree B1 B2 fun j => page * z + 4 ≤ j ∧ j < page * z + 4 + (4 + 4 * 8090) := by
    have := SameOutside.agree hso2; rwa [hdst] at this
  have hcw : words B1 (65536 * y + 8 + 4 * t) (t - 1) = ky.drop t := by
    have hw : words B (page * y + 4 + 4) (2 * t - 1) = ky := by
      have := hky.2.1; rwa [h.hky] at this
    rw [A01.words_eq (by intro j h1 h2 hr; simp only [page] at *; omega), ← hw,
      words_drop (by omega), show 2 * t - 1 - t = t - 1 by omega]
  rw [hcw] at hc2
  have hzl2 : wd B2 (page * z) = wd B (page * y) :=
    (A12.wd_eq (by intro j h1 h2 hr; simp only [page] at *; omega)).trans hz1
  exact split_if c h hm hxv hiv hzv (A01.trans A12) hzl2 hc2 hsx hfin
theorem splitFunc_body : splitFunc.body = [c32 0, iload, lset 3, lget 0, c32 65536, imul, lset 4,
    lget 4, c32 32768, iadd, lget 1, call 0, c32 65536, imul, lset 5, lget 2, c32 65536, imul,
    lset 6, lget 6, lget 5, iload, istore, lget 5, c32 8, iadd, lget 3, c32 4, imul, iadd, lget 6,
    c32 4, iadd, lget 3, c32 1, isub, call 4] ++ [lget 5, iload, ieqz, .if_ .empty [lget 5,
    c32 32772, iadd, lget 3, c32 4, imul, iadd, lget 6, c32 32768, iadd, lget 3, call 4,
    lget 5, lget 3, .intStore .i32 none ⟨0⟩ ⟨2, 32768⟩] []] ++ splitSuffix := rfl

theorem forCall_split (mi : ModuleInst) (x i z : BitVec 32) :
    Frame.forCall mi [.i32 x, .i32 i, .i32 z] splitFunc.locals = fr mi [x, i, z, 0, 0, 0, 0] := rfl

/-- The callees of `split_child`, from `Resolved`. -/
noncomputable def XCtx.ofResolved {s : Store H} {mi : ModuleInst} (hres : Resolved s mi) :
    XCtx P host s mi :=
  let g := Classical.choose_spec (Classical.choose_spec (hres.get (j := 0) (by decide)))
  let n := Classical.choose_spec (Classical.choose_spec (hres.get (j := 3) (by decide)))
  let c := Classical.choose_spec (Classical.choose_spec (hres.get (j := 4) (by decide)))
  ⟨_, _, g.1, g.2.1, get_valid g.2.2.2.1 g.2.2.2.2, g.2.2.1, _, _, n.1, n.2.1,
    baInsert_valid n.2.2.2.1 n.2.2.2.2, n.2.2.1, _, _, c.1, c.2.1, baCopy_valid c.2.2.2.1 c.2.2.2.2,
    c.2.2.1⟩

/-- The data of a split from its precondition. -/
theorem SData.ofPre {B : ByteArray} {t i z : Nat} {X : Tree} (h : SplitPre B t X i z) :
    ∃ (x y : Nat) (ly : Bool) (kx ky : List (BitVec 32)) (cs cy : List Tree),
      X = .node x false kx cs ∧ SData B t x i z y ly kx ky cs cy ∧
      ∃ lo hi, Ordered lo hi (.node x false kx cs) := by
  obtain ⟨ht, ht', h0, hl, hR, hd, ⟨lo, hhi, ho⟩, hpg, hzok, hz, hkx, hlen, c, hc, hck, hcl⟩ := h
  obtain ⟨x, l, kx, cs⟩ := X
  obtain ⟨y, ly, ky, cy⟩ := c
  obtain rfl : l = false := hl
  have hi : i < cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hy : cs[i] = .node y ly ky cy := (List.getElem?_eq_some_iff.1 hc).2
  exact ⟨x, y, ly, kx, ky, cs, cy, rfl, ⟨ht, ht', h0, hR, hd, hpg, hzok, hz, hkx, hlen, hi, hy, hck,
    hcl⟩, lo, hhi, ho⟩

/-- The keys of the split node are strictly increasing. -/
theorem SData.sorted {B : ByteArray} {t x i z y : Nat} {ly : Bool} {kx ky : List (BitVec 32)}
    {cs cy : List Tree} (h : SData B t x i z y ly kx ky cs cy) {lo hi : Option (BitVec 32)}
    (ho : Ordered lo hi (.node x false kx cs)) :
    (kx.insertIdx i (ky.getD (t - 1) 0)).Pairwise fun a b => a.toInt < b.toInt := by
  have hs := (splitChild_ordered (z := z) (by have := h.ht; omega) h.hi h.hy h.hky ho)
  rw [splitChild_eq h.hi h.hy] at hs
  exact hs.keys.1

/-- The postcondition of `split_child`: the tree and the bounds are determined by the
memory. -/
theorem split_post {a : Nat} {fi : FuncInst H} {s : Store H} {xv iv zv : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B' : ByteArray} {t : Nat} {X : Tree} (hm : MemAt s fi.module ma mt B)
    (hx : X.page = xv.toNat) (hpre : SplitPre B t X iv.toNat zv.toNat) (hsz : B'.size = B.size)
    (hR : Repr B' (X.splitChild t zv.toNat iv.toNat))
    (hU : Unchanged B B' (fun p => p = xv.toNat ∨ p = (X.children.getD iv.toNat X).page ∨
      p = zv.toNat)) :
    (splitSpec a fi).post s [.i32 xv, .i32 iv, .i32 zv] (s.setMem ma ⟨mt, B'⟩) (.normal []) := by
  intro xv' iv' zv' ma' mt' B'' t' X' hargs hm' hx' hpre'
  obtain ⟨rfl, rfl, rfl⟩ := args3_inj hargs
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  have hX : X' = X := Repr.unique hpre'.2.2.2.2.1 hpre.2.2.2.2.1 (hx'.trans hx.symm)
    (fun p hp => by have := (hpre'.2.2.2.2.2.2.2.1 p hp).2.1; omega)
    (fun p hp => by have := (hpre.2.2.2.2.2.2.2.1 p hp).2.1; omega)
  subst hX
  have ht : t' = t := by
    have e := congrArg BitVec.toNat (hpre'.2.2.1.symm.trans hpre.2.2.1)
    rwa [toNat_ofNat_lt (by have := hpre'.2.1; omega), toNat_ofNat_lt (by have := hpre.2.1; omega)] at e
  subst ht
  exact ⟨rfl, B', rfl, hsz, hR, hU⟩

/-- **`split_child` meets `splitSpec`.** -/
theorem split_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm splitFunc)
    (har : HasArity fi 3 0) : TFSpecAt P host a (splitSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, -, xv, iv, zv, ma, mt, B, t, X, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨hf, hres, xv, iv, zv, ma, mt, B, t, X, hargs, hm, hx, hpre⟩ f vs₀
    obtain ⟨x, y, ly, kx, ky, cs, cy, hX, h, lo, hi, ho⟩ := SData.ofPre hpre
    have hxv : xv.toNat = x := by rw [← hx, hX]; rfl
    have hY : (X.children.getD iv.toNat X).page = y := by
      rw [hX]; simp only [Tree.children]; rw [getD_of_lt _ h.hi, h.hy]; rfl
    rw [hargs, forCall_split, splitFunc_body]
    refine split_body (XCtx.ofResolved hres) h hm hxv rfl rfl (h.sorted ho) fun B' hsz hR hU F => ?_
    exact bodyPostT_normal (by simp [hrs]) <| split_post hm hx hpre hsz (hX ▸ hR) (by rw [hY, hxv]; exact hU)

end Silmaril.WasmSpec.BTree.V2
