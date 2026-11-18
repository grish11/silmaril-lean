module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Alloc
public import Silmaril.Proofs.WasmSpec.BTree.V2.Trees

/-!
# The B-tree library, version 2: `btree_create` by tactics

`btree_create(t)` grows the empty memory by two pages (`t_grow`); on failure it returns `0`
with the memory still empty, on success it writes the metadata page (`t` at `0`, root page
`1` at `4`, an empty free list at `8`) and an empty root leaf at page `1`, and returns `1`:
the memory then holds the B-tree `Tree.node 1 true [] []` with no free pages
(`created_btree`). Every-run total correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The writes of `btree_create` after the code before them. -/
abbrev createStores : List Instr := [c32 0, lget 0, istore, c32 4, c32 1, istore,
  c32 8, c32 0, istore, c32 65536, c32 1, istore, c32 65540, c32 0, istore, c32 1]

theorem createFunc_body : createFunc.body = [c32 2, .memoryGrow ⟨0⟩, c32 4294967295,
    .intRelOp .i32 .eq, .if_ .empty [c32 0, .return_] []] ++ createStores := rfl

theorem forCall_create (mi : ModuleInst) (t : BitVec 32) :
    Frame.forCall mi [.i32 t] createFunc.locals = fr mi [t] := rfl

/-- The memory `btree_create` builds from two zero pages. -/
def createdMem (G : ByteArray) (t : BitVec 32) : ByteArray :=
  wr (wr (wr (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)) 8 (BitVec.ofNat 32 0)) 65536
    (BitVec.ofNat 32 1)) 65540 (BitVec.ofNat 32 0)

/-- The size of the built memory. -/
theorem size_createdMem {G : ByteArray} (hG : G.size = 131072) (t : BitVec 32) :
    (createdMem G t).size = 131072 := by
  have h1 : (wr G 0 t).size = 131072 := (size_wr _ (by omega)).trans hG
  have h2 : (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)).size = 131072 :=
    (size_wr _ (by omega)).trans h1
  have h3 : (wr (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)) 8 (BitVec.ofNat 32 0)).size = 131072 :=
    (size_wr _ (by omega)).trans h2
  have h4 : (wr (wr (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)) 8 (BitVec.ofNat 32 0)) 65536
      (BitVec.ofNat 32 1)).size = 131072 := (size_wr _ (by omega)).trans h3
  exact (size_wr _ (by omega)).trans h4

/-- The words of the built memory at the five addresses written. -/
theorem wd_createdMem {G : ByteArray} (hG : G.size = 131072) (t : BitVec 32) :
    wd (createdMem G t) 0 = t ∧ wd (createdMem G t) 4 = BitVec.ofNat 32 1 ∧
      wd (createdMem G t) 8 = 0 ∧ wd (createdMem G t) 65536 = BitVec.ofNat 32 1 ∧
      wd (createdMem G t) 65540 = 0 := by
  have h1 : (wr G 0 t).size = 131072 := (size_wr _ (by omega)).trans hG
  have h2 : (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)).size = 131072 :=
    (size_wr _ (by omega)).trans h1
  have h3 : (wr (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)) 8 (BitVec.ofNat 32 0)).size = 131072 :=
    (size_wr _ (by omega)).trans h2
  have h4 : (wr (wr (wr (wr G 0 t) 4 (BitVec.ofNat 32 1)) 8 (BitVec.ofNat 32 0)) 65536
      (BitVec.ofNat 32 1)).size = 131072 := (size_wr _ (by omega)).trans h3
  unfold createdMem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [wd_wr_ne _ (by omega) (by omega), wd_wr_ne _ (by omega) (by omega),
      wd_wr_ne _ (by omega) (by omega), wd_wr_ne _ (by omega) (by omega), wd_wr_same _ (by omega)]
  · rw [wd_wr_ne _ (by omega) (by omega), wd_wr_ne _ (by omega) (by omega),
      wd_wr_ne _ (by omega) (by omega), wd_wr_same _ (by omega)]
  · rw [wd_wr_ne _ (by omega) (by omega), wd_wr_ne _ (by omega) (by omega),
      wd_wr_same _ (by omega)]
    rfl
  · rw [wd_wr_ne _ (by omega) (by omega), wd_wr_same _ (by omega)]
  · rw [wd_wr_same _ (by omega)]
    rfl

/-- An empty bounded array: a zero length cell inside memory and below `INT32_MAX`. -/
theorem OBAnd.empty {B : ByteArray} {x n : Nat} (h0 : wd B x = 0) (hs : x + 4 + 4 * n ≤ B.size)
    (hm : x + 4 + 4 * n ≤ int32Max) : OBAnd B x n [] :=
  ⟨⟨⟨by rw [h0]; rfl, rfl, Nat.zero_le _, hm, hs⟩, List.Pairwise.nil⟩, List.nodup_nil⟩

/-- The empty root leaf. -/
abbrev rootLeaf : Tree := .node 1 true [] []

/-- The pages of the empty root leaf. -/
theorem owns_rootLeaf {p : Nat} (h : Owns p rootLeaf) : p = 1 := by
  cases h with
  | here => rfl
  | child hc _ => simp at hc

/-- **The built memory holds an empty B-tree.** -/
theorem created_btree {G : ByteArray} (hG : G.size = 131072) {t : BitVec 32}
    (ht : 2 ≤ t.toNat) (ht' : t.toNat ≤ 4045) :
    IsBTree (createdMem G t) t.toNat fun _ => False := by
  obtain ⟨w0, w4, w8, w1, w2⟩ := wd_createdMem hG t
  have hs : (createdMem G t).size = 131072 := size_createdMem hG t
  have hpg : PageOK (createdMem G t) 1 := ⟨le_refl _, by decide, by rw [hs]; decide⟩
  have hl : wd (createdMem G t) (page * 1) ≠ 0 := by
    show wd (createdMem G t) 65536 ≠ 0
    rw [w1]
    decide
  have hk : OBAnd (createdMem G t) (page * 1 + 4) 8090 [] :=
    OBAnd.empty (B := createdMem G t) (x := 65540) w2 (by rw [hs]; omega)
      (by simp only [int32Max]; omega)
  have hR : Repr (createdMem G t) rootLeaf := .leaf hl hk
  have ho : Ordered none none rootLeaf :=
    .mk List.Pairwise.nil (fun _ h => by simp at h) rfl fun _ h => by simp at h
  have hb : Balanced t.toNat true 0 rootLeaf := .leaf ⟨.inl rfl, Nat.zero_le _⟩
  have hd : Distinct rootLeaf :=
    .node (fun _ h => by simp at h) List.Pairwise.nil fun _ h => by simp at h
  have hf : OBAnd (createdMem G t) 8 16381 [] :=
    OBAnd.empty w8 (by rw [hs]; omega) (by simp only [int32Max]; omega)
  refine ⟨rootLeaf, [], ⟨ht, ht', by rw [hs]; rfl, by rw [w0, BitVec.ofNat_toNat]; rfl,
    by rw [w4]; rfl, hR, ho, ⟨0, hb⟩, hd, fun p hp => owns_rootLeaf hp ▸ hpg, hf,
    fun _ h => by simp at h⟩, fun k => ⟨fun h => ?_, False.elim⟩⟩
  exact absurd (inTree_leaf.1 h) (by simp)

/-- The postcondition of `btree_create` for an outcome it builds. -/
theorem create_post {a : Nat} {fi : FuncInst H} {s : Store H} {t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : MemAt s fi.module ma mt B) {b : BitVec 32}
    {mt' : MemoryType} {B' : ByteArray} (h32 : mt'.address = .i32)
    (hB : (b = 1 ∧ IsBTree B' t.toNat fun _ => False) ∨ (b = 0 ∧ B'.size = 0)) :
    (createSpec a fi).post s [.i32 t] (s.setMem ma ⟨mt', B'⟩) (.normal [.i32 b]) := by
  intro t' ma' mt'' B'' hargs hm' _ _
  have ht : t' = t := i32_inj (List.cons.inj hargs).1
  subst ht
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  exact ⟨b, mt', B', rfl, rfl, h32, hB⟩

/-- `memory.grow` failed: return `0`, the memory unchanged and empty. -/
theorem create_fail {s : Store H} {mi : ModuleInst} {t : BitVec 32} {Q : Post H}
    (hQ : ∀ F, Q s F (.ret [.i32 0])) :
    TWP P host s (fr mi [t]) (vals [Val.i32 (BitVec.allOnes 32)].reverse ++ expression
      ([c32 4294967295, .intRelOp .i32 .eq, .if_ .empty [c32 0, .return_] []] ++ createStores))
      Q := by
  wbegin
  wrun
  refine t_if (fun _ => ?_) (fun hc => absurd hc (by decide))
  wbegin
  wrun
  exact t_ret (armPostT_ret (hQ _))

/-- `memory.grow` succeeded from the empty memory: write the tree, return `1`. -/
theorem create_grown {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {G : ByteArray} {t : BitVec 32} (hm : MemAt s mi ma mt G) (hG : G.size = 131072)
    {Q : Post H} (hQ : ∀ F, Q (s.setMem ma ⟨mt, createdMem G t⟩) F (.normal [.i32 1])) :
    TWP P host s (fr mi [t]) (vals [Val.i32 (BitVec.ofNat 32 0)].reverse ++ expression
      ([c32 4294967295, .intRelOp .i32 .eq, .if_ .empty [c32 0, .return_] []] ++ createStores))
      Q := by
  have hs : ∀ (B : ByteArray), B.size = 131072 → 65544 ≤ B.size := fun _ h => by omega
  wbegin
  wrun
  refine t_if (fun hc => absurd hc (by decide)) (fun _ => t_armEnd ?_)
  wrun
  simp only [setMem_setMem] at *
  exact w_end (m := .total) (rs := [_]) (hQ _)

/-- The body of `btree_create` from the empty memory. -/
theorem create_body {a : Nat} {fi : FuncInst H} {s : Store H} {t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : MemAt s fi.module ma mt B) (h32 : mt.address = .i32)
    (hsz : B.size = 0) (ht : 2 ≤ t.toNat) (ht' : t.toNat ≤ 4045) {f : Frame} {vs₀ : List Val} :
    TWP P host s (fr fi.module [t]) (vals [] ++ expression createFunc.body)
      (bodyPostT P host 1 f vs₀ (callPost f vs₀ ((createSpec a fi).post s [.i32 t]))) := by
  have hz : B.size / 65536 = 0 := by rw [hsz]
  rw [createFunc_body]
  wbegin
  wrun
  refine t_grow hm (fun mt' ha _ hm' => ?_) ?_
  · have hG : (grown B (2#32).toNat).size = 131072 := by rw [size_grown, hsz]; rfl
    rw [hz]
    refine create_grown hm' hG fun F => ?_
    rw [setMem_setMem]
    exact bodyPostT_normal rfl (create_post hm (ha.trans h32) (.inl ⟨rfl, created_btree hG ht ht'⟩))
  · refine create_fail fun F => ?_
    have hq := bodyPostT_ret (P := P) (host := host) (F := F) (vs₀ := vs₀) (f := f)
      (create_post (a := a) (t := t) hm (b := 0) h32 (.inr ⟨rfl, hsz⟩))
    rwa [hm.setMem_self] at hq

/-- **`btree_create` meets `createSpec`.** -/
theorem create_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm createFunc)
    (har : HasArity fi 1 1) : TFSpecAt P host a (createSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, t, ma, mt, B, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨-, t, ma, mt, B, hargs, hm, h32, hsz, ht, ht'⟩ f vs₀
    rw [hargs, forCall_create, hrs]
    exact create_body hm h32 hsz ht ht'

end Silmaril.WasmSpec.BTree.V2
