module

public import Silmaril.Proofs.WasmSpec.BTree.V2.InsLeaf
public import Silmaril.Proofs.WasmSpec.BTree.V2.InsAlloc

/-!
# The B-tree library, version 2: `insert_nonfull` by tactics

`insert_nonfull(x, k)` is proved by induction on the height `d` of the subtree at `x`
(`insNF_valid`): at a leaf, `ba_insert` puts `k` at its `oba_find` index (`leaf_step`); at an
inner node, the child `j` (the `oba_find` index) is split first if it is full (`alloc_node`
then `split_child`; `-1` from the allocator returns `0`), and the recursive call on the child
(or the new right half, when `k` is above the median) is an update of that child, hence of the
node (`Sub.replace`, `Upd.trans`). Every-run total correctness at every profile and host
relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The callees of `insert_nonfull`: `oba_get` (0), `oba_find` (1), `ba_insert` (3),
`alloc_node` (5), `split_child` (6) and itself (7), and the resolution of the calls. -/
structure NCtx (P : Profile) (host : HostSemantics H) (s : Store H) (mi : ModuleInst) : Type where
  hres : Resolved s mi
  aG : Nat
  fiG : FuncInst H
  hG : mi.funcs[0]? = some aG
  hfG : s.funcs[aG]? = some fiG
  hGS : TFSpecAt P host aG (getSpec aG fiG)
  hmG : fiG.module = mi
  aF : Nat
  fiF : FuncInst H
  hF : mi.funcs[1]? = some aF
  hfF : s.funcs[aF]? = some fiF
  hFS : TFSpecAt P host aF (findSpec aF fiF)
  hmF : fiF.module = mi
  aI : Nat
  fiI : FuncInst H
  hI : mi.funcs[3]? = some aI
  hfI : s.funcs[aI]? = some fiI
  hIS : TFSpecAt P host aI (baInsertSpec aI fiI)
  hmI : fiI.module = mi
  aA : Nat
  fiA : FuncInst H
  hA : mi.funcs[5]? = some aA
  hfA : s.funcs[aA]? = some fiA
  hAS : TFSpecAt P host aA (allocSpecI32 aA fiA)
  hmA : fiA.module = mi
  aS : Nat
  fiS : FuncInst H
  hS : mi.funcs[6]? = some aS
  hfS : s.funcs[aS]? = some fiS
  hSS : TFSpecAt P host aS (splitSpec aS fiS)
  hmS : fiS.module = mi
  aN : Nat
  fiN : FuncInst H
  hN : mi.funcs[7]? = some aN
  hfN : s.funcs[aN]? = some fiN
  hcN : fiN.code = .wasm insertNonfullFunc
  harN : HasArity fiN 2 1
  hmN : fiN.module = mi

/-- **A good outcome** of `insert_nonfull` on the subtree `X` (memory `B`, free pages `φ`):
the store `s'` changes only memory `ma`, still `i32`, to a subtree `X'` that is an update of
`X` adding `k` (`b = 1`) or nothing (`b = 0`). -/
def NGood (s : Store H) (ma : Nat) (B : ByteArray) (t : Nat) (φ : List (BitVec 32))
    (lo hi : Option (BitVec 32)) (r : Bool) (d : Nat) (X : Tree) (k b : BitVec 32)
    (s' : Store H) : Prop :=
  ∃ (mt' : MemoryType) (B' : ByteArray) (φ' : List (BitVec 32)) (X' : Tree),
    s' = s.setMem ma ⟨mt', B'⟩ ∧ mt'.address = .i32 ∧ Sub B' t φ' lo hi r d X' ∧
    ((b = 1 ∧ Upd B B' φ φ' X X' (· = k)) ∨ (b = 0 ∧ Upd B B' φ φ' X X' fun _ => False))

/-- The postcondition of `insert_nonfull` from a good outcome. -/
theorem nf_post {a : Nat} {fi : FuncInst H} {s s' : Store H} {xv k b : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {t : Nat} {φ : List (BitVec 32)}
    {lo hi : Option (BitVec 32)} {r : Bool} {d : Nat} {X : Tree}
    (hm : MemAt s fi.module ma mt B) (hx : X.page = xv.toNat) (hpre : NFPre B t φ lo hi r d X k)
    (hg : NGood s ma B t φ lo hi r d X k b s') :
    (insNFSpec a fi lo hi r d).post s [.i32 xv, .i32 k] s' (.normal [.i32 b]) := by
  intro xv' k' ma' mt' B' t' φ' X' hargs hm' _ hx' hpre'
  obtain ⟨rfl, rfl⟩ : xv' = xv ∧ k' = k := by
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨i32_inj hargs.1, i32_inj hargs.2⟩
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  obtain ⟨rfl, rfl, rfl⟩ := hpre.unique hpre' (hx.trans hx'.symm)
  obtain ⟨mt₂, B₂, φ₂, X₂, hs, h32, hS, hU⟩ := hg
  exact ⟨b, mt₂, B₂, φ₂, X₂, rfl, hs, h32, hS, hU⟩

/-- **The recursive call** on child `j` of the node `Xn` (an update of `X` keeping its keys),
whose page is local `4`, and the end of the body. -/
theorem nf_rec {s : Store H} {mi : ModuleInst} {ma : Nat} {mt₁ : MemoryType} {B B₁ : ByteArray}
    {t d' x j : Nat} {φ φ₁ : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} {X : Tree} {k : BitVec 32}
    (c : NCtx P host s mi)
    (IH : ∀ lo hi r, TFSpecAt P host c.aN (insNFSpec c.aN c.fiN lo hi r d'))
    (hm₁ : MemAt (s.setMem ma ⟨mt₁, B₁⟩) mi ma mt₁ B₁) (h32 : mt₁.address = .i32)
    (hS₁ : Sub B₁ t φ₁ lo hi r (d' + 1) (.node x false ks cs)) (hj : j < cs.length)
    (hpre : NFPre B₁ t φ₁ (lob lo ks j) (hib hi ks j) false d' cs[j] k)
    (hU₁ : Upd B B₁ φ φ₁ X (.node x false ks cs) fun _ => False)
    {xv xp jv cv zv : BitVec 32} (hcv : cs[j].page = cv.toNat) {Q : Post H}
    (hQ : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) X k b s' → ∀ F, Q s' F (.normal [.i32 b])) :
    TWP P host (s.setMem ma ⟨mt₁, B₁⟩) (fr mi [xv, k, xp, jv, cv, zv])
      (vals ([] : List Val).reverse ++ expression [lget 4, lget 1, call 7]) Q := by
  have hmN : MemAt (s.setMem ma ⟨mt₁, B₁⟩) c.fiN.module ma mt₁ B₁ := by rw [c.hmN]; exact hm₁
  have hres : Resolved (s.setMem ma ⟨mt₁, B₁⟩) c.fiN.module := by
    rw [c.hmN]; exact c.hres.setMem ma _
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 cv, .i32 k]) (by simpa [Idx.toNat] using c.hN) c.hfN
    (IH _ _ _) ⟨c.hfN, hres, cv, k, ma, mt₁, B₁, t, φ₁, cs[j], rfl, hmN, h32, hcv, hpre⟩
    fun s' o hp => ?_
  obtain ⟨b, mt₂, B₂, φ₂, c', ho, hs₂, h32', hS₂, hU₂⟩ := hp cv k ma mt₁ B₁ t φ₁ cs[j] rfl hmN h32 hcv hpre
  refine ⟨b, ho, ?_⟩
  rw [hs₂, setMem_setMem]
  refine w_end (m := .total) (rs := [.i32 b]) (hQ b _ ?_ _)
  rcases hU₂ with ⟨rfl, hU₂⟩ | ⟨rfl, hU₂⟩
  · obtain ⟨hS', hU'⟩ := hS₁.replace hj hS₂ hU₂
    exact ⟨mt₂, B₂, φ₂, _, rfl, h32', hS', .inl ⟨rfl, hU₁.trans hU'⟩⟩
  · obtain ⟨hS', hU'⟩ := hS₁.replace hj hS₂ hU₂
    exact ⟨mt₂, B₂, φ₂, _, rfl, h32', hS', .inr ⟨rfl, hU₁.trans hU'⟩⟩

/-- After the split: compare `k` with the median and descend into the half holding it. -/
theorem nf_after_split {s : Store H} {mi : ModuleInst} {ma : Nat} {mt' : MemoryType} {B B'' : ByteArray}
    {t d' x j y : Nat} {φ φ' : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r ly : Bool}
    {kx ky : List (BitVec 32)} {cs cy : List Tree} {k rv xv : BitVec 32}
    (c : NCtx P host s mi)
    (IH : ∀ lo hi r, TFSpecAt P host c.aN (insNFSpec c.aN c.fiN lo hi r d'))
    (hm : MemAt (s.setMem ma ⟨mt', B''⟩) mi ma mt' B'') (h32 : mt'.address = .i32)
    (hxv : xv.toNat = x)
    (hS : Sub B'' t φ' lo hi r (d' + 1) ((Tree.node x false kx cs).splitChild t rv.toNat j))
    (hU : Upd B B'' φ φ' (.node x false kx cs) ((Tree.node x false kx cs).splitChild t rv.toNat j)
      fun _ => False)
    (hj : j < cs.length) (hl : cs.length = kx.length + 1) (hy : cs[j] = .node y ly ky cy)
    (hky : ky.length = 2 * t - 1)
    (hw : Within (lob lo kx j) (hib hi kx j) k) (hk : ¬ InTree k (.node y ly ky cy))
    {Q : Post H}
    (hQ : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) (.node x false kx cs) k b s' → ∀ F,
      Q s' F (.normal [.i32 b])) :
    TWP P host (s.setMem ma ⟨mt', B''⟩)
      (fr mi [xv, k, xv * 65536#32, BitVec.ofNat 32 j, (cs[j]).ptr, rv])
      (vals [] ++ expression [lget 1, lget 2, c32 4, iadd, lget 3, call 0, igts,
        .if_ .empty [lget 5, lset 4] []])
      (armPostT P host [] (expression [lget 4, lget 1, call 7]) Q) := by
  have hjk : j ≤ kx.length := by omega
  have hX1 := splitChild_eq (t := t) (z := rv.toNat) (x := x) (l := false) (kx := kx) hj hy
  have hR := hS.hR
  rw [hX1] at hR
  have hK : BA B'' (page * x + 4) 8090 (kx.insertIdx j (ky.getD (t - 1) 0)) := hR.leaf_iff.2.2.1.1.1
  have hx32 : x < 32768 := (hS.hpg x (by rw [hX1]; exact .here)).2.1
  have hxa : (xv * 65536#32 + 4#32).toNat = page * x + 4 := addr_of hxv hx32 4 (by omega)
  have hl1 : (kx.insertIdx j (ky.getD (t - 1) 0)).length = kx.length + 1 :=
    List.length_insertIdx_of_le_length hjk _
  have hjn : (BitVec.ofNat 32 j).toNat = j := toNat_ofNat_lt (by have := hK.2.2.1; omega)
  have hmG : MemAt (s.setMem ma ⟨mt', B''⟩) c.fiG.module ma mt' B'' := by rw [c.hmG]; exact hm
  have hKa : BA B'' (xv * 65536#32 + 4#32).toNat 8090 (kx.insertIdx j (ky.getD (t - 1) 0)) := by
    rw [hxa]; exact hK
  have hji : (BitVec.ofNat 32 j).toNat < (kx.insertIdx j (ky.getD (t - 1) 0)).length := by
    rw [hjn, hl1]; omega
  have hmv : (kx.insertIdx j (ky.getD (t - 1) 0)).getD (BitVec.ofNat 32 j).toNat 0 = ky.getD (t - 1) 0 := by
    rw [hjn, List.getD_eq_getElem?_getD, median_key hjk]; rfl
  wbegin
  wrun
  refine t_call1 (rs := [.i32 k]) (args := [.i32 (xv * 65536#32 + 4#32), .i32 (BitVec.ofNat 32 j)])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt', B'', 8090, _, rfl, hmG, hKa, hji⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt' B'' 8090 _ rfl (hp.1 ▸ hmG) hKa hji, ?_⟩
  rw [hp.1, hmv]
  wrun
  have hcs1 := split_children_get (.node y ly (ky.take (t - 1)) (cy.take t))
    (.node rv.toNat ly (ky.drop t) (cy.drop t)) hj
  have hl2 : ((cs.set j (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (j + 1)
      (.node rv.toNat ly (ky.drop t) (cy.drop t))).length = cs.length + 1 := length_split_children _ _ hj
  rw [hX1] at hS hU
  have hbr := bounds_right (lo := lo) (hi := hi) (m := ky.getD (t - 1) 0) hjk
  have hbl := bounds_left (lo := lo) (hi := hi) (m := ky.getD (t - 1) 0) hjk
  have hhalf := fun k' => halves_inTree (y := y) (z := rv.toNat) (ly := ly) (cy := cy) (k := k')
    (by have := hS.ht; omega) hky
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · show TWP P host _ _ _ _
    have hmk : (ky.getD (t - 1) 0).toInt < k.toInt := by simpa using hc
    have hz : (((cs.set j (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (j + 1)
        (.node rv.toNat ly (ky.drop t) (cy.drop t)))[j + 1]'(by omega)) =
        .node rv.toNat ly (ky.drop t) (cy.drop t) := by
      have := hcs1.2; rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at this
    wbegin
    wrun
    refine t_armEnd (t_armEnd (nf_rec (j := j + 1) c IH hm h32 hS (by omega)
      ⟨hS.child (by omega), ?_, ?_, ?_⟩ hU (by rw [hz]; rfl) hQ))
    · rw [hz]; simp [Tree.keys, length_right_keys hky]; have := hS.ht; omega
    · rw [hbr.1, hbr.2]; exact within_right hw hmk
    · rw [hz]; exact fun h => hk ((hhalf k).1 (.inr (.inr h)))
  · show TWP P host _ _ _ _
    have hkm : k.toInt < (ky.getD (t - 1) 0).toInt := by
      have hle : k.toInt ≤ (ky.getD (t - 1) 0).toInt := by simpa using hc
      have hne : k ≠ ky.getD (t - 1) 0 := fun e => hk ((hhalf k).1 (.inr (.inl e)))
      have hne' : k.toInt ≠ (ky.getD (t - 1) 0).toInt := fun e => hne (BitVec.toInt_inj.1 e)
      omega
    have hyl : (((cs.set j (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (j + 1)
        (.node rv.toNat ly (ky.drop t) (cy.drop t)))[j]'(by omega)) =
        .node y ly (ky.take (t - 1)) (cy.take t) := by
      have := hcs1.1; rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at this
    have hmem : Tree.node y ly (ky.take (t - 1)) (cy.take t) ∈
        (cs.set j (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (j + 1)
          (.node rv.toNat ly (ky.drop t) (cy.drop t)) := by
      have h := List.getElem_mem (l := (cs.set j (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx
        (j + 1) (.node rv.toNat ly (ky.drop t) (cy.drop t))) (n := j) (by omega)
      rwa [hyl] at h
    have hyok : PageOK B'' y := hS.hpg y (.child hmem .here)
    refine t_armEnd (t_armEnd (nf_rec (j := j) c IH hm h32 hS (by omega)
      ⟨hS.child (by omega), ?_, ?_, ?_⟩ hU
      (by rw [hyl, hy]; exact (ptr_toNat (B := B'') (T := .node y ly ky cy) hyok).symm) hQ))
    · rw [hyl]; simp [Tree.keys, length_left_keys hky]; have := hS.ht; omega
    · rw [hbl.1, hbl.2]; exact within_left hw hkm
    · rw [hyl]; exact fun h => hk ((hhalf k).1 (.inl h))
/-- The full child: allocate a page (`0` if none), split the child, then `nf_after_split`. -/
theorem nf_full {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t d' x j y : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r ly : Bool}
    {kx ky : List (BitVec 32)} {cs cy : List Tree} {k xv : BitVec 32}
    (c : NCtx P host s mi)
    (IH : ∀ lo hi r, TFSpecAt P host c.aN (insNFSpec c.aN c.fiN lo hi r d'))
    (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hxv : xv.toNat = x)
    (hS : Sub B t φ lo hi r (d' + 1) (.node x false kx cs))
    (hj : j < cs.length) (hl : cs.length = kx.length + 1) (hy : cs[j] = .node y ly ky cy)
    (hky : ky.length = 2 * t - 1) (hkx : kx.length < 2 * t - 1)
    (hw : Within (lob lo kx j) (hib hi kx j) k) (hk : ¬ InTree k (.node y ly ky cy))
    {Q : Post H}
    (hQ : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) (.node x false kx cs) k b s' → ∀ F,
      Q s' F (.normal [.i32 b]))
    (hQr : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) (.node x false kx cs) k b s' → ∀ F,
      Q s' F (.ret [.i32 b])) :
    TWP P host s (fr mi [xv, k, xv * 65536#32, BitVec.ofNat 32 j, (cs[j]).ptr, 0])
      (vals [] ++ expression ([call 5, lset 5, lget 5, c32 4294967295, .intRelOp .i32 .eq,
        .if_ .empty [c32 0, .return_] [], lget 0, lget 3, lget 5, call 6] ++
        [lget 1, lget 2, c32 4, iadd, lget 3, call 0, igts, .if_ .empty [lget 5, lset 4] []]))
      (armPostT P host [] (expression [lget 4, lget 1, call 7]) Q) := by
  have hmA : MemAt s c.fiA.module ma mt B := by rw [c.hmA]; exact hm
  wbegin
  refine t_call1 (rs := []) (args := []) (by simpa [Idx.toNat] using c.hA) c.hfA c.hAS
    ⟨c.hfA, ma, mt, B, φ, rfl, hmA, h32, hS.hsz, hS.hfree, fun q hq => (hS.hfok q hq).1⟩
    fun s' o hp => ?_
  obtain ⟨rv, mt', B', φ', ho, hs', h32', hA⟩ :=
    hp ma mt B φ rfl hmA h32 hS.hsz hS.hfree fun q hq => (hS.hfok q hq).1
  refine ⟨rv, ho, ?_⟩
  rw [hs']
  have hm' : MemAt (s.setMem ma ⟨mt', B'⟩) mi ma mt' B' := MemAt.setMemT hm mt' B'
  obtain ⟨hS', hU'⟩ := alloc_sub hS hA
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · wbegin
    wrun
    exact t_ret (armPostT_ret (armPostT_ret (hQr 0 _ ⟨mt', B', φ', _, rfl, h32', hS', .inr ⟨rfl, hU'⟩⟩ _)))
  · show TWP P host _ _ _ _
    have hne : rv ≠ -1 := by
      rw [← minus_one]; simpa using hc
    obtain ⟨hzok, hzX, hzφ, hw'⟩ := alloc_fresh hS hA hne
    have hjn : (BitVec.ofNat 32 j).toNat = j := toNat_ofNat_lt (by
      have := hS.hR.leaf_iff.2.2.2 rfl; have := this.2.2.1; simp at this; omega)
    have hyo : Ordered (lob lo kx j) (hib hi kx j) (.node y ly ky cy) := hy ▸ hS.ho.child hj
    have hpre : SplitPre B' t (.node x false kx cs) (BitVec.ofNat 32 j).toNat rv.toNat := by
      rw [hjn]
      refine ⟨hS.ht, hS.ht', hS'.h0, rfl, hS'.hR, hS'.hd, ⟨lo, hi, hS'.ho⟩, hS'.hpg, hzok, hzX, hkx,
        hl, cs[j], List.getElem?_eq_getElem hj, by rw [hy]; exact hky, fun hly => ?_⟩
      rw [hy] at hly ⊢
      cases hly
      have hc2 : cy.length = 2 * t - 1 + 1 := by rw [hyo.inner_len, hky]
      show cy.length = 2 * t
      rw [hc2, Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 2 * 2) (Nat.mul_le_mul_left 2 hS.ht))]
    have hmS : MemAt (s.setMem ma ⟨mt', B'⟩) c.fiS.module ma mt' B' := by rw [c.hmS]; exact hm'
    have hres : Resolved (s.setMem ma ⟨mt', B'⟩) c.fiS.module := by
      rw [c.hmS]; exact c.hres.setMem ma _
    have hxp : (Tree.node x false kx cs).page = xv.toNat := hxv.symm
    refine t_armEnd ?_
    wrun
    refine t_call (rs := []) (args := [.i32 xv, .i32 (BitVec.ofNat 32 j), .i32 rv])
      (by simpa [Idx.toNat] using c.hS) c.hfS c.hSS
      ⟨c.hfS, hres, xv, _, rv, ma, mt', B', t, _, rfl, hmS, hxp, hpre⟩ fun s'' o hp => ?_
    obtain ⟨ho, B'', hs'', hsz, hR'', hU''⟩ := hp xv _ rv ma mt' B' t _ rfl hmS hxp hpre
    refine ⟨ho, ?_⟩
    rw [hs'', setMem_setMem]
    rw [hjn] at hR'' hU''
    have hY : ((Tree.node x false kx cs).children.getD j (.node x false kx cs)).page = y := by
      simp only [Tree.children]; rw [getD_of_lt _ hj, hy]; rfl
    rw [hY, hxv] at hU''
    obtain ⟨hS'', hU⟩ := split_sub hS hA hne hj hy hky hkx hsz hR'' hU''
    exact nf_after_split c IH (MemAt.setMemT hm mt' B'') h32' hxv hS'' hU hj hl hy hky hw hk hQ
/-- The leaf arm: `ba_insert` of `k` at its index, return `1`. -/
theorem nf_leaf {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t d x j : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r : Bool}
    {kx : List (BitVec 32)} {k xv jv : BitVec 32} {rest : List Admin}
    (c : NCtx P host s mi) (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hxv : xv.toNat = x)
    (hpre : NFPre B t φ lo hi r d (.node x true kx []) k) (hF : FindsAt kx k j)
    (hjv : jv.toNat = j) {Q : Post H}
    (hQr : ∀ b s', NGood s ma B t φ lo hi r d (.node x true kx []) k b s' → ∀ F,
      Q s' F (.ret [.i32 b])) :
    TWP P host s (fr mi [xv, k, xv * 65536#32, jv, 0, 0])
      (vals [] ++ expression [lget 2, c32 4, iadd, lget 3, lget 1, call 3, c32 1, .return_])
      (armPostT P host [] rest Q) := by
  have hpok : PageOK B x := hpre.1.hpg x .here
  have hxa : (xv * 65536#32 + 4#32).toNat = page * x + 4 := addr_of hxv hpok.2.1 4 (by omega)
  have hK : BA B (xv * 65536#32 + 4#32).toNat 8090 kx := by
    rw [hxa]; exact hpre.1.hR.leaf_iff.2.2.1.1.1
  have hkl : kx.length < 8090 := by have := hpre.2.1; have := hpre.1.ht'; simp only [Tree.keys] at *; omega
  have hjl : jv.toNat ≤ kx.length := hjv ▸ hF.1
  have hmI : MemAt s c.fiI.module ma mt B := by rw [c.hmI]; exact hm
  wbegin
  wrun
  refine t_call (rs := []) (args := [.i32 (xv * 65536#32 + 4#32), .i32 jv, .i32 k])
    (by simpa [Idx.toNat] using c.hI) c.hfI c.hIS ⟨c.hfI, _, _, _, ma, mt, B, 8090, kx, rfl, hmI, hK, hjl, hkl⟩
    fun s' o hp => ?_
  obtain ⟨ho, B', hs', hK', hso⟩ := hp _ _ _ ma mt B 8090 kx rfl hmI hK hjl hkl
  refine ⟨ho, ?_⟩
  have hK'' : BA B' (page * x + 4) 8090 (kx.insertIdx j k) := by rw [hxa, hjv] at hK'; exact hK'
  have hso' : SameOutside B B' (page * x + 4) (4 + 4 * 8090) := by rw [hxa] at hso; exact hso
  rw [hs']
  obtain ⟨hS', hU'⟩ := leaf_step hpre hF (SameOutside.agree hso') hK''
  wrun
  exact t_ret (armPostT_ret (hQr 1 _ ⟨mt, B', φ, _, rfl, h32, hS', .inl ⟨rfl, hU'⟩⟩ _))
/-- An inner node: read child `j`'s page; split it first if it is full; the recursive call. -/
theorem nf_inner {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t d' x j : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r : Bool}
    {kx : List (BitVec 32)} {cs : List Tree} {k xv : BitVec 32}
    (c : NCtx P host s mi)
    (IH : ∀ lo hi r, TFSpecAt P host c.aN (insNFSpec c.aN c.fiN lo hi r d'))
    (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hxv : xv.toNat = x)
    (hpre : NFPre B t φ lo hi r (d' + 1) (.node x false kx cs) k) (hF : FindsAt kx k j)
    {Q : Post H}
    (hQ : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) (.node x false kx cs) k b s' → ∀ F,
      Q s' F (.normal [.i32 b]))
    (hQr : ∀ b s', NGood s ma B t φ lo hi r (d' + 1) (.node x false kx cs) k b s' → ∀ F,
      Q s' F (.ret [.i32 b])) :
    TWP P host s (fr mi [xv, k, xv * 65536#32, BitVec.ofNat 32 j, 0, 0])
      (vals ([] : List Val).reverse ++ expression [lget 2, c32 32768, iadd, lget 3, call 0, lset 4,
        lget 4, c32 65536, imul, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, c32 0, iload, c32 2, imul, c32 1, isub,
        .intRelOp .i32 .eq,
        .if_ .empty ([call 5, lset 5, lget 5, c32 4294967295, .intRelOp .i32 .eq,
          .if_ .empty [c32 0, .return_] [], lget 0, lget 3, lget 5, call 6] ++
          [lget 1, lget 2, c32 4, iadd, lget 3, call 0, igts, .if_ .empty [lget 5, lset 4] []]) [],
        lget 4, lget 1, call 7]) Q := by
  obtain ⟨hS, hn, hw, hk⟩ := hpre
  have hnot : k ∉ kx := fun hm' => hk (.here hm')
  have hl : cs.length = kx.length + 1 := hS.ho.inner_len
  have hj : j < cs.length := by have := hF.1; omega
  have hpok : PageOK B x := hS.hpg x .here
  have hP : BA B (page * x + 32768) 8091 (cs.map Tree.ptr) := hS.hR.leaf_iff.2.2.2 rfl
  have hxp : (xv * 65536#32 + 32768#32).toNat = page * x + 32768 := addr_of hxv hpok.2.1 32768 (by omega)
  have hjn : (BitVec.ofNat 32 j).toNat = j := toNat_ofNat_lt (by have := hP.2.2.1; simp at this; omega)
  have hPa : BA B (xv * 65536#32 + 32768#32).toNat 8091 (cs.map Tree.ptr) := by rw [hxp]; exact hP
  have hji : (BitVec.ofNat 32 j).toNat < (cs.map Tree.ptr).length := by rw [hjn]; simpa using hj
  have hmG : MemAt s c.fiG.module ma mt B := by rw [c.hmG]; exact hm
  have hv : (cs.map Tree.ptr).getD (BitVec.ofNat 32 j).toNat 0 = cs[j].ptr := by
    rw [hjn, getD_of_lt _ (by simpa using hj), List.getElem_map]
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 (xv * 65536#32 + 32768#32), .i32 (BitVec.ofNat 32 j)])
    (by simpa [Idx.toNat] using c.hG) c.hfG c.hGS ⟨c.hfG, _, _, ma, mt, B, 8091, _, rfl, hmG, hPa, hji⟩
    fun s' o hp => ⟨_, hp.2 _ _ ma mt B 8091 _ rfl (hp.1 ▸ hmG) hPa hji, ?_⟩
  rw [hp.1, hv]
  rcases hcj : cs[j] with ⟨y, ly, ky, cy⟩
  have hmj : Tree.node y ly ky cy ∈ cs := hcj ▸ List.getElem_mem hj
  have hyok : PageOK B y := hS.hpg y (.child hmj .here)
  have hyv : (Tree.node y ly ky cy).ptr.toNat = y := ptr_toNat (T := .node y ly ky cy) hyok
  have hy0 : ((Tree.node y ly ky cy).ptr * 65536#32).toNat = 65536 * y := addr0_of hyv hyok.2.1
  have hysz : 65536 * (y + 1) ≤ B.size := hyok.2.2
  have hK : BA B (page * y + 4) 8090 ky := (hS.hR.child hmj).leaf_iff.2.2.1.1.1
  have hkl : wd B (65536 * y + 4) = BitVec.ofNat 32 ky.length := hK.1
  have h8 := hS.size8
  wrun
  rw [hy0, show (0#32 : BitVec 32).toNat = 0 from rfl, hS.h0,
    show 65536 * y + ((4 : Fin (2 ^ 64)) : Nat) = 65536 * y + 4 from rfl, hkl]
  have hcb : Balanced t false d' (.node y ly ky cy) := by
    have := hS.child hj; rw [hcj] at this; exact this.hb
  have hky2 : ky.length ≤ 2 * t - 1 := by
    cases hcb with
    | leaf hk => exact hk.2
    | inner hk _ => exact hk.2
  have hky8 : ky.length ≤ 8090 := hK.2.2.1
  have ht' := hS.ht'
  have ht := hS.ht
  have hwc : Within (lob lo kx j) (hib hi kx j) k := within_child hw hF hnot
  have hkc : ¬ InTree k (.node y ly ky cy) := fun h => hk (.child hmj h)
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · have hfull : ky.length = 2 * t - 1 := by
      have e : BitVec.ofNat 32 ky.length = BitVec.ofNat 32 t * 2#32 - 1#32 := by simpa using hc
      have e' := congrArg BitVec.toNat e
      rw [toNat_ofNat_lt (by omega)] at e'
      bv_omega
    have h := nf_full c IH hm h32 hxv hS hj hl hcj hfull hn hwc hkc hQ hQr
    rw [hcj] at h
    exact h
  · show TWP P host _ _ _ _
    have hnf : ky.length < 2 * t - 1 := by
      have e : BitVec.ofNat 32 ky.length ≠ BitVec.ofNat 32 t * 2#32 - 1#32 := by simpa using hc
      by_contra hc'
      exact e (by apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt (by omega)]; bv_omega)
    rw [← hm.setMem_self]
    refine t_armEnd (nf_rec (j := j) c IH (hm.setMem B) h32 hS hj
      ⟨hS.child hj, ?_, ?_, ?_⟩ (Upd.refl B φ _) ?_ ?_)
    · rw [hcj]; exact hnf
    · exact hwc
    · rw [hcj]; exact hkc
    · rw [hcj, hyv]; rfl
    · intro b s' hg F
      exact hQ b s' hg F
theorem insertNonfullFunc_body : insertNonfullFunc.body = [lget 0, c32 65536, imul, lset 2,
    lget 2, c32 4, iadd, lget 1, call 1, lset 3, lget 2, iload,
    .if_ .empty [lget 2, c32 4, iadd, lget 3, lget 1, call 3, c32 1, .return_] [],
    lget 2, c32 32768, iadd, lget 3, call 0, lset 4,
    lget 4, c32 65536, imul, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, c32 0, iload, c32 2, imul, c32 1, isub,
    .intRelOp .i32 .eq,
    .if_ .empty ([call 5, lset 5, lget 5, c32 4294967295, .intRelOp .i32 .eq,
      .if_ .empty [c32 0, .return_] [], lget 0, lget 3, lget 5, call 6] ++
      [lget 1, lget 2, c32 4, iadd, lget 3, call 0, igts, .if_ .empty [lget 5, lset 4] []]) [],
    lget 4, lget 1, call 7] := rfl

theorem forCall_insNF (mi : ModuleInst) (x k : BitVec 32) :
    Frame.forCall mi [.i32 x, .i32 k] insertNonfullFunc.locals = fr mi [x, k, 0, 0, 0, 0] := rfl

/-- **The body of `insert_nonfull`**: `oba_find`, then the leaf or the inner case. -/
theorem nf_body {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {t d : Nat} {φ : List (BitVec 32)} {lo hi : Option (BitVec 32)} {r : Bool} {X : Tree}
    {k xv : BitVec 32} (c : NCtx P host s mi)
    (IH : ∀ d', d = d' + 1 → ∀ lo hi r, TFSpecAt P host c.aN (insNFSpec c.aN c.fiN lo hi r d'))
    (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hx : X.page = xv.toNat)
    (hpre : NFPre B t φ lo hi r d X k) {Q : Post H}
    (hQ : ∀ b s', NGood s ma B t φ lo hi r d X k b s' → ∀ F, Q s' F (.normal [.i32 b]))
    (hQr : ∀ b s', NGood s ma B t φ lo hi r d X k b s' → ∀ F, Q s' F (.ret [.i32 b])) :
    TWP P host s (fr mi [xv, k, 0, 0, 0, 0]) (vals [] ++ expression insertNonfullFunc.body) Q := by
  obtain ⟨x, l, kx, cs⟩ := X
  have hxv : xv.toNat = x := hx.symm
  have hpok : PageOK B x := hpre.1.hpg x .here
  have hl := hpre.1.hR.leaf_iff
  have hxa : (xv * 65536#32 + 4#32).toNat = page * x + 4 := addr_of hxv hpok.2.1 4 (by omega)
  have hx0 : (xv * 65536#32).toNat = 65536 * x := addr0_of hxv hpok.2.1
  have hxsz : 65536 * (x + 1) ≤ B.size := hpok.2.2
  have hK : OBA B (xv * 65536#32 + 4#32).toNat 8090 kx := by rw [hxa]; exact hl.2.2.1.1
  have hmF : MemAt s c.fiF.module ma mt B := by rw [c.hmF]; exact hm
  rw [insertNonfullFunc_body]
  wbegin
  wrun
  refine t_call1 (rs := []) (args := [.i32 (xv * 65536#32 + 4#32), .i32 k])
    (by simpa [Idx.toNat] using c.hF) c.hfF c.hFS ⟨c.hfF, _, _, ma, mt, B, 8090, kx, rfl, hmF, hK⟩
    fun s' o hp => ?_
  obtain ⟨j, hF, ho⟩ := hp.2 _ _ ma mt B 8090 kx rfl (hp.1 ▸ hmF) hK
  refine ⟨_, ho, ?_⟩
  rw [hp.1]
  have hjn : (BitVec.ofNat 32 j).toNat = j := toNat_ofNat_lt (by
    have := hF.1; have := hK.1.2.2.1; omega)
  wrun
  rw [hx0]
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨rfl, rfl⟩ : l = true ∧ cs = [] := ⟨hl.1.2 hc, hl.2.1 (hl.1.2 hc)⟩
    exact nf_leaf c hm h32 hxv hpre hF hjn hQr
  · obtain rfl : l = false := by
      cases l
      · rfl
      · exact absurd hc (hl.1.1 rfl)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := by
      cases hpre.1.hb with
      | inner _ _ => exact ⟨_, rfl⟩
    exact t_armEnd (nf_inner c (IH d' rfl) hm h32 hxv hpre hF hQ hQr)

/-- The callees of `insert_nonfull`, from `Resolved`. -/
noncomputable def NCtx.ofResolved {s : Store H} {mi : ModuleInst} (hres : Resolved s mi) :
    NCtx P host s mi :=
  let g := Classical.choose_spec (Classical.choose_spec (hres.get (j := 0) (by decide)))
  let f := Classical.choose_spec (Classical.choose_spec (hres.get (j := 1) (by decide)))
  let n := Classical.choose_spec (Classical.choose_spec (hres.get (j := 3) (by decide)))
  let a := Classical.choose_spec (Classical.choose_spec (hres.get (j := 5) (by decide)))
  let p := Classical.choose_spec (Classical.choose_spec (hres.get (j := 6) (by decide)))
  let q := Classical.choose_spec (Classical.choose_spec (hres.get (j := 7) (by decide)))
  ⟨hres, _, _, g.1, g.2.1, get_valid g.2.2.2.1 g.2.2.2.2, g.2.2.1,
    _, _, f.1, f.2.1, find_valid f.2.2.2.1 f.2.2.2.2, f.2.2.1,
    _, _, n.1, n.2.1, baInsert_valid n.2.2.2.1 n.2.2.2.2, n.2.2.1,
    _, _, a.1, a.2.1, alloc_valid a.2.2.2.1 a.2.2.2.2, a.2.2.1,
    _, _, p.1, p.2.1, split_valid p.2.2.2.1 p.2.2.2.2, p.2.2.1,
    _, _, q.1, q.2.1, q.2.2.2.1, q.2.2.2.2, q.2.2.1⟩

/-- **`insert_nonfull` meets `insNFSpec`**, for subtrees of every height, by induction on the
height. -/
theorem insNF_valid : ∀ (d : Nat) {a : Nat} {fi : FuncInst H},
    fi.code = .wasm insertNonfullFunc → HasArity fi 2 1 →
    ∀ lo hi r, TFSpecAt P host a (insNFSpec a fi lo hi r d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a fi hcode har lo hi r
    obtain ⟨ps, rs, he, hps, hrs⟩ := har
    refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
    · rintro s args ⟨-, -, xv, k, ma, mt, B, t, φ, X, hargs, -⟩
      simp [hargs, hps]
    · rintro s args ⟨hf, hres, xv, k, ma, mt, B, t, φ, X, hargs, hm, h32, hx, hpre⟩ f vs₀
      rw [hargs, forCall_insNF, hrs]
      let c : NCtx P host s fi.module := NCtx.ofResolved hres
      exact nf_body c (fun d' hd lo hi r => ih d' (by omega) c.hcN c.harN lo hi r) hm h32 hx hpre
        (fun b s' hg F => bodyPostT_normal rfl (nf_post hm hx hpre hg))
        (fun b s' hg F => bodyPostT_ret (nf_post hm hx hpre hg))

end Silmaril.WasmSpec.BTree.V2
