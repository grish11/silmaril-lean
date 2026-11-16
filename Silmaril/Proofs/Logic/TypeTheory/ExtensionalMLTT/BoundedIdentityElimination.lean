module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Motive.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

theorem value_congr {levels : ℕ} {Γ : ECtx} {A a b p M : ETm 0} {n k : ℕ}
    {L : Finset String} (hlevels : max k (n + 1) < levels) (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqB levels ∅ Γ (motiveType A a n) M M)
    (ha : ECtx.JEqB levels ∅ Γ A a a) (hb : ECtx.JEqB levels ∅ Γ A b b)
    (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p) :
    ECtx.JEqB levels ∅ Γ (.univ n) (value M a (.refl a)) (value M b p) := by
  have hab : ECtx.JEqB levels ∅ Γ A a b := .reflect ha hb hp
  have hId : ECtx.JEqB levels ∅ Γ (.univ k) (.id A a a) (.id A a a) := .id (by omega) hA ha ha
  have hPathType : ECtx.JEqB levels ∅ Γ (.univ k) (.id A a b) (.id A a a) := .id (by omega) hA ha (.symm hab)
  have hpAtA : ECtx.JEqB levels ∅ Γ (.id A a a) p p := .conv (by omega) hPathType hp
  have hPath : ECtx.JEqB levels ∅ Γ (.id A a a) (.refl a) p := .symm (.id_uip ha ha hpAtA)
  have hFirst : ECtx.JEqB levels ∅ Γ (.pi (.id A a a) (.univ n)) (.app M a) (.app M b) := by
    simpa only [motiveType, motiveFiber_lst] using ECtx.JEqB.app (by omega) hA hFiber hM hab
  have hIdLarge : ECtx.JEqB levels ∅ Γ (.univ (max k (n + 1))) (.id A a a) (.id A a a) :=
    .cumul (by omega) (Nat.le_max_left _ _) hId
  have hUniverse : ∀ x ∉ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x (.id A a a))
      (.univ (max k (n + 1))) (.univ n) (.univ n) := by
    intro x hx
    exact .cumul (by omega) (Nat.le_max_right _ _) (.univ (by omega) (.cons_ok (by omega) hΓ hx hId))
  have hCodomain : ∀ x ∉ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x (.id A a a))
      (.univ (max k (n + 1))) ((.univ n : ETm 1).open x)
        ((.univ n : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using hUniverse x hx
  simpa only [ETm.lst, value] using
    ECtx.JEqB.app (B := .univ n) (by omega) hIdLarge hCodomain hFirst hPath

theorem basedJ_congr {levels : ℕ} {Γ : ECtx} {A a b p M d d' : ETm 0} {n k : ℕ}
    {L : Finset String} (hlevels : max k (n + 1) < levels) (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqB levels ∅ Γ (motiveType A a n) M M)
    (ha : ECtx.JEqB levels ∅ Γ A a a) (hb : ECtx.JEqB levels ∅ Γ A b b)
    (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqB levels ∅ Γ (value M a (.refl a)) d d') :
    ECtx.JEqB levels ∅ Γ (value M b p) (basedJ d b p) (basedJ d' b p) := by
  exact .conv (by omega) (value_congr (by omega) hΓ hA hFiber hM ha hb hp) hd


theorem endpointId_formation {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {k : ℕ} (hk : k < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    {x : String} (hx : x ∉ Γ.dv) :
    ECtx.JEqB levels ∅ (Γ.cons x A) (.univ k) (.id A a (.fv x)) (.id A a (.fv x)) := by
  have hΓx : ECtx.JEqB levels ∅ (Γ.cons x A) .unit .star .star := .cons_ok (by omega) hA.context hx hA
  have e : Γ.Embeds (Γ.cons x A) := ECtx.Embeds.fresh hx A
  exact .id (by omega) (hA.weaken hΓx e) (ha.weaken hΓx e) (.var hΓx (.here _ _ _))

private theorem universe_family {levels : ℕ} {Γ : ECtx} {D : ETm 0} {k n : ℕ} (hlevels : max k (n + 1) < levels)
    (hD : ECtx.JEqB levels ∅ Γ (.univ k) D D) :
    ∀ y ∉ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons y D) (.univ (max k (n + 1)))
      ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
  intro y hy
  simpa only [ETm.open] using
    ECtx.JEqB.cumul (by omega) (Nat.le_max_right k (n + 1))
      (ECtx.JEqB.univ (n := n) (by omega) (.cons_ok (by omega) hD.context hy hD))

theorem motiveFiber_formation {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {k n : ℕ} (hlevels : max k (n + 1) < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a) :
    ∀ x ∉ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
  intro x hx
  have hId := endpointId_formation (by omega) hA ha hx
  simpa only [motiveFiber_open] using
    ECtx.JEqB.pi (by omega) (.cumul (by omega) (Nat.le_max_left k (n + 1)) hId) (universe_family (by omega) hId)

theorem motiveType_formation {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {k n : ℕ} (hlevels : max k (n + 1) < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a) :
    ECtx.JEqB levels ∅ Γ (.univ (max k (n + 1))) (motiveType A a n) (motiveType A a n) :=
  .pi (by omega) (.cumul (by omega) (Nat.le_max_left k (n + 1)) hA) (motiveFiber_formation (by omega) hA ha)

theorem packageBody_typing {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ∀ x ∉ L ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x A) ((motiveFiber A a n).open x)
      ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x)
      ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x) := by
  intro x hx
  have hs : x ∉ L ∧ x ∉ Γ.dv := Finset.notMem_union.mp hx
  have hId : ECtx.JEqB levels ∅ (Γ.cons x A) (.univ k)
      (.id A a (.fv x)) (.id A a (.fv x)) := endpointId_formation (by omega) hA ha hs.2
  have hU : ∀ y ∉ K x ∪ (Γ.cons x A).dv,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ (max k (n + 1)))
        ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
    intro y hy
    exact universe_family (by omega) hId y (Finset.notMem_union.mp hy).2
  have hC' : ∀ y ∉ K x ∪ (Γ.cons x A).dv,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x)))
        ((.univ n : ETm 1).open y) ((C.open x).open y) ((C.open x).open y) := by
    intro y hy
    simpa only [ETm.open] using hC x hs.1 y (Finset.notMem_union.mp hy).1
  simpa only [motiveFiber_open, packageBody_open] using
    ECtx.JEqB.abs (by omega) (.cumul (by omega) (Nat.le_max_left k (n + 1)) hId) hU hC'

theorem packageMotive_typing {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ECtx.JEqB levels ∅ Γ (motiveType A a n) (packageMotive A a C) (packageMotive A a C) := by
  have hFiber : ∀ x ∉ L ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
    intro x hx
    exact motiveFiber_formation (by omega) hA ha (x := x) (Finset.notMem_union.mp hx).2
  exact .abs (by omega) (.cumul (by omega) (Nat.le_max_left k (n + 1)) hA) hFiber (packageBody_typing (by omega) hA ha hC)

theorem instantiatedMotive_formation {levels : ℕ} {Γ : ECtx} {A a b : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hb : ECtx.JEqB levels ∅ Γ A b b)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ∃ N : Finset String, ∀ y ∉ N,
      ECtx.JEqB levels ∅ (Γ.cons y (.id A a b)) (.univ n)
        ((C.lst b).open y) ((C.lst b).open y) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ a.fvs ∪ C.fvs ∪ Γ.dv ∪ b.fvs)
  simp only [Finset.mem_union, not_or] at hx
  have hxL : x ∉ L := hx.1.1.1.1.1.1
  have hxΓ : x ∉ Γ.typeFvs := hx.1.1.1.1.1.2
  have hxA : x ∉ A.fvs := hx.1.1.1.1.2
  have hxa : x ∉ a.fvs := hx.1.1.1.2
  have hxC : x ∉ C.fvs := hx.1.1.2
  refine ⟨K x ∪ insert x (Γ.dv ∪ b.fvs), ?_⟩
  intro y hy
  have hyK : y ∉ K x := fun h => hy (Finset.mem_union_left _ h)
  have hyx : y ≠ x := by
    intro h
    subst y
    exact hy (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  have hyΓ : y ∉ Γ.dv :=
    fun h => hy (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
  have hId : ECtx.JEqB levels ∅ Γ (.univ k) (.id A a b) (.id A a b) := .id (by omega) hA ha hb
  have hΓy : ECtx.JEqB levels ∅ (Γ.cons y (.id A a b)) .unit .star .star :=
    .cons_ok (by omega) hA.context hyΓ hId
  let σ := Function.update ETm.fv x b
  have hTy : (ETm.id A a (.fv x)).fmap σ = .id A a b := by
    simp only [σ, ETm.fmap, ETm.fmap_update_fresh ETm.fv A x b hxA,
      ETm.fmap_update_fresh ETm.fv a x b hxa, ETm.fmap_id, Function.update_self, ETm.castLE_refl]
  have hctx : ECtx.JEqB levels ∅ (Γ.cons y ((ETm.id A a (.fv x)).fmap σ)) .unit .star .star := by
    simpa only [hTy] using hΓy
  have hb' : ECtx.JEqB levels ∅ Γ (A.fmap ETm.fv) b b := by
    simpa only [ETm.fmap_id] using hb
  have e₀ : ECtx.AssignmentB levels σ (Γ.cons x A) Γ :=
    ECtx.AssignmentB.update (ECtx.AssignmentB.identity hA.context) hxΓ hxA hb'
  have hσy : σ y = .fv y := Function.update_of_ne hyx _ _
  have e₁ : ECtx.AssignmentB levels σ ((Γ.cons x A).cons y (.id A a (.fv x)))
      (Γ.cons y ((ETm.id A a (.fv x)).fmap σ)) :=
    ECtx.AssignmentB.cons e₀ hσy hyΓ hctx
  have hσ : ETm.Supported σ (insert x ∅) :=
    ETm.Supported.update ETm.fv (fun _ _ => rfl) x b
  have hinst := (hC x hxL y hyK).assign σ (insert x ∅) hσ e₁ hctx
  rw [hTy] at hinst
  have hCmap : ((C.open x).open y).fmap σ = (C.lst b).open y := by
    rw [ETm.fmap_open σ _ hσy]
    change ((C.open x).fmap (Function.update ETm.fv x b)).open y = (C.lst b).open y
    rw [ETm.fmap_update_open ETm.fv C x b hxC, ETm.fmap_id]
  simpa only [hCmap, ETm.fmap] using hinst

theorem packageMotive_value {levels : ℕ} {Γ : ECtx} {A a b p : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqB levels ∅ Γ A b b) (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p) :
    ECtx.JEqB levels ∅ Γ (.univ n) (value (packageMotive A a C) b p) ((C.lst b).lst p) := by
  have hFiber : ∀ x ∉ L ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
    intro x hx
    exact motiveFiber_formation (by omega) hA ha (x := x) (Finset.notMem_union.mp hx).2
  have hFirst : ECtx.JEqB levels ∅ Γ (.pi (.id A a b) (.univ n))
      (.app (packageMotive A a C) b) (.abs (.id A a b) (C.lst b)) := by
    simpa only [packageMotive, motiveFiber_lst, packageBody_lst] using
      ECtx.JEqB.beta_app (by omega) (.cumul (by omega) (Nat.le_max_left k (n + 1)) hA)
        hFiber (packageBody_typing (by omega) hA ha hC) hb
  have hId : ECtx.JEqB levels ∅ Γ (.univ k) (.id A a b) (.id A a b) := .id (by omega) hA ha hb
  obtain ⟨N, hCN⟩ := instantiatedMotive_formation (by omega) hA ha hb hC
  have hU : ∀ y ∉ N ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons y (.id A a b))
      (.univ (max k (n + 1))) ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
    intro y hy
    exact universe_family (by omega) hId y (Finset.notMem_union.mp hy).2
  have hBody : ∀ y ∉ N ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons y (.id A a b))
      ((.univ n : ETm 1).open y) ((C.lst b).open y) ((C.lst b).open y) := by
    intro y hy
    simpa only [ETm.open] using hCN y (Finset.notMem_union.mp hy).1
  have hIdLarge := ECtx.JEqB.cumul (by omega) (Nat.le_max_left k (n + 1)) hId
  have hApp := ECtx.JEqB.app (by omega) hIdLarge hU hFirst hp
  have hBeta := ECtx.JEqB.beta_app (by omega) hIdLarge hU hBody hp
  simpa only [value, ETm.lst] using ECtx.JEqB.trans hApp hBeta

theorem directBasedJ_congr {levels : ℕ} {Γ : ECtx} {A a b p d d' : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqB levels ∅ Γ A b b) (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqB levels ∅ Γ ((C.lst a).lst (.refl a)) d d') :
    ECtx.JEqB levels ∅ Γ ((C.lst b).lst p) (basedJ d b p) (basedJ d' b p) := by
  have hBase : ECtx.JEqB levels ∅ Γ (value (packageMotive A a C) a (.refl a)) d d' :=
    .conv (by omega) (.symm (packageMotive_value (by omega) hA ha hC ha (.refl ha))) hd
  have hResult : ECtx.JEqB levels ∅ Γ (value (packageMotive A a C) b p)
      (basedJ d b p) (basedJ d' b p) :=
    basedJ_congr (by omega) hA.context (.cumul (by omega) (Nat.le_max_left k (n + 1)) hA)
      (motiveFiber_formation (by omega) hA ha) (packageMotive_typing (by omega) hA ha hC) ha hb hp hBase
  exact .conv (by omega) (packageMotive_value (by omega) hA ha hC hb hp) hResult


end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination
