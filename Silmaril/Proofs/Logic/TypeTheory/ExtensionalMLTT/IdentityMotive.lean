module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Motive.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationSubstitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Thms
import Mathlib.Data.Fintype.EquivFin

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

theorem open_wkn_outermost {k : ℕ} (t : ETm k) (x : String) : (t.wkn k).open x = t := by
  induction t with
  | fv y => simp only [ETm.wkn, ETm.open]
  | bv i => simp only [ETm.wkn, i.isLt, ↓reduceIte, ETm.open, Fin.lastCases_castSucc]
  | univ n => simp only [ETm.wkn, ETm.open]
  | empty => simp only [ETm.wkn, ETm.open]
  | unit => simp only [ETm.wkn, ETm.open]
  | star => simp only [ETm.wkn, ETm.open]
  | nats => simp only [ETm.wkn, ETm.open]
  | zero => simp only [ETm.wkn, ETm.open]
  | succ t ih => simpa only [ETm.wkn, ETm.open] using congrArg ETm.succ ih
  | natrec C s z t ihC ihs ihz iht => simp only [ETm.wkn, ETm.open, ihC, ihs, ihz, iht]
  | pi A B ihA ihB => simp only [ETm.wkn, ETm.open, ihA, ihB]
  | sigma A B ihA ihB => simp only [ETm.wkn, ETm.open, ihA, ihB]
  | abs A b ihA ihb => simp only [ETm.wkn, ETm.open, ihA, ihb]
  | app f a ihf iha => simp only [ETm.wkn, ETm.open, ihf, iha]
  | pair a b iha ihb => simp only [ETm.wkn, ETm.open, iha, ihb]
  | fst p ih => simpa only [ETm.wkn, ETm.open] using congrArg ETm.fst ih
  | snd p ih => simpa only [ETm.wkn, ETm.open] using congrArg ETm.snd ih
  | id A a b ihA iha ihb => simp only [ETm.wkn, ETm.open, ihA, iha, ihb]
  | refl a ih => simpa only [ETm.wkn, ETm.open] using congrArg ETm.refl ih
  | absurd A e ihA ihe => simp only [ETm.wkn, ETm.open, ihA, ihe]

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f 0 = a := rfl

theorem motiveFiber_open (A a : ETm 0) (n : ℕ) (x : String) :
    (motiveFiber A a n).open x = .pi (.id A a (.fv x)) (.univ n) := by
  simp only [motiveFiber, ETm.open, ETm.wk0, open_wkn_outermost, lastCases_zero]

theorem packageBody_open (A a : ETm 0) (C : ETm 2) (x : String) :
    ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x) =
      .abs (.id A a (.fv x)) (C.open x) := by
  simp only [ETm.open, ETm.wk0, open_wkn_outermost, lastCases_zero]

theorem packageBody_lst (A a b : ETm 0) (C : ETm 2) :
    ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).lst b) =
      .abs (.id A a b) (C.lst b) := by
  simp only [ETm.lst, ETm.wk0, lst_wkn_outermost, ETm.castLE_refl, lastCases_zero]

theorem endpointId_formation {Γ : ECtx} {A a : ETm 0} {k : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    {x : String} (hx : x ∉ Γ.dv) :
    ECtx.JEqH ∅ (Γ.cons x A) (.univ k) (.id A a (.fv x)) (.id A a (.fv x)) := by
  have hΓx : ECtx.JEqH ∅ (Γ.cons x A) .unit .star .star := .cons_ok hA.context hx hA
  have e : Γ.Embeds (Γ.cons x A) := ECtx.Embeds.fresh hx A
  exact .id (hA.weaken hΓx e) (ha.weaken hΓx e) (.var hΓx (.here _ _ _))

private theorem universe_family {Γ : ECtx} {D : ETm 0} {k n : ℕ}
    (hD : ECtx.JEqH ∅ Γ (.univ k) D D) :
    ∀ y ∉ Γ.dv, ECtx.JEqH ∅ (Γ.cons y D) (.univ (max k (n + 1)))
      ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
  intro y hy
  simpa only [ETm.open] using
    ECtx.JEqH.cumul (Nat.le_max_right k (n + 1))
      (ECtx.JEqH.univ (n := n) (.cons_ok hD.context hy hD))

theorem motiveFiber_formation {Γ : ECtx} {A a : ETm 0} {k n : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a) :
    ∀ x ∉ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
  intro x hx
  have hId := endpointId_formation hA ha hx
  simpa only [motiveFiber_open] using
    ECtx.JEqH.pi (.cumul (Nat.le_max_left k (n + 1)) hId) (universe_family hId)

theorem motiveType_formation {Γ : ECtx} {A a : ETm 0} {k n : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a) :
    ECtx.JEqH ∅ Γ (.univ (max k (n + 1))) (motiveType A a n) (motiveType A a n) :=
  .pi (.cumul (Nat.le_max_left k (n + 1)) hA) (motiveFiber_formation hA ha)

theorem packageBody_typing {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ∀ x ∉ L ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) ((motiveFiber A a n).open x)
      ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x)
      ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x) := by
  intro x hx
  have hs : x ∉ L ∧ x ∉ Γ.dv := Finset.notMem_union.mp hx
  have hId : ECtx.JEqH ∅ (Γ.cons x A) (.univ k)
      (.id A a (.fv x)) (.id A a (.fv x)) := endpointId_formation hA ha hs.2
  have hU : ∀ y ∉ K x ∪ (Γ.cons x A).dv,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ (max k (n + 1)))
        ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
    intro y hy
    exact universe_family hId y (Finset.notMem_union.mp hy).2
  have hC' : ∀ y ∉ K x ∪ (Γ.cons x A).dv,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x)))
        ((.univ n : ETm 1).open y) ((C.open x).open y) ((C.open x).open y) := by
    intro y hy
    simpa only [ETm.open] using hC x hs.1 y (Finset.notMem_union.mp hy).1
  simpa only [motiveFiber_open, packageBody_open] using
    ECtx.JEqH.abs (.cumul (Nat.le_max_left k (n + 1)) hId) hU hC'

theorem packageMotive_typing {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ECtx.JEqH ∅ Γ (motiveType A a n) (packageMotive A a C) (packageMotive A a C) := by
  have hFiber : ∀ x ∉ L ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
    intro x hx
    exact motiveFiber_formation hA ha (x := x) (Finset.notMem_union.mp hx).2
  exact .abs (.cumul (Nat.le_max_left k (n + 1)) hA) hFiber (packageBody_typing hA ha hC)

theorem instantiatedMotive_formation {Γ : ECtx} {A a b : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hb : ECtx.JEqH ∅ Γ A b b)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ∃ N : Finset String, ∀ y ∉ N,
      ECtx.JEqH ∅ (Γ.cons y (.id A a b)) (.univ n)
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
  have hId : ECtx.JEqH ∅ Γ (.univ k) (.id A a b) (.id A a b) := .id hA ha hb
  have hΓy : ECtx.JEqH ∅ (Γ.cons y (.id A a b)) .unit .star .star :=
    .cons_ok hA.context hyΓ hId
  have hTy : (ETm.id A a (.fv x)).fsubst x b = .id A a b := by
    simp only [ETm.fsubst, ite_true, ETm.castLE_refl,
      ETm.fsubst_fresh x b A hxA, ETm.fsubst_fresh x b a hxa]
  have hctx : ECtx.JEqH ∅ (Γ.cons y ((ETm.id A a (.fv x)).fsubst x b)) .unit .star .star := by
    simpa only [hTy] using hΓy
  have e₀ : ECtx.Subst x b (Γ.cons x A) Γ := ECtx.Subst.drop hA.context hb hxΓ hxA
  have e₁ : ECtx.Subst x b ((Γ.cons x A).cons y (.id A a (.fv x)))
      (Γ.cons y ((ETm.id A a (.fv x)).fsubst x b)) := ECtx.Subst.cons e₀ hyx hyΓ hctx
  rw [hTy] at e₁
  simpa only [ETm.fsubst, ETm.fsubst_open x b _ hyx,
    ETm.fsubst_open_self x b C hxC] using
    (hC x hxL y hyK).substitute x b _ e₁ hΓy

theorem packageMotive_value {Γ : ECtx} {A a b p : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqH ∅ Γ A b b) (hp : ECtx.JEqH ∅ Γ (.id A a b) p p) :
    ECtx.JEqH ∅ Γ (.univ n) (value (packageMotive A a C) b p) ((C.lst b).lst p) := by
  have hFiber : ∀ x ∉ L ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) := by
    intro x hx
    exact motiveFiber_formation hA ha (x := x) (Finset.notMem_union.mp hx).2
  have hFirst : ECtx.JEqH ∅ Γ (.pi (.id A a b) (.univ n))
      (.app (packageMotive A a C) b) (.abs (.id A a b) (C.lst b)) := by
    simpa only [packageMotive, motiveFiber_lst, packageBody_lst] using
      ECtx.JEqH.beta_app (.cumul (Nat.le_max_left k (n + 1)) hA)
        hFiber (packageBody_typing hA ha hC) hb
  have hId : ECtx.JEqH ∅ Γ (.univ k) (.id A a b) (.id A a b) := .id hA ha hb
  obtain ⟨N, hCN⟩ := instantiatedMotive_formation hA ha hb hC
  have hU : ∀ y ∉ N ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons y (.id A a b))
      (.univ (max k (n + 1))) ((.univ n : ETm 1).open y) ((.univ n : ETm 1).open y) := by
    intro y hy
    exact universe_family hId y (Finset.notMem_union.mp hy).2
  have hBody : ∀ y ∉ N ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons y (.id A a b))
      ((.univ n : ETm 1).open y) ((C.lst b).open y) ((C.lst b).open y) := by
    intro y hy
    simpa only [ETm.open] using hCN y (Finset.notMem_union.mp hy).1
  have hIdLarge := ECtx.JEqH.cumul (Nat.le_max_left k (n + 1)) hId
  have hApp := ECtx.JEqH.app hIdLarge hU hFirst hp
  have hBeta := ECtx.JEqH.beta_app hIdLarge hU hBody hp
  simpa only [value, ETm.lst] using ECtx.JEqH.trans hApp hBeta

theorem directBasedJ_congr {Γ : ECtx} {A a b p d d' : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqH ∅ Γ A b b) (hp : ECtx.JEqH ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqH ∅ Γ ((C.lst a).lst (.refl a)) d d') :
    ECtx.JEqH ∅ Γ ((C.lst b).lst p) (basedJ d b p) (basedJ d' b p) := by
  have hBase : ECtx.JEqH ∅ Γ (value (packageMotive A a C) a (.refl a)) d d' :=
    .conv (.symm (packageMotive_value hA ha hC ha (.refl ha))) hd
  have hResult : ECtx.JEqH ∅ Γ (value (packageMotive A a C) b p)
      (basedJ d b p) (basedJ d' b p) :=
    basedJ_congr hA.context (.cumul (Nat.le_max_left k (n + 1)) hA)
      (motiveFiber_formation hA ha) (packageMotive_typing hA ha hC) ha hb hp hBase
  exact .conv (packageMotive_value hA ha hC hb hp) hResult

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive
