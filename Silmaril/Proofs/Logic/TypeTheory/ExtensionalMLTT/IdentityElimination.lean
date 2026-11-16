module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- Removing an added outermost variable leaves every original constructor unchanged. -/
theorem lst_wkn_outermost {k : ℕ} (t : ETm k) (a : ETm 0) : (t.wkn k).lst a = t := by
  induction t with
  | fv x => simp only [ETm.wkn, ETm.lst]
  | bv i => simp only [ETm.wkn, i.isLt, ↓reduceIte, ETm.lst, Fin.lastCases_castSucc]
  | univ n => simp only [ETm.wkn, ETm.lst]
  | empty => simp only [ETm.wkn, ETm.lst]
  | unit => simp only [ETm.wkn, ETm.lst]
  | star => simp only [ETm.wkn, ETm.lst]
  | nats => simp only [ETm.wkn, ETm.lst]
  | zero => simp only [ETm.wkn, ETm.lst]
  | succ t ih => simpa only [ETm.wkn, ETm.lst] using congrArg ETm.succ ih
  | natrec C s z t ihC ihs ihz iht =>
    simp only [ETm.wkn, ETm.lst, ihC, ihs, ihz, iht]
  | pi A B ihA ihB => simp only [ETm.wkn, ETm.lst, ihA, ihB]
  | sigma A B ihA ihB => simp only [ETm.wkn, ETm.lst, ihA, ihB]
  | abs A b ihA ihb => simp only [ETm.wkn, ETm.lst, ihA, ihb]
  | app f a ihf iha => simp only [ETm.wkn, ETm.lst, ihf, iha]
  | pair a b iha ihb => simp only [ETm.wkn, ETm.lst, iha, ihb]
  | fst p ih => simpa only [ETm.wkn, ETm.lst] using congrArg ETm.fst ih
  | snd p ih => simpa only [ETm.wkn, ETm.lst] using congrArg ETm.snd ih
  | id A a b ihA iha ihb => simp only [ETm.wkn, ETm.lst, ihA, iha, ihb]
  | refl a ih => simpa only [ETm.wkn, ETm.lst] using congrArg ETm.refl ih
  | absurd A e ihA ihe => simp only [ETm.wkn, ETm.lst, ihA, ihe]

theorem castLE_refl {k : ℕ} (t : ETm k) (h : k ≤ k) : t.castLE h = t := by
  induction t with
  | fv x => rfl
  | bv i => rfl
  | univ n => rfl
  | empty => rfl
  | unit => rfl
  | star => rfl
  | nats => rfl
  | zero => rfl
  | succ t ih => exact congrArg ETm.succ (ih _)
  | natrec C s z t ihC ihs ihz iht => simp only [ETm.castLE, ihC, ihs, ihz, iht]
  | pi A B ihA ihB => simp only [ETm.castLE, ihA, ihB]
  | sigma A B ihA ihB => simp only [ETm.castLE, ihA, ihB]
  | abs A b ihA ihb => simp only [ETm.castLE, ihA, ihb]
  | app f a ihf iha => simp only [ETm.castLE, ihf, iha]
  | pair a b iha ihb => simp only [ETm.castLE, iha, ihb]
  | fst p ih => exact congrArg ETm.fst (ih _)
  | snd p ih => exact congrArg ETm.snd (ih _)
  | id A a b ihA iha ihb => simp only [ETm.castLE, ihA, iha, ihb]
  | refl a ih => exact congrArg ETm.refl (ih _)
  | absurd A e ihA ihe => simp only [ETm.castLE, ihA, ihe]

theorem motiveFiber_lst (A a b : ETm 0) (n : ℕ) :
    (motiveFiber A a n).lst b = .pi (.id A a b) (.univ n) := by
  simp only [motiveFiber, ETm.lst, ETm.wk0, lst_wkn_outermost, castLE_refl]
  rfl

theorem value_congr {H : Set EJdg} {Γ : ECtx} {A a b p M : ETm 0} {n k : ℕ}
    {L : Finset String} (hΓ : ECtx.JEqH H Γ .unit .star .star)
    (hA : ECtx.JEqH H Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqH H (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqH H Γ (motiveType A a n) M M)
    (ha : ECtx.JEqH H Γ A a a) (hb : ECtx.JEqH H Γ A b b)
    (hp : ECtx.JEqH H Γ (.id A a b) p p) :
    ECtx.JEqH H Γ (.univ n) (value M a (.refl a)) (value M b p) := by
  have hab : ECtx.JEqH H Γ A a b := .reflect ha hb hp
  have hId : ECtx.JEqH H Γ (.univ k) (.id A a a) (.id A a a) := .id hA ha ha
  have hPathType : ECtx.JEqH H Γ (.univ k) (.id A a b) (.id A a a) := .id hA ha (.symm hab)
  have hpAtA : ECtx.JEqH H Γ (.id A a a) p p := .conv hPathType hp
  have hPath : ECtx.JEqH H Γ (.id A a a) (.refl a) p := .symm (.id_uip ha ha hpAtA)
  have hFirst : ECtx.JEqH H Γ (.pi (.id A a a) (.univ n)) (.app M a) (.app M b) := by
    simpa only [motiveType, motiveFiber_lst] using ECtx.JEqH.app hA hFiber hM hab
  have hIdLarge : ECtx.JEqH H Γ (.univ (max k (n + 1))) (.id A a a) (.id A a a) :=
    .cumul (Nat.le_max_left _ _) hId
  have hUniverse : ∀ x ∉ Γ.dv, ECtx.JEqH H (Γ.cons x (.id A a a))
      (.univ (max k (n + 1))) (.univ n) (.univ n) := by
    intro x hx
    exact .cumul (Nat.le_max_right _ _) (.univ (.cons_ok hΓ hx hId))
  have hCodomain : ∀ x ∉ Γ.dv, ECtx.JEqH H (Γ.cons x (.id A a a))
      (.univ (max k (n + 1))) ((.univ n : ETm 1).open x)
        ((.univ n : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using hUniverse x hx
  simpa only [ETm.lst, value] using
    ECtx.JEqH.app (B := .univ n) hIdLarge hCodomain hFirst hPath

theorem basedJ_congr {H : Set EJdg} {Γ : ECtx} {A a b p M d d' : ETm 0} {n k : ℕ}
    {L : Finset String} (hΓ : ECtx.JEqH H Γ .unit .star .star)
    (hA : ECtx.JEqH H Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqH H (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqH H Γ (motiveType A a n) M M)
    (ha : ECtx.JEqH H Γ A a a) (hb : ECtx.JEqH H Γ A b b)
    (hp : ECtx.JEqH H Γ (.id A a b) p p)
    (hd : ECtx.JEqH H Γ (value M a (.refl a)) d d') :
    ECtx.JEqH H Γ (value M b p) (basedJ d b p) (basedJ d' b p) := by
  exact .conv (value_congr hΓ hA hFiber hM ha hb hp) hd

theorem basedJ_beta {H : Set EJdg} {Γ : ECtx} {M a d : ETm 0}
    (hd : ECtx.JEqH H Γ (value M a (.refl a)) d d) :
    ECtx.JEqH H Γ (value M a (.refl a)) (basedJ d a (.refl a)) d := hd

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f 0 = a := rfl

theorem unitFiber_formed {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ∀ x ∉ Γ.dv, ECtx.JEqH H (Γ.cons x .unit) (.univ 1)
      ((motiveFiber .unit .star 0).open x) ((motiveFiber .unit .star 0).open x) := by
  intro x hx
  have hΓx : ECtx.JEqH H (Γ.cons x .unit) .unit .star .star :=
    .cons_ok hΓ hx (.unit (n := 1) hΓ)
  have hId : ECtx.JEqH H (Γ.cons x .unit) (.univ 1)
      (.id .unit .star (.fv x)) (.id .unit .star (.fv x)) :=
    .id (.unit hΓx) hΓx (.var hΓx (.here _ _ _))
  have hU : ∀ y ∉ (Γ.cons x .unit).dv,
      ECtx.JEqH H ((Γ.cons x .unit).cons y (.id .unit .star (.fv x))) (.univ 1)
        ((.univ 0 : ETm 1).open y) ((.univ 0 : ETm 1).open y) := by
    intro y hy
    simpa only [ETm.open] using ECtx.JEqH.univ (n := 0) (.cons_ok hΓx hy hId)
  simpa only [motiveFiber, ETm.open, ETm.wk0, ETm.wkn, lastCases_zero] using ECtx.JEqH.pi hId hU

theorem unitMotive_body {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ∀ x ∉ Γ.dv, ECtx.JEqH H (Γ.cons x .unit)
      ((motiveFiber .unit .star 0).open x)
      ((.abs (.id .unit .star (.bv 0)) .unit : ETm 1).open x)
      ((.abs (.id .unit .star (.bv 0)) .unit : ETm 1).open x) := by
  intro x hx
  have hΓx : ECtx.JEqH H (Γ.cons x .unit) .unit .star .star :=
    .cons_ok hΓ hx (.unit (n := 1) hΓ)
  have hId : ECtx.JEqH H (Γ.cons x .unit) (.univ 1)
      (.id .unit .star (.fv x)) (.id .unit .star (.fv x)) :=
    .id (.unit hΓx) hΓx (.var hΓx (.here _ _ _))
  have hU : ∀ y ∉ (Γ.cons x .unit).dv,
      ECtx.JEqH H ((Γ.cons x .unit).cons y (.id .unit .star (.fv x))) (.univ 1)
        ((.univ 0 : ETm 1).open y) ((.univ 0 : ETm 1).open y) := by
    intro y hy
    simpa only [ETm.open] using ECtx.JEqH.univ (n := 0) (.cons_ok hΓx hy hId)
  have hUnit : ∀ y ∉ (Γ.cons x .unit).dv,
      ECtx.JEqH H ((Γ.cons x .unit).cons y (.id .unit .star (.fv x)))
        ((.univ 0 : ETm 1).open y) ((.unit : ETm 1).open y)
        ((.unit : ETm 1).open y) := by
    intro y hy
    simpa only [ETm.open] using ECtx.JEqH.unit (n := 0) (.cons_ok hΓx hy hId)
  simpa only [motiveFiber, ETm.open, ETm.wk0, ETm.wkn, lastCases_zero] using
    ECtx.JEqH.abs hId hU hUnit

theorem unitMotive_typing {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (motiveType .unit .star 0) unitMotive unitMotive :=
  ECtx.JEqH.abs (.unit hΓ) (unitFiber_formed hΓ) (unitMotive_body hΓ)

theorem unitMotive_value {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (.univ 0) (value unitMotive .star (.refl .star)) .unit := by
  have hFirst : ECtx.JEqH H Γ (.pi (.id .unit .star .star) (.univ 0))
      (.app unitMotive .star) (.abs (.id .unit .star .star) .unit) := by
    simpa only [motiveFiber_lst, unitMotive, ETm.lst, lastCases_zero, ETm.castLE] using
      ECtx.JEqH.beta_app (.unit (n := 1) hΓ) (unitFiber_formed hΓ) (unitMotive_body hΓ) hΓ
  have hId : ECtx.JEqH H Γ (.univ 1)
      (.id .unit .star .star) (.id .unit .star .star) := .id (.unit hΓ) hΓ hΓ
  have hU : ∀ x ∉ Γ.dv,
      ECtx.JEqH H (Γ.cons x (.id .unit .star .star)) (.univ 1)
        ((.univ 0 : ETm 1).open x) ((.univ 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using ECtx.JEqH.univ (n := 0) (.cons_ok hΓ hx hId)
  have hUnit : ∀ x ∉ Γ.dv,
      ECtx.JEqH H (Γ.cons x (.id .unit .star .star))
        ((.univ 0 : ETm 1).open x) ((.unit : ETm 1).open x)
        ((.unit : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using ECtx.JEqH.unit (n := 0) (.cons_ok hΓ hx hId)
  have hApp := ECtx.JEqH.app hId hU hFirst (ECtx.JEqH.refl hΓ)
  have hBeta := ECtx.JEqH.beta_app hId hU hUnit (ECtx.JEqH.refl hΓ)
  simpa only [value, ETm.lst] using ECtx.JEqH.trans hApp hBeta

theorem unitMotive_base {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (value unitMotive .star (.refl .star)) .star .star :=
  .conv (.symm (unitMotive_value hΓ)) hΓ

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
