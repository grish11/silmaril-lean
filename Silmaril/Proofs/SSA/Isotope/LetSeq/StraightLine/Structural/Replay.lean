module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Binders.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv HasType Pure Tm TypedSubst)
open scoped Structural

variable {α Φ : Type} [Signature α Φ]
open Binders

set_option backward.isDefEq.respectTransparency false

omit [Signature α Φ] in
theorem Assembly.term_rename {n m : Nat} {β : Context α n} {γ : Context α m}
    {A : Ty α} (ρ : BoundCtx.Renaming β γ) (a : Assembly β A) :
    (a.rename ρ).term (Φ := Φ) = (a.term (Φ := Φ)).rename ρ.toFun := by
  induction a with
  | atom | unit => rfl
  | pair _ _ iha ihb => simp only [Assembly.rename, Assembly.term, Tm.rename, iha, ihb]

omit [Signature α Φ] in
theorem Assembly.pure {n : Nat} {β : Context α n} {A : Ty α} (v : Assembly β A) :
    Pure false (v.term (Φ := Φ)) := by
  induction v with
  | atom => exact .bv
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb

theorem AssemblyEnv.typed {n m : Nat} {β : Context α n} {γ : Context α m}
    (σ : AssemblyEnv β γ) : TypedSubst (Γ := Γ₀) β γ (σ.terms (Φ := Φ)) :=
  fun i => (σ i).derivation.toHasType

omit [Signature α Φ] in
theorem Split.wrap_append {n m k : Nat} {β : Context α n} {γ : Context α m} {δ : Context α k}
    (p : Split β γ) (q : Split γ δ) (t : Term Φ k) : (p.append q).wrap t = p.wrap (q.wrap t) := by
  induction p with
  | nil => rfl
  | pair _ _ ih => simp only [Split.append, Split.wrap, ih]

theorem Split.congr {n m : Nat} {β : Context α n} {γ : Context α m} {t u : Term Φ m} {A : Ty α}
    (p : Split β γ) (h : Equiv false Γ₀ γ t u A) : Equiv false Γ₀ β (p.wrap t) (p.wrap u) A := by
  induction p with
  | nil => exact h
  | pair s _ ih => exact .let₂ (.refl s.derivation.toHasType) (ih h)

private theorem weaken_cont {n : Nat} (t : Term Φ (n + 1)) :
    t.underBinder.underBinder = t.rename (Tm.up (fun i => i.succ.succ)) := by
  rw [Tm.underBinder, Tm.underBinder, Tm.rename_comp]
  exact Tm.rename_congr (Fin.cases rfl (fun _ => rfl)) t

theorem Split.bind {n m : Nat} {β : Context α n} {γ : Context α m}
    {t : Term Φ m} {k : Term Φ (n + 1)} {A B : Ty α} (p : Split β γ)
    (d : Derivation Φ Γ₀ γ t A) (h : HasType Φ Γ₀ (β.snoc A) k B) :
    Equiv false Γ₀ β (.let₁ (p.wrap t) k) (p.wrap (.let₁ t (k.rename (Tm.up p.rename.toFun)))) B := by
  induction p with
  | nil =>
    simp only [Split.wrap, Split.rename, BoundCtx.Renaming.id, Tm.up_id, Tm.rename_id]
    exact .refl (.let₁ d.toHasType h)
  | pair s next ih =>
    have commute := Equiv.bindLetPair (pureEff := false) s.derivation.toHasType
      (next.derivation d).toHasType h
    have inner := ih d h.underBinder.underBinder
    rw [weaken_cont, Tm.rename_comp, ← Tm.up_comp, ← weaken_cont k] at inner
    exact commute.trans (.let₂ (.refl s.derivation.toHasType) inner)

omit [Signature α Φ] in
theorem instantiate_assembly {n m : Nat} {β : Context α n} {γ : Context α m} {A : Ty α}
    (σ : AssemblyEnv β γ) (k : Term Φ (n + 1)) (a : Assembly γ A) :
    Tm.instantiate (k.bsubst (Tm.upSub σ.terms)) a.term = k.bsubst (σ.extend a).terms := by
  rw [instantiate_bsubst_up]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

theorem replay_pair {n m : Nat} {β : Context α n} {γ : Context α m} {A B C : Ty α}
    {k : Term Φ (n + 2)} (σ : AssemblyEnv β γ) (a : Assembly γ A) (b : Assembly γ B)
    (h : HasType Φ Γ₀ ((β.snoc A).snoc B) k C) :
    Equiv false Γ₀ γ (.let₂ (.pair a.term b.term) (k.bsubst (Tm.upSub (Tm.upSub σ.terms))))
      (k.bsubst ((σ.extend a).extend b).terms) C := by
  have body := h.bsubst (((σ.typed (Φ := Φ)).up A).up B)
  have ta := (a.derivation (Φ := Φ)).toHasType
  have tb := (b.derivation (Φ := Φ)).toHasType
  have inner := Equiv.letBeta b.pure.lift tb.lift body
  have outer := Equiv.letBeta a.pure ta inner.hasType.2
  have openBoth : Tm.instantiate (Tm.instantiate (k.bsubst (Tm.upSub (Tm.upSub σ.terms))) b.term.lift)
      a.term = k.bsubst ((σ.extend a).extend b).terms := by
    rw [instantiate_bsubst_up, Tm.instantiate, Tm.bsubst_comp]
    apply Tm.bsubst_congr
    intro i
    refine Fin.cases ?_ (Fin.cases rfl (fun j => ?_)) i
    · simp only [Fin.cases_zero, Tm.lift, Tm.bsubst_rename]
      exact Tm.bsubst_id _
    · simp only [Fin.cases_succ, Tm.upSub_succ, Tm.lift, Tm.bsubst_rename]
      exact Tm.bsubst_id _
  rw [openBoth] at outer
  exact (Equiv.pairBeta ta tb body).trans ((Equiv.let₁ (.refl ta) inner).trans outer)

theorem pair_lets {n : Nat} {β : Context α n} {a b : Term Φ n} {A B : Ty α}
    (ha : HasType Φ Γ₀ β a A) (hb : HasType Φ Γ₀ β b B) :
    Equiv false Γ₀ β (.pair a b) (.let₁ a (.let₁ b.lift (.pair (.bv 1) (.bv 0)))) (.product A B) :=
  (Equiv.pairEta (.pair ha hb)).symm.trans (Equiv.pairBeta ha hb (.pair .bv .bv))

/-- Native replay of the structural unfolding of a bound variable. -/
theorem unpack_eta {n : Nat} {β : Context α n} (s : Shape α) (slot : Slot β s.ty) :
    Equiv false Γ₀ β (.bv slot.1 : Term Φ n)
      ((s.unpack slot).split.wrap (s.unpack slot).value.term) s.ty := by
  induction s generalizing n with
  | atom a => exact .refl slot.derivation.toHasType
  | unit =>
    exact (Equiv.unitEta slot.derivation.toHasType).symm.trans
      (Equiv.letBeta .bv slot.derivation.toHasType .unit)
  | pair a b iha ihb =>
    let γ := (β.snoc a.ty).snoc b.ty
    let l := a.unpack (β := γ) ⟨1, rfl⟩
    let right : Slot γ b.ty := ⟨0, rfl⟩
    let r := b.unpack (right.rename l.split.rename)
    change Equiv false Γ₀ β (.bv slot.1)
      (.let₂ (.bv slot.1) ((l.split.append r.split).wrap (.pair
        (l.value.rename r.split.rename).term r.value.term))) (.product a.ty b.ty)
    rw [Split.wrap_append]
    apply (Equiv.pairEta slot.derivation.toHasType).symm.trans
    apply Equiv.let₂ (.refl slot.derivation.toHasType)
    apply (Equiv.pair (iha (β := γ) ⟨1, rfl⟩) (.refl right.derivation.toHasType)).trans
    have leftType := (l.split.derivation (l.value.derivation (Φ := Φ))).toHasType
    apply (pair_lets leftType right.derivation.toHasType).trans
    apply (l.split.bind l.value.derivation (HasType.let₁ right.derivation.toHasType.lift
      (HasType.pair .bv .bv))).trans
    apply l.split.congr
    have newRight := (right.rename l.split.rename).derivation (Φ := Φ)
    have newLeft := l.value.derivation (Φ := Φ)
    have pairTyped : HasType Φ Γ₀ ((l.context.snoc a.ty).snoc b.ty)
        (.pair (.bv 1) (.bv 0)) (.product a.ty b.ty) := .pair .bv .bv
    have push := Equiv.letBeta l.value.pure newLeft.toHasType
      (HasType.let₁ newRight.toHasType.lift pairTyped)
    have opened := open_left_pair (Φ := Φ) (.bv right.1) l.value.term l.split.rename.toFun
    have pushTerm : Tm.instantiate (.let₁ (Tm.lift (.bv (right.rename l.split.rename).1))
        (.pair (.bv 1) (.bv 0))) (l.value.term (Φ := Φ)) =
        .let₁ (.bv (right.rename l.split.rename).1) (.pair l.value.term.lift (.bv 0)) := opened
    rw [pushTerm] at push
    apply push.trans
    have rightEta := ihb (right.rename l.split.rename)
    have assemble : HasType Φ Γ₀ (l.context.snoc b.ty) (.pair l.value.term.lift (.bv 0))
        (.product a.ty b.ty) := .pair newLeft.toHasType.lift .bv
    have step := Equiv.let₁ rightEta (.refl assemble)
    apply step.trans
    apply (r.split.bind r.value.derivation assemble).trans
    apply r.split.congr
    have moved := assemble.rename (r.split.rename.up b.ty)
    have last := Equiv.letBeta r.value.pure (r.value.derivation (Φ := Φ)).toHasType moved
    change Equiv false Γ₀ r.context _ (Tm.instantiate
      ((Tm.pair l.value.term.lift (.bv 0)).rename (Tm.up r.split.rename.toFun)) r.value.term) _ at last
    rw [open_right_pair, ← Assembly.term_rename] at last
    exact last

end Silmaril.Isotope.LetSeq.StraightLine.Structural
