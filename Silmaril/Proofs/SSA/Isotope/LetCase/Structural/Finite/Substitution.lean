module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv HasType Pure Tm TypedSubst)
open Reply (Γ₀)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

variable {Φ : Type}

theorem Constructor.term_bsubst {n m : Nat} {A : Types} (v : Constructor A)
    (σ : Fin n → Term Φ m) : Tm.bsubst σ v.term = v.term := by
  induction v <;> simp [Constructor.term, *]

theorem Constructor.term_rename {n m : Nat} {A : Types} (v : Constructor A)
    (ρ : Fin n → Fin m) : Tm.rename ρ (v.term (Φ := Φ)) = v.term := by
  rw [← Tm.bsubst_bv_eq_rename, Constructor.term_bsubst]

theorem Constructor.pure {n : Nat} {A : Types} (v : Constructor A) :
    Pure false (v.term : Term Φ n) := by
  induction v with
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

variable [Signature Φ]

theorem Assignment.typed {n : Nat} {β : Context n} (ρ : Assignment β) :
    TypedSubst (Γ := Γ₀) β .nil (ρ.terms (Φ := Φ)) :=
  fun i => (ρ i).typing.toHasType

omit [Signature Φ] in
theorem instantiate_up {n m : Nat} (σ : Fin n → Term Φ m) (k : Term Φ (n + 1)) (v : Term Φ m) :
    Tm.instantiate (k.bsubst (Tm.upSub σ)) v = k.bsubst (Fin.cases v σ) := by
  rw [Tm.instantiate, Tm.bsubst_comp]
  apply Tm.bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, Tm.upSub_succ, Tm.lift, Tm.bsubst_rename]
  exact Tm.bsubst_id _

omit [Signature Φ] in
theorem Assignment.instantiate {n : Nat} {β : Context n} {A : Types}
    (ρ : Assignment β) (v : Constructor A) (k : Term Φ (n + 1)) :
    Tm.instantiate (k.bsubst (Tm.upSub ρ.terms)) v.term = k.bsubst (ρ.snoc v).terms := by
  rw [instantiate_up]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

omit [Signature Φ] in
theorem open_underBinder {n : Nat} (k : Term Φ (n + 1)) (v : Term Φ n) :
    (k.underBinder).bsubst (Tm.upSub (Fin.cases v (fun i => .bv i))) = k := by
  rw [Tm.underBinder, Tm.bsubst_rename]
  exact (Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k).trans (Tm.bsubst_id k)

omit [Signature Φ] in
theorem open_underTwoBinders {n : Nat} (k : Term Φ (n + 2)) (v : Term Φ n) :
    (k.underTwoBinders).bsubst (Tm.upSub (Tm.upSub (Fin.cases v (fun i => .bv i)))) = k := by
  rw [Tm.underTwoBinders, Tm.bsubst_rename]
  exact (Tm.bsubst_congr (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) k).trans (Tm.bsubst_id k)

omit [Signature Φ] in
theorem open_lift {n : Nat} (k v : Term Φ n) : Tm.instantiate k.lift v = k := by
  rw [Tm.instantiate, Tm.lift, Tm.bsubst_rename]
  exact Tm.bsubst_id _

/-- Product beta followed by two pure lets. The body can have effects. -/
theorem replay_constructor_pair {n : Nat} {β : Context n} {A B D : Types}
    {k : Term Φ (n + 2)} (ρ : Assignment β) (a : Constructor A) (b : Constructor B)
    (hk : HasType Φ Γ₀ ((β.snoc A).snoc B) k D) :
    Equiv false Γ₀ .nil
      (.let₂ (.pair a.term b.term) (k.bsubst (Tm.upSub (Tm.upSub ρ.terms))))
      (k.bsubst ((ρ.snoc a).snoc b).terms) D := by
  have typed : HasType Φ Γ₀ ((BoundCtx.nil.snoc A).snoc B)
      (k.bsubst (Tm.upSub (Tm.upSub ρ.terms))) D :=
    hk.bsubst (((ρ.typed (Φ := Φ)).up A).up B)
  have left : HasType Φ Γ₀ .nil a.term A := a.typing.toHasType
  have right : HasType Φ Γ₀ .nil b.term B := b.typing.toHasType
  have inner := Equiv.letBeta (pureEff := false) b.pure.lift right.lift typed
  have outer := Equiv.letBeta a.pure left inner.hasType.2
  have openBoth : Tm.instantiate (Tm.instantiate (k.bsubst (Tm.upSub (Tm.upSub ρ.terms)))
      b.term.lift) a.term = k.bsubst ((ρ.snoc a).snoc b).terms := by
    rw [instantiate_up, Tm.instantiate, Tm.bsubst_comp]
    apply Tm.bsubst_congr
    intro i
    refine Fin.cases ?_ (Fin.cases rfl (fun j => ?_)) i
    · simp only [Fin.cases_zero, Tm.lift, Tm.bsubst_rename]
      exact Tm.bsubst_id _
    · simp only [Fin.cases_succ, Tm.upSub_succ, Tm.lift, Tm.bsubst_rename]
      exact Tm.bsubst_id _
  rw [openBoth] at outer
  exact (Equiv.pairBeta left right typed).trans ((Equiv.let₁ (.refl left) inner).trans outer)

end Silmaril.Isotope.LetCase.Structural.Finite
