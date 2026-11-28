module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Isotope.LetCase.LocallyNameless (Equiv HasType Pure PureTypedSubst Tm)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)
local notation "Term" => Tm Empty signature.Instr

theorem instantiate_lift {k : Nat} (t a : Term k) : Tm.instantiate t.lift a = t := by
  unfold Tm.instantiate Tm.lift
  rw [Tm.bsubst_rename]
  exact Tm.bsubst_id t

theorem instantiate_up {k m : Nat} (t : Term (k + 1)) (σ : Fin k → Term m) (a : Term m) :
    (t.bsubst (Tm.upSub σ)).instantiate a = t.bsubst (Fin.cases a σ) := by
  unfold Tm.instantiate
  rw [Tm.bsubst_comp]
  apply Tm.bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact instantiate_lift (σ j) a

private theorem unit_slot {k : Nat} (β : BoundCtx Sorts k) :
    Equiv false Γ₀ (β.snoc U) (.bv 0 : Term (k + 1)) .unit U := by
  let d : HasType signature.Instr Γ₀ (β.snoc U) (.bv 0) U := .bv
  exact (Equiv.unitEta d).symm.trans (Equiv.letBeta .bv d .unit)

private theorem instantiate_id {k : Nat} (t : Term (k + 1)) :
    Tm.instantiate t.underBinder (.bv 0) = t := by
  unfold Tm.instantiate Tm.underBinder
  rw [Tm.bsubst_rename]
  apply (Tm.bsubst_congr _ t).trans (Tm.bsubst_id t)
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem instantiate_branch {k : Nat} (t : Term (k + 1)) (a : Term k) :
    Tm.instantiate t.underBinder.underBinder a.lift.lift = (Tm.instantiate t a).lift.lift := by
  unfold Tm.instantiate Tm.underBinder Tm.lift
  rw [Tm.rename_comp, Tm.bsubst_rename, Tm.bsubst_rename, Tm.rename_bsubst, Tm.rename_bsubst]
  simp only [Tm.rename_comp]
  apply Tm.bsubst_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

theorem bit_cover_proof {k : Nat} {β : BoundCtx Sorts k} {A : Sorts} {t : Term (k + 1)}
    (ht : HasType signature.Instr Γ₀ (β.snoc Bit) t A) :
    Equiv false Γ₀ (β.snoc Bit) t
      (.case (.bv 0)
        (Tm.instantiate t (.inl .unit)).lift.lift (Tm.instantiate t (.inr .unit)).lift.lift) A := by
  let γ := β.snoc Bit
  let v : HasType signature.Instr Γ₀ γ (.bv 0) Bit := .bv
  have forget := Equiv.letBeta (pureEff := false) .bv v ht.underBinder
  rw [instantiate_id] at forget
  let l : HasType signature.Instr Γ₀ (γ.snoc U) (.inl (.bv 0)) Bit := .inl .bv
  let r : HasType signature.Instr Γ₀ (γ.snoc U) (.inr (.bv 0)) Bit := .inr .bv
  have eta := Equiv.let₁ (Equiv.caseEta (pureEff := false) v).symm (.refl ht.underBinder)
  have distribute := Equiv.bindLetCase (pureEff := false) v l r ht.underBinder
  have payload := unit_slot γ
  let body : HasType signature.Instr Γ₀ ((γ.snoc U).snoc Bit) t.underBinder.underBinder A :=
    ht.underBinder.underBinder
  have low : Equiv false Γ₀ (γ.snoc U) (.let₁ (.inl (.bv 0)) t.underBinder.underBinder)
      (Tm.instantiate t (.inl .unit)).lift.lift A := by
    have reduce := Equiv.letBeta (pureEff := false) (.inl .unit) (.inl .unit) body
    change Equiv false Γ₀ (γ.snoc U) (.let₁ (.inl .unit) t.underBinder.underBinder)
      (Tm.instantiate t.underBinder.underBinder ((.inl .unit : Term k).lift.lift)) A at reduce
    rw [instantiate_branch] at reduce
    exact (Equiv.let₁ (.inl payload) (.refl body)).trans reduce
  have high : Equiv false Γ₀ (γ.snoc U) (.let₁ (.inr (.bv 0)) t.underBinder.underBinder)
      (Tm.instantiate t (.inr .unit)).lift.lift A := by
    have reduce := Equiv.letBeta (pureEff := false) (.inr .unit) (.inr .unit) body
    change Equiv false Γ₀ (γ.snoc U) (.let₁ (.inr .unit) t.underBinder.underBinder)
      (Tm.instantiate t.underBinder.underBinder ((.inr .unit : Term k).lift.lift)) A at reduce
    rw [instantiate_branch] at reduce
    exact (Equiv.let₁ (.inr payload) (.refl body)).trans reduce
  exact forget.symm.trans (eta.trans (distribute.trans (.case (.refl v) low high)))

theorem bit_ext_proof {k : Nat} {β : BoundCtx Sorts k} {A : Sorts} {t u : Term (k + 1)}
    (ht : HasType signature.Instr Γ₀ (β.snoc Bit) t A)
    (hu : HasType signature.Instr Γ₀ (β.snoc Bit) u A)
    (lo : Equiv false Γ₀ β (t.instantiate (.inl .unit)) (u.instantiate (.inl .unit)) A)
    (hi : Equiv false Γ₀ β (t.instantiate (.inr .unit)) (u.instantiate (.inr .unit)) A) :
    Equiv false Γ₀ (β.snoc Bit) t u A :=
  (bit_cover_proof ht).trans ((Equiv.case (.refl .bv) lo.lift.lift hi.lift.lift).trans (bit_cover_proof hu).symm)

theorem bit_pure {k : Nat} (β : BoundCtx Sorts k) (b : Bool) :
    Pure false (bitOperand β b).1 := by
  cases b
  · exact .inl .unit
  · exact .inr .unit

theorem literal_lift {k : Nat} (β : BoundCtx Sorts k) (A : Sorts) (b : Bool) :
    (bitOperand β b).1.lift = (bitOperand (β.snoc A) b).1 := by cases b <;> rfl

theorem literal_bsubst {k m : Nat} (β : BoundCtx Sorts k) (γ : BoundCtx Sorts m)
    (σ : Fin k → Term m) (b : Bool) :
    (bitOperand β b).1.bsubst σ = (bitOperand γ b).1 := by cases b <;> rfl

private theorem assignment_push_subst {n : Nat} (env : Assignment n) (b : Bool) :
    (fun i => Tm.bsubst (literalSubst .nil env) (Fin.cases (bitOperand (CommonRequest.bitCtx n) b).1
      (fun j => .bv j) i)) = literalSubst .nil (env.push b) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact literal_bsubst _ _ _ b

theorem assignments_ext_proof {n : Nat} {A : Sorts} {t u : Term n}
    (ht : HasType signature.Instr Γ₀ (CommonRequest.bitCtx n) t A)
    (hu : HasType signature.Instr Γ₀ (CommonRequest.bitCtx n) u A)
    (all : ∀ env : Assignment n,
      Equiv false Γ₀ .nil (t.bsubst (literalSubst .nil env)) (u.bsubst (literalSubst .nil env)) A) :
    Equiv false Γ₀ (CommonRequest.bitCtx n) t u A := by
  induction n with
  | zero =>
    have empty (env : Assignment 0) : literalSubst .nil env = (Tm.bv : Fin 0 → Term 0) :=
      funext fun i => i.elim0
    simpa only [CommonRequest.bitCtx, empty, Tm.bsubst_id] using all Fin.elim0
  | succ n ih =>
    apply bit_ext_proof ht hu
    · have low : HasType signature.Instr Γ₀ (CommonRequest.bitCtx n) (.inl .unit : Term n) Bit :=
        .inl .unit
      apply ih (ht.instantiate low) (hu.instantiate low)
      intro env
      change Equiv false Γ₀ .nil
        ((t.instantiate (bitOperand (CommonRequest.bitCtx n) false).1).bsubst (literalSubst .nil env))
        ((u.instantiate (bitOperand (CommonRequest.bitCtx n) false).1).bsubst (literalSubst .nil env)) A
      rw [Tm.instantiate, Tm.instantiate, Tm.bsubst_comp, Tm.bsubst_comp, assignment_push_subst]
      exact all (env.push false)
    · have high : HasType signature.Instr Γ₀ (CommonRequest.bitCtx n) (.inr .unit : Term n) Bit :=
        .inr .unit
      apply ih (ht.instantiate high) (hu.instantiate high)
      intro env
      change Equiv false Γ₀ .nil
        ((t.instantiate (bitOperand (CommonRequest.bitCtx n) true).1).bsubst (literalSubst .nil env))
        ((u.instantiate (bitOperand (CommonRequest.bitCtx n) true).1).bsubst (literalSubst .nil env)) A
      rw [Tm.instantiate, Tm.instantiate, Tm.bsubst_comp, Tm.bsubst_comp, assignment_push_subst]
      exact all (env.push true)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
