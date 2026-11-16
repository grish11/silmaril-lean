module

public import Silmaril.Logic.Algebraic.Lambda.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.Lambda
open Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

@[simp] theorem envTuple_contextVar {B : Type} {n : Nat} (w : Fin n → B)
    (X : Ty B → Type) (ρ : ∀ i, X (.base (w i))) (i : Fin n) :
    envTuple w X ρ _ (contextVar w i) = ρ i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun i => w i.succ) (fun i => ρ i.succ) j

theorem envTuple_eta {B : Type} {n : Nat} (w : Fin n → B)
    (X : Ty B → Type) (ρ : Tuple X (context w)) :
    envTuple w X (fun i => ρ _ (contextVar w i)) = ρ := by
  induction n with
  | zero => exact Tuple.ext fun _ v => v.elim
  | succ n ih =>
      apply Tuple.ext
      intro a v
      cases v with
      | zero => rfl
      | succ v =>
          exact congrFun (congrFun (ih (fun i => w i.succ)
            (fun a v => ρ a (.succ v))) _) v

theorem envTuple_map {B : Type} {n : Nat} (w : Fin n → B)
    (X Y : Ty B → Type) (f : ∀ a, X a → Y a) (ρ : ∀ i, X (.base (w i))) :
    (fun a v => f a (envTuple w X ρ a v)) = envTuple w Y (fun i => f _ (ρ i)) := by
  induction n with
  | zero => exact Tuple.ext fun _ v => v.elim
  | succ n ih =>
      apply Tuple.ext
      intro a v
      cases v with
      | zero => rfl
      | succ v => exact congrFun (congrFun (ih (fun i => w i.succ) (fun i => ρ i.succ)) _) v

theorem eval_term {A : EQ.Signature} (M : STLC.SetModel (signature A))
    {n : Nat} {Γ : Fin n → A.S} {s : A.S} (t : EQ.Term A Γ s)
    (ρ : ∀ i, M.base (Γ i)) :
    STLC.eval M (term t) (envTuple Γ (STLC.carrier M.base) ρ) =
      t.eval (reduct M) ρ := by
  induction t with
  | var i => exact envTuple_contextVar _ _ _ _
  | app o args ih =>
      simp only [term, STLC.eval, EQ.Term.eval, reduct]
      rw [envTuple_map _ _ _ (fun _ t => STLC.eval M t (envTuple Γ (STLC.carrier M.base) ρ))]
      exact congrArg (fun values => M.op (.original o)
        (envTuple _ (STLC.carrier M.base) values)) (funext ih)

theorem satisfies_equation {A : EQ.Signature} (M : STLC.SetModel (signature A))
    (e : EQ.Equation A) : STLC.Sat M (equation e) ↔ e.Holds (reduct M) := by
  change (∀ ρ, STLC.eval M (term e.lhs) ρ = STLC.eval M (term e.rhs) ρ) ↔ _
  constructor
  · intro h ρ
    exact (eval_term M e.lhs ρ).symm.trans
      ((h (envTuple e.ctx (STLC.carrier M.base) ρ)).trans (eval_term M e.rhs ρ))
  · intro h ρ
    have hr := h (fun i => ρ _ (contextVar e.ctx i))
    have hl := eval_term M e.lhs (fun i => ρ _ (contextVar e.ctx i))
    have hu := eval_term M e.rhs (fun i => ρ _ (contextVar e.ctx i))
    rw [envTuple_eta e.ctx (STLC.carrier M.base) ρ] at hl hu
    exact hl.trans (hr.trans hu.symm)

theorem reduct_expand {A : EQ.Signature} (M : EQ.Algebra A) : reduct (expand M) = M := by
  cases M with
  | mk carrier op =>
      simp only [reduct, expand]
      congr
      funext n w s o args
      congr 1
      funext i
      exact envTuple_contextVar _ _ _ _

end Silmaril.Logic.Algebraic.Lambda
