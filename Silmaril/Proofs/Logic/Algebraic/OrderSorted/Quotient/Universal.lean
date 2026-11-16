module

public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Models

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Algebraic.Initial.Presented (eval_hom)

/-- The reflection step is sound specifically because every target model has
injective coercions; all other steps use actual operation/equation preservation. -/
theorem rel_sound {T : Initial.Theory} {k : Nat} {Γ : Fin k → T.sig.base.S}
    (M : Initial.Models T) (v : ∀ i, M.obj.algebra.carrier (Γ i))
    {s : T.sig.base.S} {a b : Free.Normal T.sig Γ s} (h : Rel T Γ a b) :
    Free.eval M.obj v a = Free.eval M.obj v b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | op o a b _ ih =>
    have hl := (Free.foldHom M.obj v).map_op o a
    have hr := (Free.foldHom M.obj v).map_op o b
    exact hl.trans ((congrArg (M.obj.algebra.op o) (funext ih)).trans hr.symm)
  | equation e he subst =>
    have hl := eval_hom (Free.foldHom M.obj v) subst e.lhs
    have hr := eval_hom (Free.foldHom M.obj v) subst e.rhs
    exact hl.trans ((M.property _ he (fun i => Free.eval M.obj v (subst i))).trans hr.symm)
  | reflect h _ ih =>
    apply M.obj.coherent.injective h
    exact (Free.eval_coerce M.obj v h _).symm.trans
      (ih.trans (Free.eval_coerce M.obj v h _))

/-- Every axiom holds under every complete quotient valuation, with no
inhabitance premise on any sort. -/
theorem model_models (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S) :
    ∀ e ∈ T.axioms, Satisfies (coherentModel T Γ) e.down := by
  intro lifted he v
  induction v using Quotient.induction_on_pi with
  | h a =>
    have h := Quotient.sound (s := setoid T Γ lifted.down.sort)
      (Rel.equation (T := T) (Γ := Γ) lifted.down he a)
    have hl := eval_hom (projection T Γ) a lifted.down.lhs
    have hr := eval_hom (projection T Γ) a lifted.down.rhs
    exact hl.symm.trans (h.trans hr)

def foldHom {T : Initial.Theory} {k : Nat} {Γ : Fin k → T.sig.base.S}
    (M : Initial.Models T) (v : ∀ i, M.obj.algebra.carrier (Γ i)) :
    coherentModel T Γ ⟶ M.obj where
  map _ := Quotient.lift (Free.eval M.obj v) (fun _ _ h => rel_sound M v h)
  map_op o args := by
    induction args using Quotient.induction_on_pi with
    | h a =>
      change Quotient.lift (Free.eval M.obj v) _
        ((algebra T Γ).op o (fun i => Quotient.mk _ (a i))) =
        M.obj.algebra.op o (fun i => Free.eval M.obj v (a i))
      rw [op_mk T Γ o a]
      exact (Free.foldHom M.obj v).map_op o a

end Silmaril.Logic.Algebraic.OrderSorted.Presented
