module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Presented
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- Evaluating a closed term back into its constructor algebra retains its syntax. -/
theorem eval_closed_self {A : EQ.Signature} {s : A.S}
    (t : EQ.Term A (closedContext A) s) :
    t.eval (closedAlgebra A) (fun i => i.elim0) = t := by
  induction t with
  | var i => exact i.elim0
  | app op args ih => exact congrArg (EQ.Term.app op) (funext ih)

/-- Actual public algebra homomorphisms commute with evaluation in every context. -/
theorem eval_hom {A : EQ.Signature} {M N : EQ.Algebra A} (f : M ⟶ N)
    {k : Nat} {Γ : Fin k → A.S} (v : ∀ i, M.carrier (Γ i))
    {s : A.S} (t : EQ.Term A Γ s) :
    f.map s (t.eval M v) = t.eval N (fun i => f.map (Γ i) (v i)) := by
  induction t with
  | var i => rfl
  | app op args ih =>
    exact (f.map_op op _).trans (congrArg (N.op op) (funext ih))

/-- Every generated equality is valid under any assignment in any actual model
of the theory. No initiality or inhabitance premise is assumed. -/
theorem rel_sound {T : Theory} {k : Nat} {Γ : Fin k → T.sig.S}
    (M : Models T) (v : ∀ i, M.obj.carrier (Γ i))
    {s : T.sig.S} {a b : EQ.Term T.sig Γ s} (h : Rel T Γ a b) :
    a.eval M.obj v = b.eval M.obj v := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | app op a b _ ih => exact congrArg (M.obj.op op) (funext ih)
  | equation e he subst =>
    have hl := eval_hom (foldHom M.obj v) subst e.lhs
    have hr := eval_hom (foldHom M.obj v) subst e.rhs
    exact hl.trans ((M.property _ he (fun i => (subst i).eval M.obj v)).trans hr.symm)

/-- All complete quotient valuations lift to axiom instances, including contexts
whose declared variables do not occur in either side. -/
theorem algebra_models (T : Theory) {k : Nat} (Γ : Fin k → T.sig.S) :
    ∀ e ∈ T.axioms, e.down.Holds (algebra T Γ) := by
  intro lifted he v
  induction v using Quotient.induction_on_pi with
  | h a =>
    have h := Quotient.sound (s := setoid T Γ lifted.down.sort)
      (Rel.equation (T := T) (Γ := Γ) lifted.down he a)
    have hl := eval_hom (projection T Γ) a lifted.down.lhs
    have hr := eval_hom (projection T Γ) a lifted.down.rhs
    exact hl.symm.trans (h.trans hr)

/-- Evaluation descends to a genuine homomorphism into every theory model. -/
def foldHom {T : Theory} {k : Nat} {Γ : Fin k → T.sig.S} (M : Models T)
    (v : ∀ i, M.obj.carrier (Γ i)) : algebra T Γ ⟶ M.obj where
  map _ := Quotient.lift (fun t => t.eval M.obj v) (fun _ _ h => rel_sound M v h)
  map_op op args := by
    induction args using Quotient.induction_on_pi with
    | h a =>
      change _ = M.obj.op op (fun i => (a i).eval M.obj v)
      rw [op_mk T Γ op a]
      rfl

end Silmaril.Logic.Algebraic.Initial.Presented
