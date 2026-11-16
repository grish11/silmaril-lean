module

public import Silmaril.Logic.Algebraic.ManySorted.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
variable {S : Type} {A : Signature S} {k l : Nat}
    {Γ : Fin k → S} {Δ : Fin l → S}

/-- Simultaneous, capture-free substitution respects each variable's sort. -/
def Term.subst (σ : ∀ i, Term A Δ (Γ i)) {s : S} : Term A Γ s → Term A Δ s
  | .var i => σ i
  | .app op args => .app op (fun i => subst σ (args i))

theorem Term.subst_var {s} (t : Term A Γ s) :
    t.subst (fun i => .var i) = t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app op) (funext ih)

theorem Model.eval_subst (M : Model A) (v : ∀ i, M.carrier (Δ i))
    (σ : ∀ i, Term A Δ (Γ i)) {s} (t : Term A Γ s) :
    M.eval v (t.subst σ) = M.eval (fun i => M.eval v (σ i)) t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (M.operation op) (funext ih)

/-- A universally valid identity remains valid after sorted substitution. -/
theorem substitution_preserves_identity (M : Model A) {s} (lhs rhs : Term A Γ s)
    (valid : ∀ v : (i : Fin k) → M.carrier (Γ i), M.eval v lhs = M.eval v rhs)
    (σ : ∀ i, Term A Δ (Γ i)) (v : ∀ i, M.carrier (Δ i)) :
    M.eval v (lhs.subst σ) = M.eval v (rhs.subst σ) := by
  rw [M.eval_subst, M.eval_subst]
  exact valid _
end Silmaril.Logic.Algebraic.ManySorted

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
variable {S : Type} {A : Signature S}

/-- A nullary symbol forces its result carrier to be inhabited, even when other sorts are empty. -/
theorem Model.nonempty_of_nullary (M : Model A) {s : S}
    (op : A.operations 0 Fin.elim0 s) : Nonempty (M.carrier s) :=
  ⟨M.operation op (fun i => nomatch i)⟩

/-- The usual singleton algebra exists for every pure operation signature. -/
def Model.trivial (A : Signature S) : Model A :=
  ⟨fun _ => PUnit, fun _ _ => PUnit.unit⟩

theorem Equation.trivial_satisfies (e : Equation A) :
    Equation.Satisfies (Model.trivial A) e := by
  intro v
  exact @Subsingleton.elim PUnit inferInstance _ _
end Silmaril.Logic.Algebraic.ManySorted

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory
variable {S : Type} {A B : Signature S} {k l m : Nat}
    {Γ : Fin k → S} {Δ : Fin l → S} {Ξ : Fin m → S}

theorem Term.subst_comp (σ : ∀ i, Term A Δ (Γ i)) (τ : ∀ i, Term A Ξ (Δ i))
    {s} (t : Term A Γ s) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app op) (funext ih)

theorem Term.map_subst (f : A ⟶ B) (σ : ∀ i, Term A Δ (Γ i))
    {s} (t : Term A Γ s) :
    Term.map f (t.subst σ) = (Term.map f t).subst (fun i => Term.map f (σ i)) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app (f.operations op)) (funext ih)
end Silmaril.Logic.Algebraic.ManySorted
