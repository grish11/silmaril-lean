module

public import Silmaril.Logic.Smt.Uflia.Quantified.Variables

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
variable {U : Type} {A : Signature U}

/-- A parallel substitution assigns one correctly sorted target term to each
source variable. Images are inserted simultaneously, not substituted again. -/
abbrev Substitution (A : Signature U) {k l : Nat}
    (Γ : Fin k → SortCode U) (Δ : Fin l → SortCode U) := ∀ i, Term A Δ (Γ i)

/-- Keep the newly bound variable and weaken all old images under its binder. -/
def Substitution.lift {k l : Nat} {Γ : Fin k → SortCode U} {Δ : Fin l → SortCode U}
    (σ : Substitution A Γ Δ) (sort : SortCode U) :
    Substitution A (Fin.cases sort Γ : Fin (k + 1) → SortCode U) (Fin.cases sort Δ) :=
  Fin.cases (motive := fun i => Term A (Fin.cases sort Δ)
    ((Fin.cases sort Γ : Fin (k + 1) → SortCode U) i))
    (.var 0) (fun i => (σ i).weaken sort)

/-- Typed capture-avoiding parallel substitution through every term position. -/
def Term.subst : {k l : Nat} → {Γ : Fin k → SortCode U} → {Δ : Fin l → SortCode U} →
    Substitution A Γ Δ → {s : SortCode U} → Term A Γ s → Term A Δ s := by
  intro k l Γ Δ σ s t
  exact match t with
  | .var i => σ i
  | .app op args => .app op (fun i => (args i).subst σ)
  | .all sort body => .all sort (body.subst (σ.lift sort))
  | .ex sort body => .ex sort (body.subst (σ.lift sort))

set_option backward.isDefEq.respectTransparency false in
/-- Replace the outermost bound variable by an arbitrary term in the remaining
context, while preserving each remaining variable. -/
def Term.instantiate {k : Nat} {Γ : Fin k → SortCode U} {s sort : SortCode U}
    (body : Term A (Fin.cases sort Γ) s) (t : Term A Γ sort) : Term A Γ s :=
  let σ : Substitution A (Fin.cases sort Γ : Fin (k + 1) → SortCode U) Γ :=
    @Fin.cases k (fun i => Term A Γ
      ((@Fin.cases k (fun _ => SortCode U) sort Γ) i)) t (fun i => .var i)
  body.subst σ

end Silmaril.Logic.Smt.Uflia.Quantified
