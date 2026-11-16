module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Defs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified
open CategoryTheory
variable {U : Type} {A B : Uflia.Signature U}

theorem Ref.map_term (f : A ⟶ B) {k : Nat} {Γ : Fin k → SortCode U} {s}
    (r : Ref Γ s) : (r.term : Term A Γ s).map f = (r.term : Term B Γ s) := by
  cases r
  rfl

/-- Global symbol transport commutes with capture-safe local reference renaming. -/
theorem Term.map_rename (f : A ⟶ B) {k Γ s} (term : Term A (k := k) Γ s) :
    ∀ {l : Nat} {Δ : Fin l → SortCode U} (r : ∀ i, Ref Δ (Γ i)),
      (term.rename r).map f = (term.map f).rename r := by
  induction term with
  | var i =>
      intro l Δ r
      exact Ref.map_term f (r i)
  | app op args ih =>
      intro l Δ r
      simp only [Term.rename, Term.map]
      congr 1
      funext i
      exact ih i r
  | all sort body ih =>
      intro l Δ r
      exact congrArg (Term.all sort) (ih (Ref.lift r sort))
  | ex sort body ih =>
      intro l Δ r
      exact congrArg (Term.ex sort) (ih (Ref.lift r sort))

theorem Term.map_weaken (f : A ⟶ B) {k Γ s} (term : Term A (k := k) Γ s)
    (sort : SortCode U) : (term.weaken sort).map f = (term.map f).weaken sort := by
  unfold Term.weaken
  exact term.map_rename f (Δ := Fin.cases sort Γ) (fun i => Ref.index i.succ)

end Silmaril.Logic.Smt.Uflia.Quantified
