module

public import Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Defs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.PublicEQ
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S : Type} {A B : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

theorem to_fromTerm (t : Term A Γ s) : toTerm (fromTerm t) = t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app op) (funext ih)

theorem from_toTerm (t : EQ.Term (signature A) Γ s) : fromTerm (toTerm t) = t := by
  exact EQ.Term.rec (motive := fun _ t => fromTerm (toTerm t) = t)
    (fun _ => rfl) (fun op _ ih => by
      simp only [toTerm, fromTerm]
      exact congrArg (EQ.Term.app op) (funext ih)) t

theorem to_fromEquation (e : Equation A) : toEquation (fromEquation e) = e := by
  cases e
  simp only [toEquation, fromEquation, to_fromTerm]

theorem from_toEquation (e : EQ.Equation (signature A)) : fromEquation (toEquation e) = e := by
  cases e
  simp only [toEquation, fromEquation, from_toTerm]

theorem to_fromModel (M : Model A) : toModel (fromModel M) = M := by cases M; rfl
theorem from_toModel (M : EQ.Algebra (signature A)) : fromModel (toModel M) = M := by cases M; rfl

/-- The round trip retains all arrows as well as all objects. -/
theorem models_roundtrip : fromModels A ⋙ toModels A = 𝟭 (Model A) := by
  apply Functor.hext to_fromModel
  intro M N h
  cases M
  cases N
  cases h
  rfl

theorem publicModels_roundtrip : toModels A ⋙ fromModels A = 𝟭 (EQ.Algebra (signature A)) := by
  apply Functor.hext from_toModel
  intro M N h
  cases M
  cases N
  cases h
  rfl

theorem eval_toTerm (M : Model A) (ρ : ∀ i, M.carrier (Γ i))
    (t : EQ.Term (signature A) Γ s) :
    M.eval ρ (toTerm t) = t.eval (fromModel M) ρ := by
  exact EQ.Term.rec (motive := fun _ t => M.eval ρ (toTerm t) = t.eval (fromModel M) ρ)
    (fun _ => rfl) (fun op _ ih => congrArg (M.operation op) (funext ih)) t

theorem eval_fromTerm (M : EQ.Algebra (signature A)) (ρ : ∀ i, M.carrier (Γ i))
    (t : Term A Γ s) :
    (fromTerm t).eval M ρ = (toModel M).eval ρ t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (M.op op) (funext ih)

theorem satisfaction (M : Model A) (e : EQ.Equation (signature A)) :
    Equation.Satisfies M (toEquation e) ↔ e.Holds (fromModel M) := by
  simp only [Equation.Satisfies, toEquation, EQ.Equation.Holds, eval_toTerm]
  rfl

theorem reverse_satisfaction (M : EQ.Algebra (signature A)) (e : Equation A) :
    (fromEquation e).Holds M ↔ Equation.Satisfies (toModel M) e := by
  simp only [Equation.Satisfies, fromEquation, EQ.Equation.Holds, eval_fromTerm]
  rfl

theorem toTerm_map (f : A ⟶ B) (t : EQ.Term (signature A) Γ s) :
    toTerm (t.map (signatureMap f)) = Term.map f (toTerm t) := by
  exact EQ.Term.rec (motive := fun _ t =>
      toTerm (A := B) (t.map (signatureMap f)) = Term.map f (toTerm (A := A) t))
    (fun _ => rfl) (fun op _ ih => by
      simp only [EQ.Term.map, toTerm, Term.map]
      exact congrArg (Term.app (f.operations op)) (funext ih)) t

theorem fromTerm_map (f : A ⟶ B) (t : Term A Γ s) :
    fromTerm (Term.map f t) = (fromTerm t).map (signatureMap f) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (EQ.Term.app (f.operations op)) (funext ih)

theorem toEquation_map (f : A ⟶ B) (e : EQ.Equation (signature A)) :
    toEquation (e.map (signatureMap f)) = Equation.map f (toEquation e) := by
  cases e
  simp only [toEquation, EQ.Equation.map, Equation.map, toTerm_map]
  rfl

theorem fromEquation_map (f : A ⟶ B) (e : Equation A) :
    fromEquation (Equation.map f e) = (fromEquation e).map (signatureMap f) := by
  cases e
  simp only [fromEquation, EQ.Equation.map, Equation.map, fromTerm_map]
  rfl

/-- Exact naturality includes every model homomorphism, not merely objects. -/
theorem fromModels_reduct (f : A ⟶ B) :
    fromModels B ⋙ EQ.Algebra.reduct (signatureMap f) =
      Signature.Hom.reductFunctor f ⋙ fromModels A := rfl

theorem toModels_reduct (f : A ⟶ B) :
    toModels B ⋙ Signature.Hom.reductFunctor f =
      EQ.Algebra.reduct (signatureMap f) ⋙ toModels A := rfl

end Silmaril.Logic.Algebraic.ManySorted.PublicEQ
