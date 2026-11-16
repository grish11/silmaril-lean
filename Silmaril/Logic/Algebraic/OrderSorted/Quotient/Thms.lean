module

public import Silmaril.Proofs.Logic.Algebraic.OrderSorted.Quotient.Universal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented
open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution.Structured
variable {T : Initial.Theory} {k : Nat} {Γ : Fin k → T.sig.base.S}

def model (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S) : Initial.Models T :=
  ⟨coherentModel T Γ, model_models T Γ⟩

theorem hom_ext {M : Model T.sig} (f g : coherentModel T Γ ⟶ M)
    (h : projection T Γ ≫ f = projection T Γ ≫ g) : f = g := by
  apply Free.hom_ext
  funext s q
  induction q using Quotient.inductionOn with
  | h a => exact congrArg (fun h => h.map s a) h

theorem fold_unique (M : Initial.Models T) (v : ∀ i, M.obj.algebra.carrier (Γ i))
    (f : coherentModel T Γ ⟶ M.obj)
    (hv : ∀ i, f.map (Γ i) (Quotient.mk _ (Free.generator i)) = v i) :
    f = foldHom M v := by
  apply hom_ext
  exact Free.fold_unique (projection T Γ ≫ f) v hv

def freeHomEquiv (M : Initial.Models T) :
    (coherentModel T Γ ⟶ M.obj) ≃ ((i : Fin k) → M.obj.algebra.carrier (Γ i)) where
  toFun f i := f.map (Γ i) (Quotient.mk _ (Free.generator i))
  invFun := foldHom M
  left_inv f := (fold_unique M _ f (fun _ => rfl)).symm
  right_inv v := funext (Free.eval_generator M.obj v)

def quotientModel (T : Initial.Theory) : Initial.Models T :=
  model T (Free.closedContext T.sig)

def quotientModel_isInitial (T : Initial.Theory) : IsInitial (quotientModel T) :=
  IsInitial.ofUniqueHom (fun M => ⟨foldHom M (fun i => i.elim0)⟩) (by
    intro M f
    apply ObjectProperty.hom_ext
    exact fold_unique M _ f.hom (fun i => i.elim0))

def emptyPresentationIso (A : Signature) :
    Initial.closedModel A ≅ quotientModel (Initial.emptyPresentation A) :=
  (Initial.closedModel_isInitial A).uniqueUpToIso (quotientModel_isInitial _)

theorem quotientModel_satisfies (T : Initial.Theory) :
    Constraints.Sat Initial.ordered (quotientModel T).obj (Initial.initialConstraint T) :=
  (Initial.initialConstraint_sat_iff T (quotientModel T)).2 ⟨quotientModel_isInitial T⟩

end Silmaril.Logic.Algebraic.OrderSorted.Presented
