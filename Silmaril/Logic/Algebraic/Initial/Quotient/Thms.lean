module

public import Silmaril.Proofs.Logic.Algebraic.Initial.Quotient.Universal

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Presented
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured
variable {T : Theory} {k : Nat} {Γ : Fin k → T.sig.S}

def model (T : Theory) {k : Nat} (Γ : Fin k → T.sig.S) : Models T :=
  ⟨algebra T Γ, algebra_models T Γ⟩

/-- Projection determines every homomorphism out of the presented algebra. -/
theorem hom_ext {M : EQ.Algebra T.sig} (f g : algebra T Γ ⟶ M)
    (h : projection T Γ ≫ f = projection T Γ ≫ g) : f = g := by
  apply algebraHom_ext
  funext s q
  induction q using Quotient.inductionOn with
  | h a => exact congrArg (fun h => h.map s a) h

/-- Quotient evaluation extends precisely the requested generator assignment. -/
theorem fold_unique (M : Models T) (v : ∀ i, M.obj.carrier (Γ i))
    (f : algebra T Γ ⟶ M.obj)
    (hv : ∀ i, f.map (Γ i) (Quotient.mk _ (.var i)) = v i) : f = foldHom M v := by
  apply hom_ext
  have h := Initial.fold_unique (projection T Γ ≫ f)
  have he : (fun i => f.map (Γ i) (Quotient.mk _ (.var i))) = v := funext hv
  exact h.symm.trans (congrArg (Initial.foldHom M.obj) he)

def freeHomEquiv (M : Models T) :
    (algebra T Γ ⟶ M.obj) ≃ ((i : Fin k) → M.obj.carrier (Γ i)) where
  toFun f i := f.map (Γ i) (Quotient.mk _ (.var i))
  invFun := foldHom M
  left_inv f := (fold_unique M _ f (fun _ => rfl)).symm
  right_inv _ := rfl

/-- Constructed model for every actual equation theory, without assuming any
sort is inhabited or that the axiom set is empty. -/
def quotientModel (T : Theory) : Models T := model T (closedContext T.sig)

def quotientModel_isInitial (T : Theory) : IsInitial (quotientModel T) :=
  IsInitial.ofUniqueHom (fun M => ⟨foldHom M (fun i => i.elim0)⟩) (by
    intro M f
    apply ObjectProperty.hom_ext
    exact fold_unique M _ f.hom (fun i => i.elim0))

/-- Empty presentations recover the original constructor initial model up to
an isomorphism in the same actual model category. -/
def emptyPresentationIso (A : EQ.Signature) :
    Initial.closedModel A ≅ quotientModel (emptyPresentation A) :=
  (Initial.closedModel_isInitial A).uniqueUpToIso (quotientModel_isInitial _)

/-- The quotient actually satisfies the shared institutional initial constraint. -/
theorem quotientModel_satisfies (T : Theory) :
    Constraints.Sat equational (quotientModel T).obj (initialConstraint T) :=
  (initialConstraint_sat_iff T (quotientModel T)).2 ⟨quotientModel_isInitial T⟩

end Silmaril.Logic.Algebraic.Initial.Presented
