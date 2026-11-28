module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Relational.Model

public section

namespace Silmaril.Isotope.Institution.Relational.Model

open CategoryTheory

universe u v

variable {τ ε : Type u} {P Q R : InstrSig τ ε} {D : τ → Type v}

@[simp] theorem reduct_id (M : Model D P) : M.reduct (𝟙 P) = M := rfl

@[simp] theorem reduct_comp (f : P ⟶ Q) (g : Q ⟶ R) (M : Model D R) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f :=
  reduct_comp_proof f g M

variable (D)

@[simp] theorem reductFunctor_id : reductFunctor D (𝟙 P) = 𝟭 (Model D P) := rfl

@[simp] theorem reductFunctor_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    reductFunctor D (f ≫ g) = reductFunctor D g ⋙ reductFunctor D f :=
  CategoryTheory.Functor.ext (reduct_comp f g) (fun _ _ _ => Subsingleton.elim _ _)

end Silmaril.Isotope.Institution.Relational.Model
