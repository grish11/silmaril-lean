module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Defs

public section

namespace Silmaril.Isotope.Institution.Relational.Model

open CategoryTheory

universe u v

variable {τ ε : Type u} {P Q R : InstrSig τ ε} {D : τ → Type v}

theorem reduct_comp_proof (f : P ⟶ Q) (g : Q ⟶ R) (M : Model D R) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f := by
  apply congrArg Semantics.RelationModel.mk
  funext op a b
  change M.eval _ (cast _ a) (cast _ b) = M.eval _ (cast _ (cast _ a)) (cast _ (cast _ b))
  simp only [cast_cast]
  rfl

end Silmaril.Isotope.Institution.Relational.Model
