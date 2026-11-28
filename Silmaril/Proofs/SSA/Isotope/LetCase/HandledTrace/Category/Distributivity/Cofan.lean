module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.DistributivityProofs

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open Silmaril.Isotope.Refinement.Models (OrderedCategory)

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {A B T : Interface M policy}

theorem precomp_le_iff (i : A ≅ B) {f g : B ⟶ T} :
    i.hom ≫ f ≤ i.hom ≫ g ↔ f ≤ g := by
  constructor
  · intro compared
    have restored := OrderedCategory.comp_mono (le_refl i.inv) compared
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using restored
  · exact OrderedCategory.comp_mono (le_refl i.hom)

theorem empty_domain_eq (absent : D A.ty → False) (f g : A ⟶ B) : f = g := by
  induction f, g using Quotient.inductionOn₂
  exact Quotient.sound (Program.equiv_of_run_eq (fun x => (absent x).elim))

end Silmaril.Isotope.LetCase.HandledTrace.DistributivityProofs
