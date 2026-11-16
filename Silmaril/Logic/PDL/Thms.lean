module

public import Silmaril.Proofs.Logic.PDL.Semantics

@[expose] public section
namespace Silmaril.Logic.PDL
open CategoryTheory Silmaril.Logic.Institution

def institution : Signature ⥤ Room where
  obj S := ⟨Formula S, Cat.of (Model S), Sat⟩
  map f := ⟨Formula.map f, ModalMu.modelReduct f, fun M p => p.holds_map f M M.point⟩
  map_id _ := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

end Silmaril.Logic.PDL
