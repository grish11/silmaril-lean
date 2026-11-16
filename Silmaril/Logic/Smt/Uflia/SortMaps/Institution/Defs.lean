module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Syntax.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Models.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- Ground UF/LIA with varying sort sets and every ordinary UF model hom. -/
noncomputable def room (A : Signature) : Room.{0,0,1} :=
  ⟨Formula A.symbols, Cat.of (Model A.symbols), Model.Holds⟩

noncomputable def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨Hom.formula f, Hom.reductFunctor f, Hom.holds_formula f⟩

noncomputable def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Hom.formula_id) (Hom.model_reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (Hom.formula_comp f g)) (Hom.model_reductFunctor_comp f g)

noncomputable def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Include the existing fixed-sort signatures without changing their symbols. -/
def fixedSortSignatures (U : Type) : Uflia.Signature U ⥤ Signature where
  obj A := ⟨U, A⟩
  map f := ⟨id, rfl, rfl, fun op => f.operations op⟩

end Silmaril.Logic.Smt.Uflia.SortMaps
