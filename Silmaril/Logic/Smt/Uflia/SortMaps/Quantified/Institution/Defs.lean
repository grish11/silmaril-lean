module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.QuantifiedModels
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- Full quantified terms over varying sort sets; model arrows are ordinary
operation-preserving homomorphisms, without a claim of quantified truth transport. -/
noncomputable def room (A : Signature) : Room.{0,0,1} :=
  ⟨Quantified.Sentence A.symbols, Cat.of (Model A.symbols), fun M p => p.Holds M⟩

noncomputable def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨Hom.quantifiedSentence f, Hom.reductFunctor f, Hom.holds_quantifiedSentence f⟩

noncomputable def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Hom.quantifiedSentence_id) (Hom.model_reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (Hom.quantifiedSentence_comp f g))
    (Hom.model_reductFunctor_comp f g)

noncomputable def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

end Silmaril.Logic.Smt.Uflia.SortMaps.QuantifiedModels
