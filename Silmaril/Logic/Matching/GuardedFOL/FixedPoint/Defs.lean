module

public import Silmaril.Logic.Matching.GuardedFOL.Structure

/-! Native matching fixed points on the existing guarded FOL model category.
The raw models, decoded FOL homomorphisms and reduct functors are unchanged. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Every native μ/ν sentence on the marked signature is admitted, including
sentences outside the first-order image. Satisfaction uses native denotation. -/
def fixedInstitution : FOL.Signature ⥤ Room where
  obj S := ⟨FixedPoint.Sentence (signature S).symbols, Cat.of (Model S),
    fun M p => FixedPoint.Sentence.Satisfies M.base p⟩
  map f := ⟨SortMaps.Hom.fixedSentence (signatureMap f), reductFunctor f,
    fun M p => SortMaps.Hom.fixedSatisfaction (signatureMap f) M.base p⟩
  map_id S := by
    apply Room.hom_ext
    · funext p
      change SortMaps.Hom.fixedSentence (signatureMap (𝟙 S)) p = p
      rw [signatureMap_id, SortMaps.Hom.fixedSentence_id]
    · exact reductFunctor_id S
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change SortMaps.Hom.fixedSentence (signatureMap (f ≫ g)) p =
        SortMaps.Hom.fixedSentence (signatureMap g) (SortMaps.Hom.fixedSentence (signatureMap f) p)
      rw [signatureMap_comp, SortMaps.Hom.fixedSentence_comp]
    · exact reductFunctor_comp f g

def fixedInst : Inst := ⟨FOL.Signature, fixedInstitution⟩

end Silmaril.Logic.Matching.GuardedFOL
