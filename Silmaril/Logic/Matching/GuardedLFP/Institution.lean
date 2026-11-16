module

public import Silmaril.Logic.Matching.GuardedLFP.Sentences
public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Syntax

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S T : FOL.Signature}

/-- All native positive matching fixed-point sentences over the marked tuple
signature are present, including sentences outside the source translation. -/
def institution : FOL.Signature ⥤ Room where
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

theorem sentence_map (f : S ⟶ T) (p : FirstOrderLFP.Sentence S) :
    SortMaps.Hom.fixedSentence (signatureMap f) (sentence p) = sentence (p.map f) := by
  cases p with
  | mk P Γ p =>
      exact congrArg (FixedPoint.Sentence.mk (A := (signature T).symbols) 0 0 _ _ (.base .truth))
        (formula_map f p)

def inst : Inst := ⟨FOL.Signature, institution⟩

def lfpNatural : FirstOrderLFP.institution ⟶ (𝟭 FOL.Signature) ⋙ institution where
  app S := ⟨sentence, decodeFunctor S, sentence_satisfaction⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (sentence_map f p).symm
    · exact decodeFunctor_naturality f

/-- Full n-ary positive FO(LFP), with possibly empty source sorts and captured
parameters, translated to actual native tuple-valued μ in the guarded target. -/
def lfpToGuardedMatching : Inst.CoHom ⟨FOL.Signature, FirstOrderLFP.institution⟩ inst :=
  ⟨𝟭 _, lfpNatural⟩

theorem lfp_entails_iff (H : Set (FirstOrderLFP.Sentence S)) (p : FirstOrderLFP.Sentence S) :
    ((FirstOrderLFP.institution.obj S).Entails H p) ↔
      ((institution.obj S).Entails (sentence '' H) (sentence p)) := by
  constructor
  · intro h M hH
    apply (sentence_satisfaction M p).mpr
    apply h (decode M)
    intro q hq
    exact (sentence_satisfaction M q).mp (hH _ ⟨q, hq, rfl⟩)
  · intro h M hH
    apply (expanded_satisfaction M p).mp
    apply h (expand M.toStructure)
    rintro q ⟨r, hr, rfl⟩
    exact (expanded_satisfaction M r).mpr (hH r hr)
end Silmaril.Logic.Matching.GuardedLFP
