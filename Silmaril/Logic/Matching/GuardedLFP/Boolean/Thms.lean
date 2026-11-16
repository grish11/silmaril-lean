module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Boolean.Sentences

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S T : FOL.Signature}

theorem sentence_map (f : S ⟶ T) (p : FirstOrderLFP.Boolean.Sentence S) :
    SortMaps.Hom.fixedSentence (signatureMap f) (sentence p) = sentence (p.map f) := by
  cases p with
  | mk P Γ p =>
      exact congrArg (FixedPoint.Sentence.mk (A := (signature T).symbols) 0 0 _ _ (.base .truth))
        (formula_map f p)


def lfpNatural : FirstOrderLFP.Boolean.institution ⟶ (𝟭 FOL.Signature) ⋙ GuardedLFP.institution where
  app S := ⟨sentence, decodeFunctor S, sentence_satisfaction⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (sentence_map f p).symm
    · exact decodeFunctor_naturality f

/-- Full signed Boolean n-ary FO(LFP), with possibly empty source sorts and captured
parameters, translated to actual native tuple-valued μ in the guarded target. -/
def lfpToGuardedMatching : Inst.CoHom ⟨FOL.Signature, FirstOrderLFP.Boolean.institution⟩ GuardedLFP.inst :=
  ⟨𝟭 _, lfpNatural⟩

theorem lfp_entails_iff (H : Set (FirstOrderLFP.Boolean.Sentence S)) (p : FirstOrderLFP.Boolean.Sentence S) :
    ((FirstOrderLFP.Boolean.institution.obj S).Entails H p) ↔
      ((GuardedLFP.institution.obj S).Entails (sentence '' H) (sentence p)) := by
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
end Silmaril.Logic.Matching.GuardedLFP.Boolean
