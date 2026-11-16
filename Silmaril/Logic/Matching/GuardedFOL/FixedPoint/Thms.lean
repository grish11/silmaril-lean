module

public import Silmaril.Logic.Matching.GuardedFOL.FixedPoint.Defs
public import Silmaril.Logic.Matching.GuardedFOL.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S T : FOL.Signature}

/-- Inclusion keeps every guarded model and every decoded FOL homomorphism. -/
def firstOrderFixedNatural : institution ⟶ (𝟭 FOL.Signature) ⋙ fixedInstitution where
  app S := ⟨FixedPoint.encodeFirstOrder, 𝟭 (Model S),
    fun M p => FixedPoint.firstOrder_satisfies M.base p⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (SortMaps.Hom.encodeFirstOrder_map (signatureMap f) p).symm
    · rfl

def firstOrderToFixedPoint : Inst.CoHom inst fixedInst :=
  ⟨𝟭 _, firstOrderFixedNatural⟩

/-- Literal expansion holds here because the inclusion has the identity model map. -/
theorem firstOrderToFixedPoint_modelExpansive : firstOrderToFixedPoint.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem firstOrder_fixed_sat_iff (p : FirstOrder.Sentence (signature S).symbols) :
    (∃ M : Model S, FirstOrder.Sentence.Satisfies M.base p) ↔
      ∃ M : Model S, FixedPoint.Sentence.Satisfies M.base (FixedPoint.encodeFirstOrder p) := by
  constructor
  · rintro ⟨M, hp⟩
    exact ⟨M, (FixedPoint.firstOrder_satisfies M.base p).mpr hp⟩
  · rintro ⟨M, hp⟩
    exact ⟨M, (FixedPoint.firstOrder_satisfies M.base p).mp hp⟩

theorem firstOrder_fixed_unsat_iff (p : FirstOrder.Sentence (signature S).symbols) :
    (¬ ∃ M : Model S, FirstOrder.Sentence.Satisfies M.base p) ↔
      ¬ ∃ M : Model S, FixedPoint.Sentence.Satisfies M.base (FixedPoint.encodeFirstOrder p) :=
  not_congr (firstOrder_fixed_sat_iff p)

theorem firstOrder_fixed_entails_iff (H : Set (FirstOrder.Sentence (signature S).symbols))
    (p : FirstOrder.Sentence (signature S).symbols) :
    (institution.obj S).Entails H p ↔
      (fixedInstitution.obj S).Entails (FixedPoint.encodeFirstOrder '' H) (FixedPoint.encodeFirstOrder p) :=
  firstOrderToFixedPoint.entails_iff firstOrderToFixedPoint_modelExpansive S H p

/-- The public FOL translation followed by the native first-order inclusion. -/
def folFixedSentence (p : FOL.Sentence S) : FixedPoint.Sentence (signature S).symbols :=
  FixedPoint.encodeFirstOrder (sentence p)

theorem folFixedSentence_map (f : S ⟶ T) (p : FOL.Sentence S) :
    SortMaps.Hom.fixedSentence (signatureMap f) (folFixedSentence p) = folFixedSentence (p.map f) := by
  unfold folFixedSentence
  rw [SortMaps.Hom.encodeFirstOrder_map, sentence_map]

theorem folFixed_satisfaction (M : Model S) (p : FOL.Sentence S) :
    FixedPoint.Sentence.Satisfies M.base (folFixedSentence p) ↔ p.Holds (decode M) :=
  (FixedPoint.firstOrder_satisfies M.base (sentence p)).trans (sentence_satisfaction M p)

def folFixedNatural : FOL.institution ⟶ (𝟭 FOL.Signature) ⋙ fixedInstitution where
  app S := ⟨folFixedSentence, decodeFunctor S, folFixed_satisfaction⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (folFixedSentence_map f p).symm
    · exact decodeFunctor_naturality f

/-- No literal model-expansiveness assertion is made for this public FOL edge. -/
def folToGuardedFixedPoint : Inst.CoHom FOL.inst fixedInst := ⟨𝟭 _, folFixedNatural⟩

end Silmaril.Logic.Matching.GuardedFOL
