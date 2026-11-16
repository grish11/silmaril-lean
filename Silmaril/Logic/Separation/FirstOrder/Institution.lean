module

public import Silmaril.Logic.Separation.FirstOrder.Signatures

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.FirstOrder
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S : Type} {A B C : FixedSignature S}

/-- Every native base sentence is admitted; native semantics is computed, not stored. -/
def canonicalRoom (A : FixedSignature S) : Room.{0,0,1} :=
  ⟨BaseSentence (signature A.fol), Cat.of (FOL.Structure A.fol),
    fun M p => BaseSentence.Satisfies (native M) p⟩

def canonicalCorridor (f : A ⟶ B) : canonicalRoom A ⟶ canonicalRoom B :=
  ⟨BaseSentence.map (atomMap f), FOL.Structure.reduct f.fol, fun M p => by
    change (p.map (atomMap f)).Satisfies (native M) ↔
      p.Satisfies (native ((FOL.Structure.reduct f.fol).obj M))
    rw [native_reduct]
    exact BaseSentence.satisfaction (atomMap f) (native M) p⟩

def canonicalInstitution (S : Type) : FixedSignature S ⥤ Room.{0,0,1} where
  obj := canonicalRoom
  map := canonicalCorridor
  map_id A := by
    apply Room.hom_ext
    · have h : atomMap (𝟙 A) = 𝟙 (signature A.fol) := funext atomMap_id
      change BaseSentence.map (atomMap (𝟙 A)) = id
      rw [h]
      exact funext BaseSentence.map_id
    · rfl
  map_comp f g := by
    apply Room.hom_ext
    · have h : atomMap (f ≫ g) = atomMap f ≫ atomMap g := funext (atomMap_comp f g)
      change BaseSentence.map (atomMap (f ≫ g)) = _
      rw [h]
      exact funext (BaseSentence.map_comp (atomMap f) (atomMap g))
    · rfl

/-- Only signatures are restricted: all actual FOL models and homs remain. -/
def sourceInstitution (S : Type) : FixedSignature S ⥤ Room.{0,0,1} :=
  toFOL S ⋙ FOL.institution

def sourceInst (S : Type) : Inst := ⟨FixedSignature S, sourceInstitution S⟩
def canonicalInst (S : Type) : Inst := ⟨FixedSignature S, canonicalInstitution S⟩

def compilerCorridor (A : FixedSignature S) :
    (sourceInstitution S).obj A ⟶ (canonicalInstitution S).obj A :=
  ⟨sentence, 𝟭 _, sentence_correct⟩

def compilerNatural (S : Type) : sourceInstitution S ⟶ canonicalInstitution S where
  app := compilerCorridor
  naturality := by
    intro A B f
    apply Room.hom_ext
    · exact funext fun φ => (sentence_naturality f φ).symm
    · rfl

/-- Fixed-sort actual FOL to canonical owned-store native separation semantics. -/
def toSeparation (S : Type) : Inst.CoHom (sourceInst S) (canonicalInst S) where
  Φ := 𝟭 _
  ρ := compilerNatural S ≫ (Functor.leftUnitor (canonicalInstitution S)).inv

theorem toSeparation_modelExpansive (S : Type) : (toSeparation S).ModelExpansive :=
  fun _ M => ⟨M,rfl⟩

theorem entails_iff (H : Set (FOL.Sentence A.fol)) (φ : FOL.Sentence A.fol) :
    (FOL.room A.fol).Entails H φ ↔
      (canonicalRoom A).Entails (sentence '' H) (sentence φ) :=
  (toSeparation S).entails_iff (toSeparation_modelExpansive S) A H φ

theorem sat_iff (H : Set (FOL.Sentence A.fol)) :
    (∃ M : FOL.Structure A.fol, ∀ φ ∈ H, φ.Holds M) ↔
      ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, (sentence φ).Satisfies (native M) := by
  constructor
  · rintro ⟨M,h⟩; exact ⟨M, fun φ hφ => (sentence_correct M φ).2 (h φ hφ)⟩
  · rintro ⟨M,h⟩; exact ⟨M, fun φ hφ => (sentence_correct M φ).1 (h φ hφ)⟩

theorem unsat_iff (H : Set (FOL.Sentence A.fol)) :
    (¬ ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, φ.Holds M) ↔
      ¬ ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, (sentence φ).Satisfies (native M) :=
  not_congr (sat_iff H)

end Silmaril.Logic.Separation.FirstOrder
