module

public import Silmaril.Logic.Hoare.FirstOrder.Models

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Hoare.FirstOrder
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S : Type} {A B : FixedSignature S}

/-- All native Hoare triples are admitted. Models and arrows are actual FOL structures/homs;
semantics is computed in their independent partial-store native PDL frames.
This is not a functor from FOL homs to native Hoare's equality-only model arrows. -/
def canonicalRoom (A : FixedSignature S) : Room.{0,0,1} :=
  ⟨Hoare.Triple (Command S) (signature A.fol), Cat.of (FOL.Structure A.fol),
    fun M t => t.Satisfies (Command S) (native M)⟩

def canonicalCorridor (f : A ⟶ B) : canonicalRoom A ⟶ canonicalRoom B :=
  ⟨Hoare.Triple.map (Command S) (nativeSignatureMap f), FOL.Structure.reduct f.fol, fun M t => by
    change (t.map (Command S) (nativeSignatureMap f)).Satisfies (Command S) (native M) ↔
      t.Satisfies (Command S) (native ((FOL.Structure.reduct f.fol).obj M))
    rw [Hoare.Triple.satisfaction]
    exact Iff.of_eq (congrArg (t.Satisfies (Command S)) (native_reduct f M).symm)⟩

def canonicalInstitution (S : Type) : FixedSignature S ⥤ Room.{0,0,1} where
  obj := canonicalRoom
  map := canonicalCorridor
  map_id A := by
    apply Room.hom_ext
    · have hf := (toNative S).map_id A
      change Hoare.Triple.map (Command S) ((toNative S).map (𝟙 A)) = id
      rw [hf]
      exact funext (Hoare.Triple.map_id (Command S))
    · rfl
  map_comp f g := by
    apply Room.hom_ext
    · have hf := (toNative S).map_comp f g
      change Hoare.Triple.map (Command S) ((toNative S).map (f ≫ g)) = _
      rw [hf]
      exact funext (Hoare.Triple.map_comp (Command S) (nativeSignatureMap f) (nativeSignatureMap g))
    · rfl

def sourceInstitution (S : Type) : FixedSignature S ⥤ Room.{0,0,1} :=
  toFOL S ⋙ FOL.institution

def sourceInst (S : Type) : Inst := ⟨FixedSignature S, sourceInstitution S⟩
def canonicalInst (S : Type) : Inst := ⟨FixedSignature S, canonicalInstitution S⟩

/-- Identity on actual FOL structures and every actual algebra/relation homomorphism. -/
def forgetModels (A : FixedSignature S) : FOL.Structure A.fol ⥤ FOL.Structure A.fol := 𝟭 _

theorem modelReduct_natural (f : A ⟶ B) :
    forgetModels B ⋙ FOL.Structure.reduct f.fol =
      FOL.Structure.reduct f.fol ⋙ forgetModels A := rfl

def compilerCorridor (A : FixedSignature S) :
    (sourceInstitution S).obj A ⟶ (canonicalInstitution S).obj A :=
  ⟨sentence, forgetModels A, sentence_correct⟩

def compilerNatural (S : Type) : sourceInstitution S ⟶ canonicalInstitution S where
  app := compilerCorridor
  naturality := by
    intro A B f
    exact Room.hom_ext (funext fun φ => (sentence_naturality f φ).symm) (modelReduct_natural f)

/-- Actual structural FOL→canonical native Hoare compiler over fixed arbitrary sorts. -/
def toHoare (S : Type) : Inst.CoHom (sourceInst S) (canonicalInst S) where
  Φ := 𝟭 _
  ρ := compilerNatural S ≫ (Functor.leftUnitor (canonicalInstitution S)).inv

theorem toHoare_modelExpansive (S : Type) : (toHoare S).ModelExpansive :=
  fun _ M => ⟨M,rfl⟩

theorem entails_iff (H : Set (FOL.Sentence A.fol)) (φ : FOL.Sentence A.fol) :
    (FOL.room A.fol).Entails H φ ↔
      (canonicalRoom A).Entails (sentence '' H) (sentence φ) :=
  (toHoare S).entails_iff (toHoare_modelExpansive S) A H φ

theorem sat_iff (H : Set (FOL.Sentence A.fol)) :
    (∃ M : FOL.Structure A.fol, ∀ φ ∈ H, φ.Holds M) ↔
      ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, (sentence φ).Satisfies (Command S) (native M) := by
  constructor
  · rintro ⟨M,h⟩
    exact ⟨M, fun φ hφ => (sentence_correct M φ).2 (h φ hφ)⟩
  · rintro ⟨M,h⟩
    exact ⟨M, fun φ hφ => (sentence_correct M φ).1 (h φ hφ)⟩

theorem unsat_iff (H : Set (FOL.Sentence A.fol)) :
    (¬ ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, φ.Holds M) ↔
      ¬ ∃ M : FOL.Structure A.fol, ∀ φ ∈ H, (sentence φ).Satisfies (Command S) (native M) :=
  not_congr (sat_iff H)

end Silmaril.Logic.Hoare.FirstOrder
