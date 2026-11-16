module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

/-- Admission checks all bound recursion variables, with no restriction on the
polarity of the universally quantified free set variables. -/
structure Sentence (A : Signature S) where
  setCount : Nat
  objectCount : Nat
  sets : Fin setCount → S
  objects : Fin objectCount → S
  sort : S
  pattern : Pattern A sets objects sort
  admitted : pattern.admissible = true

def Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.setCount, p.objectCount, p.sets, p.objects, p.sort, p.pattern.map f,
    by rw [Pattern.admissible_map]; exact p.admitted⟩

def Sentence.Satisfies (M : Model A) (p : Sentence A) : Prop :=
  ∀ (v : ObjEnv A M p.objects) (η : SetEnv A M p.sets) (x : M.carrier p.sort),
    x ∈ p.pattern.denote M v η

theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by
  cases p
  simp only [map, Pattern.map_id]

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p
  simp only [map, Pattern.map_comp]

def institution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, FirstOrder.SignatureMap.reductFunctor f, by
    intro M p
    change (∀ v η x, x ∈ (p.pattern.map f).denote M v η) ↔ _
    simp only [Pattern.denote_map]
    rfl⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) FirstOrder.SignatureMap.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g))
    (FirstOrder.SignatureMap.reductFunctor_comp f g)

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst (S : Type) := (⟨Signature S, institution S⟩ : Silmaril.Logic.Institution.Inst)

def positiveSentence (p : FixedPoint.Sentence A) : Sentence A :=
  ⟨p.setCount, p.objectCount, p.sets, p.objects, p.sort, ofPositive p.pattern,
    ofPositive_admissible p.pattern⟩

theorem positive_satisfies (M : Model A) (p : FixedPoint.Sentence A) :
    Sentence.Satisfies M (positiveSentence p) ↔ FixedPoint.Sentence.Satisfies M p := by
  change (∀ v η x, x ∈ (ofPositive p.pattern).denote M v η) ↔ _
  simp only [denote_ofPositive]
  rfl
theorem positiveSentence_map (f : A ⟶ B) (p : FixedPoint.Sentence A) :
    positiveSentence (p.map f) = (positiveSentence p).map f := by
  cases p
  simp only [positiveSentence, FixedPoint.Sentence.map, Sentence.map, ofPositive_map]

def positiveNatural : FixedPoint.institution S ⟶ (𝟭 (Signature S)) ⋙ institution S where
  app A := ⟨positiveSentence, 𝟭 (Model A), positive_satisfies⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (positiveSentence_map f)) rfl

/-- The old positive institution embeds with the actual unchanged models. -/
def positiveComorphism : Inst.CoHom ⟨Signature S, FixedPoint.institution S⟩
    ⟨Signature S, institution S⟩ := ⟨𝟭 _, positiveNatural⟩

theorem positive_modelExpansive : (positiveComorphism (S := S)).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem positive_entails_iff (A : Signature S) (H : Set (FixedPoint.Sentence A))
    (p : FixedPoint.Sentence A) :
    ((FixedPoint.institution S).obj A).Entails H p ↔
      ((institution S).obj A).Entails (positiveSentence '' H) (positiveSentence p) :=
  positiveComorphism.entails_iff positive_modelExpansive A H p

end Silmaril.Logic.Matching.GeneralFixedPoint
