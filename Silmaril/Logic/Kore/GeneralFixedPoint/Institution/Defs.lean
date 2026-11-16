module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Semantics.Thms
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)

/-- A named source pattern together with an actual successful elaboration.
Contexts remain explicit; no unchecked raw pattern is a source sentence. -/
structure CheckedSentence (scope : Modules.Scope) where
  fuel : Nat
  sets : Names
  objects : Names
  sort : String
  raw : RawPattern
  typed : Pattern scope sets objects sort
  accepted : Checking.elaborate scope fuel sets objects sort raw = some typed
  admitted : typed.admissible = true

def CheckedSentence.lower {scope : Modules.Scope} (p : CheckedSentence scope) :
    Matching.GeneralFixedPoint.Sentence scope.signature :=
  ⟨p.sets.length, p.objects.length, context p.sets, context p.objects, p.sort, p.typed, p.admitted⟩

/-- Satisfaction runs the independent raw interpreter, universally quantifying
both object and set valuations. -/
def CheckedSentence.Satisfies {scope : Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) (p : CheckedSentence scope) : Prop :=
  ∀ (v : ∀ i, M.carrier (context p.objects i))
    (η : ∀ i, Set (M.carrier (context p.sets i))) (x : M.carrier p.sort),
    x ∈ (Semantics.denote scope M p.fuel (Semantics.interpret M p.sets η)
      (Semantics.interpret M p.objects (fun i => {v i})) p.sort p.raw).getD ∅

theorem CheckedSentence.satisfies_lower {scope : Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) (p : CheckedSentence scope) :
    p.Satisfies M ↔ Matching.GeneralFixedPoint.Sentence.Satisfies M p.lower := by
  change (∀ v η x, x ∈ (Semantics.denote scope M p.fuel _ _ p.sort p.raw).getD ∅) ↔ _
  simp only [Semantics.elaborate_sound M p.fuel p.sets p.objects p.sort p.raw
    p.typed _ _ p.accepted, Option.getD_some]
  rfl

/-- Installation interprets the actual named scope in an ambient signature.
Mapping composes this interpretation; it does not rename the original bytes. -/
structure Sentence (A : Signature String) where
  scope : Modules.Scope
  source : CheckedSentence scope
  symbols : scope.signature ⟶ A

/-- Install a checked declaration at its own signature. -/
def CheckedSentence.install {scope : Modules.Scope} (p : CheckedSentence scope) :
    Sentence scope.signature := ⟨scope, p, 𝟙 scope.signature⟩

variable {A B C : Signature String}

def Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.scope, p.source, p.symbols ≫ f⟩

def Sentence.lower (p : Sentence A) : Matching.GeneralFixedPoint.Sentence A :=
  p.source.lower.map p.symbols

def Sentence.Satisfies (M : Matching.GeneralFixedPoint.Model A) (p : Sentence A) : Prop :=
  p.source.Satisfies (Matching.FirstOrder.SignatureMap.reduct p.symbols M)

/-- Installation commutes with the actual scope interpretation on lowering. -/
theorem CheckedSentence.install_map_lower {scope : Modules.Scope}
    (p : CheckedSentence scope) (f : scope.signature ⟶ A) :
    (p.install.map f).lower = p.lower.map f := by
  change p.lower.map ((𝟙 scope.signature) ≫ f) = p.lower.map f
  rw [Category.id_comp]

theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by
  cases p
  simp only [map, Category.comp_id]

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  simp only [map, Category.assoc]

theorem Sentence.lower_map (f : A ⟶ B) (p : Sentence A) :
    (p.map f).lower = p.lower.map f :=
  Matching.GeneralFixedPoint.Sentence.map_comp p.symbols f p.source.lower

theorem Sentence.satisfies_lower (M : Matching.GeneralFixedPoint.Model A) (p : Sentence A) :
    p.Satisfies M ↔ Matching.GeneralFixedPoint.Sentence.Satisfies M p.lower := by
  exact (p.source.satisfies_lower _).trans
    (((Matching.GeneralFixedPoint.institution String).map p.symbols).sat M p.source.lower).symm

theorem Sentence.satisfaction (f : A ⟶ B) (M : Matching.GeneralFixedPoint.Model B)
    (p : Sentence A) :
    (p.map f).Satisfies M ↔ p.Satisfies (Matching.FirstOrder.SignatureMap.reduct f M) := by
  rw [Sentence.satisfies_lower, Sentence.satisfies_lower, Sentence.lower_map]
  exact ((Matching.GeneralFixedPoint.institution String).map f).sat M p.lower

/-- The checked named general Boolean fixed-point fragment with raw source satisfaction and actual
operation-graph model reducts. -/
def institution : Signature String ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Matching.GeneralFixedPoint.Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, Matching.FirstOrder.SignatureMap.reductFunctor f,
    Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id)
    Matching.FirstOrder.SignatureMap.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g))
    (Matching.FirstOrder.SignatureMap.reductFunctor_comp f g)

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst := (⟨Signature String, institution⟩ : Silmaril.Logic.Institution.Inst)

def loweringNatural : institution ⟶ Matching.GeneralFixedPoint.institution String where
  app A := ⟨Sentence.lower, 𝟭 (Matching.GeneralFixedPoint.Model A), fun M p => (Sentence.satisfies_lower M p).symm⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (Sentence.lower_map f)) rfl

def loweringComorphism : Inst.CoHom ⟨Signature String, institution⟩
    ⟨Signature String, Matching.GeneralFixedPoint.institution String⟩ where
  Φ := 𝟭 _
  ρ := loweringNatural ≫ (Functor.leftUnitor (Matching.GeneralFixedPoint.institution String)).inv

theorem lowering_modelExpansive : loweringComorphism.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem entails_iff (A : Signature String) (H : Set (Sentence A)) (p : Sentence A) :
    (institution.obj A).Entails H p ↔
      ((Matching.GeneralFixedPoint.institution String).obj A).Entails
        (Sentence.lower '' H) p.lower :=
  loweringComorphism.entails_iff lowering_modelExpansive A H p

abbrev Presentation := Silmaril.Logic.Institution.Presentation institution
abbrev Theory := Silmaril.Logic.Institution.Theory institution
end Silmaril.Logic.Kore.GeneralFixedPoint
