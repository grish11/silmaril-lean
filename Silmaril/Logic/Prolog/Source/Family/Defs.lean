module

public import Silmaril.Logic.Prolog.Source.Accepted.Thms

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Finite one-sorted vocabularies with arbitrary arity-preserving symbol maps.
Maps may identify or rename symbols; they need not be inclusions. -/
instance : Category Vocabulary where
  Hom V W := V.signature ⟶ W.signature
  id V := 𝟙 V.signature
  comp f g := f ≫ g

/-- The actual public signature, including both function and predicate maps. -/
def vocabularySignatures : Vocabulary ⥤ FOL.Signature where
  obj := Vocabulary.signature
  map f := f

/-- Accepted text in its own local vocabulary, interpreted in a shared ambient
vocabulary. Mapping changes this interpretation, not the original parse receipt. -/
structure Family (V : Vocabulary) where
  localVocabulary : Vocabulary
  sentence : AcceptedSentence localVocabulary
  symbols : localVocabulary.signature ⟶ V.signature

namespace Family
variable {V W X : Vocabulary}

/-- Direct named meaning in the reduct: no scoped or FOL evaluator defines truth. -/
def Holds (M : FOL.Structure V.signature) (s : Family V) : Prop :=
  s.sentence.Holds ((FOL.Structure.reduct s.symbols).obj M)

def map (f : V ⟶ W) (s : Family V) : Family W :=
  ⟨s.localVocabulary, s.sentence, s.symbols ≫ f⟩

@[simp] theorem map_id (s : Family V) : s.map (𝟙 V) = s := by
  rcases s with ⟨L, t, h⟩
  change Family.mk L t (h ≫ 𝟙 V.signature) = Family.mk L t h
  rw [Category.comp_id]

@[simp] theorem map_comp (f : V ⟶ W) (g : W ⟶ X) (s : Family V) :
    s.map (f ≫ g) = (s.map f).map g := by
  change Family.mk s.localVocabulary s.sentence
    (s.symbols ≫ ((f : V.signature ⟶ W.signature) ≫ g)) =
    Family.mk s.localVocabulary s.sentence ((s.symbols ≫ f) ≫ g)
  rw [Category.assoc]

theorem holds_map (f : V ⟶ W) (M : FOL.Structure W.signature) (s : Family V) :
    (s.map f).Holds M ↔ s.Holds ((FOL.Structure.reduct f).obj M) := Iff.rfl

/-- Package a sentence without changing its vocabulary, text or models. -/
def ofAccepted (s : AcceptedSentence V) : Family V := ⟨V, s, 𝟙 _⟩

theorem ofAccepted_holds (M : FOL.Structure V.signature) (s : AcceptedSentence V) :
    (ofAccepted s).Holds M ↔ s.Holds M := Iff.rfl

/-- Sentence-local compilation followed by the recorded symbol interpretation. -/
def encode (s : Family V) : Definite.Sentence V.signature :=
  s.sentence.resolved.encode.map s.symbols

theorem encode_holds (M : FOL.Structure V.signature) (s : Family V) :
    s.encode.Holds M ↔ s.Holds M :=
  (Definite.Sentence.holds_map s.symbols M s.sentence.resolved.encode).trans
    (s.sentence.encode_holds _)

theorem encode_map (f : V ⟶ W) (s : Family V) :
    (s.map f).encode = s.encode.map f :=
  Definite.Sentence.map_comp s.symbols f s.sentence.resolved.encode

end Family

namespace Families

def room (V : Vocabulary) : Room.{0,0,1} :=
  ⟨Family V, Cat.of (FOL.Structure V.signature), fun M s => s.Holds M⟩

def corridor {V W : Vocabulary} (f : V ⟶ W) : room V ⟶ room W :=
  ⟨Family.map f, FOL.Structure.reduct f, Family.holds_map f⟩

def institution : Vocabulary ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext Family.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Family.map_comp f g)) rfl

def inst : Inst.{0,0,0,0,1} := ⟨Vocabulary, institution⟩

/-- Varying-vocabulary accepted-source institution, with every ordinary model hom. -/
def toDefinite : Inst.CoHom inst Definite.inst where
  Φ := vocabularySignatures
  ρ :=
    { app V := ⟨Family.encode, 𝟭 _, Family.encode_holds⟩
      naturality := by
        intro V W f
        exact Room.hom_ext (funext (Family.encode_map f)) rfl }

def toFirstOrder : Inst.CoHom inst FOL.inst := toDefinite.comp Definite.toFirstOrder

/-- A comparison with the original fixed-vocabulary frontend, rather than a
second implementation of that room. Its model functor is the identity. -/
def package (V : Vocabulary) : sourceRoom V ⟶ room V :=
  ⟨Family.ofAccepted, 𝟭 _, Family.ofAccepted_holds⟩

end Families
end Silmaril.Logic.Prolog.Source
