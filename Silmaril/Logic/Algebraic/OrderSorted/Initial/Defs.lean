module

public import Silmaril.Logic.Algebraic.OrderSorted.Free.Thms
public import Silmaril.Logic.Institution.Structured.Constraints.Institution

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Initial
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- The existing coherent model category, with only its sentence universe lifted
so the shared constraint construction can quantify over ordered signatures. -/
def orderedRoom (A : Signature) : Room.{1,0,1} :=
  ⟨ULift.{1} (Sentence A), Cat.of (Model A), fun M e => Satisfies M e.down⟩

def orderedCorridor {A B : Signature} (f : A ⟶ B) : orderedRoom A ⟶ orderedRoom B :=
  ⟨fun e => ⟨sentenceMap f e.down⟩, reductFunctor f, fun M e => satisfaction f M e.down⟩

def ordered : Signature ⥤ Room.{1,0,1} where
  obj := orderedRoom
  map := orderedCorridor
  map_id _ := Room.hom_ext
    (funext fun e => congrArg ULift.up (sentenceMap_id e.down)) reductFunctor_id
  map_comp f g := Room.hom_ext
    (funext fun e => congrArg ULift.up (sentenceMap_comp f g e.down)) (reductFunctor_comp f g)

/-- Order-sorted initial/free semantics: the genuine shared freeness constraints
on the actual coherent institution, rather than a restriction to initial models. -/
abbrev institution := Constraints.institution ordered
abbrev Constraint (A : Signature) := Constraints.Constraint ordered A
abbrev Theory := Spec ordered
abbrev Models (T : Theory) := SemanticModels.Models ordered T

abbrev emptySignature : Signature := ⟨⟨PEmpty, fun _ _ _ => PEmpty⟩, inferInstance⟩
def emptyMap (A : Signature) : emptySignature ⟶ A :=
  ⟨⟨PEmpty.elim, fun o => o.elim⟩, fun s => s.elim⟩
abbrev emptyTheory : Theory := ⟨emptySignature, ∅⟩
def emptyTheoryMap (T : Theory) : emptyTheory ⟶ T :=
  ⟨emptyMap T.sig, fun _ h => h.elim⟩

def initialConstraint (T : Theory) : Constraint T.sig :=
  ⟨emptyTheory, T, emptyTheoryMap T, 𝟙 T.sig⟩

abbrev emptyPresentation (A : Signature) : Theory := ⟨A, ∅⟩
def closedModel (A : Signature) : Models (emptyPresentation A) :=
  SemanticModels.emptyModel ordered A (Free.closedModel A)

end Silmaril.Logic.Algebraic.OrderSorted.Initial
