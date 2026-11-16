module

public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Thms
public import Silmaril.Logic.Institution.Syntactic.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution

open CategoryTheory Silmaril.Logic.Institution

/-- A raw closed-context equality assertion; validity includes endpoint typing. -/
@[ext] structure Sentence where
  left : Term
  right : Term
  carrier : Term

/-- Translate all three terms using an actual typed encoding. -/
def Sentence.map {P Q : TypedPresentation} (F : P ⟶ Q) (q : Sentence) : Sentence :=
  ⟨F.term q.left, F.term q.right, F.term q.carrier⟩

/-- Actual native equality means both endpoint typings and conversion.
No source type theory or source satisfaction predicate occurs in this definition. -/
def Holds (P : TypedPresentation) (q : Sentence) : Prop :=
  Derives P.calculus ∅ ⟨[], q.left, q.carrier⟩ ∧
  Derives P.calculus ∅ ⟨[], q.right, q.carrier⟩ ∧
  P.calculus.Conversion q.left q.right

/-- A model interprets constants in another actual typed native presentation. -/
structure Model (P : TypedPresentation) where
  target : TypedPresentation
  assignment : P ⟶ target

/-- The identity encoding is an actual model of every typed native presentation. -/
def Model.identity (P : TypedPresentation) : Model P := ⟨P, 𝟙 P⟩

def Model.Satisfies {P : TypedPresentation} (M : Model P) (q : Sentence) : Prop :=
  Holds M.target (q.map M.assignment)

/-- Reduce a target interpretation by composing its actual native encoding. -/
def Model.reduce {P Q : TypedPresentation} (F : P ⟶ Q) (M : Model Q) : Model P :=
  ⟨M.target, F ≫ M.assignment⟩

/-- Independent native typed-equality semantics, with discrete interpretation models. -/
def room (P : TypedPresentation) : Room.{0, 0, 0} where
  Sen := Sentence
  Mod := Cat.of (Discrete (Model P))
  Sat M q := M.as.Satisfies q

end Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution
