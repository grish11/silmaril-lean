module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Thms
public import Silmaril.Logic.Institution.Syntactic.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution

open CategoryTheory Silmaril.Logic.Institution
open IntensionalMLTT

/-- A telescope of independently source-checked global LF declarations. -/
structure Signature where
  scope : ℕ
  context : Context scope
  formed : SignatureFormed context

/-- Interpret each source global by an actually source-typed target term.
Images may be compound terms, including functions and type families. -/
structure Map (S T : Signature) where
  terms : Fin S.scope → IntensionalMLTT.Term T.scope
  typed : TypedSubstitution S.context T.context T.context terms

def Map.identity (S : Signature) : Map S S where
  terms := IntensionalMLTT.Term.var
  typed h := by
    simpa only [IntensionalMLTT.Term.subst_var] using Equality.var (.signature S.formed) h

def Map.comp {S T U : Signature} (F : Map S T) (G : Map T U) : Map S U where
  terms i := (F.terms i).subst G.terms
  typed h := by
    simpa only [IntensionalMLTT.Term.subst_comp] using
      (F.typed h).subst (.signature U.formed) G.terms G.typed

/-- A source equality assertion; formation and derivability are tested by satisfaction. -/
structure Sentence (S : Signature) where
  left : IntensionalMLTT.Term S.scope
  right : IntensionalMLTT.Term S.scope
  carrier : IntensionalMLTT.Term S.scope

def Map.sentence {S T : Signature} (F : Map S T) (q : Sentence S) : Sentence T :=
  ⟨q.left.subst F.terms, q.right.subst F.terms, q.carrier.subst F.terms⟩

/-- A syntactic model interprets the globals in another source-formed signature. -/
structure Model (S : Signature) where
  target : Signature
  assignment : Map S target

/-- Source equality under this particular typed interpretation. -/
def Model.Satisfies {S : Signature} (M : Model S) (q : Sentence S) : Prop :=
  Equality M.target.context M.target.context
    (q.left.subst M.assignment.terms) (q.right.subst M.assignment.terms)
    (q.carrier.subst M.assignment.terms)

/-- Raw source equality assertions with actual typed substitution models. -/
def room (S : Signature) : Room.{0, 0, 0} where
  Sen := Sentence S
  Mod := Cat.of (Discrete (Model S))
  Sat M q := M.as.Satisfies q

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution
