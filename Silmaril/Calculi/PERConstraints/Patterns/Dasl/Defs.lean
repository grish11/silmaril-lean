module

public import Silmaril.Calculi.PERConstraints.Patterns.Defs
public import Silmaril.Calculi.PERConstraints.Congruence.Dasl.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns

open CategoryTheory Silmaril.Formats.Dasl

variable {Ref Name NextRef NextName SourceIndex TargetIndex : Type}

def daslSignature (Index : Type) (enabled : Tree.Shape Ref Name → Prop) : Signature :=
  ⟨Congruence.daslSignature enabled, Index⟩

abbrev DaslPattern (enabled : Tree.Shape Ref Name → Prop) (arity : Nat) :=
  Pattern (Congruence.daslSignature enabled) (Fin arity)

/-- A reference/name translation inherits the same child positions. Unlike the
forward-only constructor bridge, the rule institution also checks exact guards
and requires every target tree to lift. -/
def daslMap (refs : Ref → NextRef) (names : Name → NextName) (indices : SourceIndex → TargetIndex)
    {enabled : Tree.Shape Ref Name → Prop} {next : Tree.Shape NextRef NextName → Prop}
    (guard : ∀ shape, enabled shape ↔ next (shape.map refs names))
    (onto : Function.Surjective (Tree.map refs names)) : daslSignature SourceIndex enabled ⟶ daslSignature TargetIndex next where
  constructorMap := Congruence.daslMap refs names fun shape => (guard shape).1
  indexMap := indices
  ontoTerm := onto
  ontoPosition := fun shape => by cases shape <;> exact Function.surjective_id
  reflectsEnabled := fun shape _ => (guard shape).2

end Silmaril.Calculi.PERConstraints.Patterns
