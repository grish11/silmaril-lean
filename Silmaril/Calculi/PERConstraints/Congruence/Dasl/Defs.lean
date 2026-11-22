module

public import Silmaril.Calculi.PERConstraints.Congruence.Defs
public import Silmaril.Formats.Dasl.Congruence.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Congruence

open CategoryTheory Silmaril.Formats.Dasl

variable {Ref Name NextRef NextName : Type}

def daslSignature (enabled : Tree.Shape Ref Name → Prop) : Signature :=
  ⟨⟨Tree Ref Name⟩, Tree.constructors enabled⟩

/-- DASL reference and name maps act on constructor payloads, leaving child
positions unchanged. Only the forward guard implication is required. -/
def daslMap (refs : Ref → NextRef) (names : Name → NextName)
    {enabled : Tree.Shape Ref Name → Prop} {next : Tree.Shape NextRef NextName → Prop}
    (guard : ∀ shape, enabled shape → next (shape.map refs names)) : daslSignature enabled ⟶ daslSignature next where
  term := Tree.map refs names
  shapeMap := fun shape => shape.map refs names
  positionMap := fun shape => by cases shape <;> exact id
  enabledMap := fun shape _ => guard shape
  makeMap := by
    intro shape children
    cases shape <;> first | rfl | rename_i terminal; cases terminal <;> rfl

end Silmaril.Calculi.PERConstraints.Congruence
