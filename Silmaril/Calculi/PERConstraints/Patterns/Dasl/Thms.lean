module

public import Silmaril.Calculi.PERConstraints.Patterns.Dasl.Defs
public import Silmaril.Calculi.PERConstraints.Patterns.Thms
import Silmaril.Proofs.Calculi.PERConstraints.Patterns.Dasl

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns

open Silmaril.Formats.Dasl

theorem tree_map_surjective {Ref Name NextRef NextName : Type} {refs : Ref → NextRef} {names : Name → NextName}
    (ontoRefs : Function.Surjective refs) (ontoNames : Function.Surjective names) :
    Function.Surjective (Tree.map refs names) := Proofs.tree_map_surjective ontoRefs ontoNames

end Silmaril.Calculi.PERConstraints.Patterns
