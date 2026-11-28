module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs

/-! # Public recovery with a supplied numbered representative and row maps -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Renumbered

open Sequential
open Flat.Numbered.Recognize (opcodeCode)
open NestedTheta.Isomorphism (Mapping check)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {actualSigs canonicalSigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

structure Fibre (actual : Flat.Serial.Graph Φ A X Z L E D actualSigs)
    (canonical : Flat.Serial.Graph Φ A X Z L E D canonicalSigs) (layout : Layout τ A X Z L E D canonicalSigs) where
  numbering : NestedTheta.Graph.Isomorphic (Wires.Op Φ) actual canonical
  recovered : Translation.Fibre layout canonical

/-- Check the proposed row maps, then recover a source from the numbered
representative using its existing layout decoder. -/
def recover [DecidableEq τ] [DecidableEq Φ]
    (actual : Flat.Serial.Graph Φ A X Z L E D actualSigs) (canonical : Flat.Serial.Graph Φ A X Z L E D canonicalSigs)
    (layout : Layout τ A X Z L E D canonicalSigs) (mapping : Mapping) :
    Option (Fibre actual canonical layout) :=
  match check (opcodeCode (τ := τ) (Φ := Φ)) mapping actual canonical with
  | none => none
  | some numbering => (Translation.recover layout canonical).map fun recovered => ⟨numbering.down, recovered⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Renumbered
