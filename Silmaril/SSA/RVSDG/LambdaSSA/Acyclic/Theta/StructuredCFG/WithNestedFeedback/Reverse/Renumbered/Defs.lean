module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! # Recover mixed structured CFGs through a supplied typed graph isomorphism -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered

open Sequential
open Isotope.LambdaSSA (Region)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Supply only a graph representative and a checked recursive vertex
bijection. The canonical decoder obtains the source from that representative. -/
structure View (actual : Flat.Serial.Graph Φ A X Z L E D sigs) where
  signatures : List (Ports (OrderedRuntime.Structured.Ty τ))
  representative : Flat.Serial.Graph Φ A X Z L E D signatures
  numbering : NestedTheta.Graph.Isomorphic (Wires.Op Φ) actual representative

structure Related (actual : Flat.Serial.Graph Φ A X Z L E D sigs) (source : Region Φ) where
  view : View actual
  canonical : WithNestedFeedback.Related A X Z L E D view.signatures source view.representative

abbrev Fibre (actual : Flat.Serial.Graph Φ A X Z L E D sigs) :=
  Σ source : Region Φ, Related actual source

def recover [DecidableEq τ] [DecidableEq Φ]
    (actual : Flat.Serial.Graph Φ A X Z L E D sigs) (view : View actual) : Option (Fibre actual) :=
  (Recursive.recover view.representative).map fun recovered => ⟨recovered.1, ⟨view, recovered.2⟩⟩

theorem Related.typing {actual : Flat.Serial.Graph Φ A X Z L E D sigs} {r : Region Φ}
    (w : Related actual r) : Region.HasType [A] r [E,D] :=
  w.canonical.typing

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered
