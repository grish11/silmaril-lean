module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! # Finite coloured completion of the actual shared-suffix θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (m : Model.{u, v, w} Op)

/-- The emitted numbered graph has a finite coloured completion with the
given output exactly when the original source does. Firing length is independent. -/
theorem petri_finishes_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    Finishes (Join.model m) (lower p) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  (finishes_iff (Join.model m) (lower p) input _).trans (returns_iff p m input value)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered
