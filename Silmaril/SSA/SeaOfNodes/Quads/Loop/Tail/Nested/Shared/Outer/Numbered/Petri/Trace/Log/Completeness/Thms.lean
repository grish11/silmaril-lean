module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Entry
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Soundness
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Observations

/-! Exact complete-log acceptance for the marked-entry profile. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

/-- The checker accepts exactly the adjacent-legal, completed logs with a
fully marked preheader at θ entry. The list carries no caller boundaries. -/
theorem scan_isSome_iff (roots : List (RootMark p)) :
    (scan p input roots).isSome ↔ LegalComplete p input roots :=
  ⟨Completeness.Proofs.scan_sound p input roots, Completeness.Proofs.scan_complete p input roots⟩

variable {roots₁ roots₂ : List (RootMark p)}

/-- Comparison forgets firing positions and keeps the ordered full typed
observations. It applies at the same input across any two accepted logs. -/
theorem Complete.observations_eq (left : Complete p input roots₁) (right : Complete p input roots₂) :
    left.observations p input = right.observations p input :=
  Completeness.Proofs.observations_same p input left right

theorem Complete.result_eq (left : Complete p input roots₁) (right : Complete p input roots₂) :
    left.result p input = right.result p input :=
  Completeness.Proofs.result_same p input left right

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
