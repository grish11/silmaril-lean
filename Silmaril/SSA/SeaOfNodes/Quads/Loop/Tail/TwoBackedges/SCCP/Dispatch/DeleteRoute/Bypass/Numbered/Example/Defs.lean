module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

/-! Run both actual targets with the mixed-width fixture from the CF lowering. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example

open Bypass.MLIR.CF.Example (entry facts program bytePort regs word)
open SeaOfNodes.Loop.MLIR.CF (Op model)

/-- The immediate return must read the post-header byte. On the true route
feedback would write 99 instead. -/
def headerWrite : Program Op regs word :=
  { program with header := [⟨[], word, bytePort, .arithmetic (.constant 42), .nil⟩] }

/-- Original, numbered and CF observations at their respective budgets for
the same feedback limit. The outer option reports checker admission. -/
def observations (p : Program Op regs word) (again side : Bool) (limit : Nat) :
    Option (Option Nat × Option Nat × Option Nat) := do
  let graph ← compile model p (facts (.constant ⟨side⟩))
  let (original, cf) ← Bypass.MLIR.CF.Example.observations p again side (3 * limit + 2) (2 * limit + 3)
  let numbered := (graph.run (Join.model model) limit (entry again side)).map
    (fun values => (values.get .head).toNat)
  return (original, numbered, cf)

/-- Execute the numbered body table once on the continuing first header.
Read its tag, continue bit, selector and byte in packet order. -/
def packet (side : Bool) : Option (Nat × Bool × Bool × Nat) := do
  let checked ← check model program (facts (.constant ⟨side⟩))
  match (thetaBody checked).toGraph.run (Join.model model) 0 (entry true side) with
  | some (.cons tag (.cons again (.cons selector (.cons byte .nil)))) =>
    some (tag.down.val, again.down, selector.down, byte.toNat)
  | none => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example
