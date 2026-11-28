module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

/-! Run the two emitted artifacts from one admission on the mixed-width fixture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example

open Bypass.MLIR.CF.Example (entry facts width ports regs word program bytePort)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open RVSDG (Tuple)

/-- With a false header predicate and an empty header, neither feedback
occurrence is marked. -/
def stoppingFacts : Tuple (Fact Word) ports :=
  .cons (.constant ⟨false⟩) (.cons .overdefined (.cons (.constant (7 : Word width)) .nil))

/-- The preheader derives the false selector by comparing the covered byte
with itself. The incoming selector can be overdefined. -/
def computesSelector : Program Op regs word :=
  { program with preheader := [⟨[word, word], .predicate, .tail .head, .ult width,
      .cons bytePort (.cons bytePort .nil)⟩] }

/-- One compile followed by three runners with independently accounted
budgets. The tuple gives the retained side, original, CF and numbered results. -/
def observations (p : Program Op regs word) (again side : Bool) (limit : Nat) :
    Except Refusal (Bool × Option Nat × Option Nat × Option Nat) := do
  let targets ← compile p (facts (.constant ⟨side⟩))
  let input := entry again side
  let source := p.source.runFrom model (3 * limit + 2) 0 input
  let cf := targets.cf.run evalOp (2 * limit + 3) (encodeValues input)
  let numbered := targets.numbered.run (Join.model model) limit input
  return (targets.retained, source.map BitVec.toNat, cf.map (fun env => (env.get .here).toNat),
    numbered.map (fun values => (values.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example
