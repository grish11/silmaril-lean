module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

/-! Run the original loop and both emitted targets as the selector changes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example

open Bypass.MLIR.CF.Example (program bytePort ports regs width word)
open Backends.Example (computesSelector)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)
open RVSDG (Tuple)

/-- True writes 99 and selects false next. False doubles the reaching byte
and stops. Starting at true therefore takes both feedback edges. -/
def bothRoutes : Program Op regs word :=
  { program with feedback := fun side =>
      if side then
        computesSelector.preheader ++ [⟨[], word, bytePort, .arithmetic (.constant 99), .nil⟩]
      else
        program.feedback false ++ [⟨[word, word], word, bytePort, .arithmetic (.binary .addi),
          .cons bytePort (.cons bytePort .nil)⟩] }

/-- Show the outcome followed by source, CF and numbered observations at
the budgets for the same feedback limit. -/
def observations (p : Program Op regs word) (inputFacts : Tuple (Fact Word) ports)
    (input : Bank (regs := regs) model) (limit : Nat) : String × Option Nat × Option Nat × Option Nat :=
  let native := (p.source.runFrom model (3 * limit + 2) 0 input).map BitVec.toNat
  let original (mode : String) (targets : OriginalTargets p) :=
    (mode, native,
      (targets.cf.run evalOp (3 * limit + 3) (encodeValues input)).map (fun env => (env.get .here).toNat),
      (targets.numbered.run (Join.model model) limit input).map (fun values => (values.get .head).toNat))
  match compile p inputFacts with
  | .specialized targets =>
    ("specialized", native,
      (targets.cf.run evalOp (2 * limit + 3) (encodeValues input)).map (fun env => (env.get .here).toNat),
      (targets.numbered.run (Join.model model) limit input).map (fun values => (values.get .head).toNat))
  | .twoLive targets => original "twoLive" targets
  | .neitherMarked targets => original "neitherMarked" targets

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example
