module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs

/-! # Run the projected CF lowering on the existing unequal-arm fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example

open CF.Example (checked input regs width)
open Diamond.Prune (Checked carriedMask checkMask prune)
open Blocks.Prune (Mask)
open SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)

abbrev mask := carriedMask checked

def accepted : Checked checked mask :=
  (prune checked).get (by rfl)

def runCF (fuel : Nat) : Option Nat :=
  ((lower accepted).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def runRVSDG (activations : Nat) : Option Nat :=
  (accepted.lower.run (Join.model model) activations input).map (fun values => (values.get .head).toNat)

/-- Inspect the actual branch frames leaving the full and pruned CF entries. -/
def headerArities : Option Nat × Option Nat := by
  let entryArity {Labels : List Width → Type} (cfg : Cfg TargetOp Labels (Widths regs) [width]) :=
    match cfg.entry.eval evalOp (fun term env => term.eval env) (encodeValues input) with
    | .inl frame => some frame.argsTy.length
    | .inr _ => none
  exact (entryArity (CF.lower checked), entryArity (lower accepted))

def rejects (slot : Nat) : Bool :=
  (checkMask checked (Mask.ofSlots (fun i => i != slot) regs)).isNone

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example
