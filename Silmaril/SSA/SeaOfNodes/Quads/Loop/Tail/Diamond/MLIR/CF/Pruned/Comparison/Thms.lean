module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Correctness

/-! # Partial agreement of the pruned typed CF and numbered RVSDG emitters -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask) (input : Bank (regs := regs) model)

/-- The CF witness budget counts the original blocks on the selected
source arms and one additional visit for the typed return. -/
theorem run_at_source_visits (activations : Nat) :
    (lower checked).run evalOp (p.sourceVisits model activations input + 1) (encodeValues input) =
      (checked.lower.run (Join.model model) activations input).map (encodeValues (ins := [out])) :=
  Proofs.run_at_source_visits checked input activations

/-- At the common typed boundary, either target's finite return witnesses
the same encoded result at a finite budget on the other target. -/
theorem returns_iff (output : Env [valueWidth out]) :
    (∃ fuel, (lower checked).run evalOp fuel (encodeValues input) = some output) ↔
      ∃ activations,
        (checked.lower.run (Join.model model) activations input).map (encodeValues (ins := [out])) = some output :=
  Proofs.returns_iff checked input output

/-- Compare the existing partial observations of the actual emitted graphs.
An RVSDG singleton result encodes to a returned CF result environment. -/
theorem denotePart_eq :
    (Cfg.embed (lower checked)).denotePart evalOp (encodeValues input) =
      (checked.lower.denotePart (Join.model model) input).map
        (fun values => Outcome.returned (encodeValues (ins := [out]) values)) :=
  Proofs.denotePart_eq checked input

/-- The original source has no finite return exactly when the emitted CF
has none. Composing with `diverges_iff` gives the same result for RVSDG. -/
theorem source_diverges_iff :
    (∀ fuel, src.runFrom model fuel entry input = none) ↔
      (lower checked).Diverges evalOp (encodeValues input) :=
  Proofs.source_diverges_iff checked input

/-- Absence of any finite CF return agrees with absence of any finite
RVSDG return, quantified over each target's own budget. -/
theorem diverges_iff :
    (lower checked).Diverges evalOp (encodeValues input) ↔
      ∀ activations, checked.lower.run (Join.model model) activations input = none :=
  Proofs.diverges_iff checked input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison
