module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Correctness

/-! # Compare actual CF, numbered θ and coloured completion -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (siteFrame exitFrame)
open RVSDG.NestedTheta.Petri (Finishes)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

/-- The actual CF edge packages the same full bank as the emitted outer γ,
at the original common-tail label. -/
theorem outer_arrival (fuel : Nat) (old : Bank (regs := regs) model) :
    some (outerArrival p input old) =
      ((Outer.Numbered.outerRegion p).toGraph.run (Join.model model) fuel old).map
        (fun bank => .inl (siteFrame p.stop bank)) := by
  rw [CF.outer_arrival, Outer.Numbered.outer_run]
  rfl

/-- CF feedback passes the full bank of the numbered activation. On exit
the existing typed return label takes just that bank's return slot. -/
theorem latch_successor (old : Bank (regs := regs) model) :
    let next := Outer.Numbered.nextBank p model old
    latchSuccessor p input old =
      .inl (if (next.get p.again).down then siteFrame p.header next else exitFrame (next.get p.result)) :=
  Proofs.latch_successor p input old

/-- Read the actual numbered activation's control port and carried data
ports to recover the CF successor frame. -/
theorem latch_successor_at_activation (fuel : Nat) (old : Bank (regs := regs) model) :
    some (latchSuccessor p input old) =
      ((Outer.Numbered.thetaBody p).toGraph.run (Join.model model) fuel old).map
        (fun
        | .cons route bank =>
          .inl (if route.down.val = 1 then siteFrame p.header bank else exitFrame (bank.get p.result))) := by
  rw [latch_successor, Outer.Numbered.activation_run]
  cases again : ((Outer.Numbered.nextBank p model old).get p.again).down <;>
    simp [RVSDG.Theta.bodyResult, again] <;> rfl

/-- CF spends the original source visits and one synthetic return visit.
The numbered graph spends θ activations. -/
theorem cf_at_activations (activations : Nat) :
    (CF.lower p).run evalOp (Outer.Numbered.sourceVisits p model activations input + 1) (encodeValues input) =
      ((Outer.Numbered.lower p).run (Join.model model) activations input).map (encodeValues (ins := [out])) := by
  rw [CF.lower_run, Outer.Numbered.lower_run, Option.map_map]
  rfl

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (CF.lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ activations, ((Outer.Numbered.lower p).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output :=
  Proofs.cf_returns_iff p input output

theorem cf_noFiniteReturn_iff :
    (CF.lower p).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (Outer.Numbered.lower p).run (Join.model model) activations input = none :=
  (CF.source_noFiniteReturn_iff p input).trans (Outer.Numbered.noFiniteReturn_iff p model input).symm

/-- An independent finite firing witness returns the packet encoding the
actual CF result. -/
theorem cf_finishes_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (CF.lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ packet, Finishes (Join.model model) (Outer.Numbered.lower p) input packet ∧
        encodeValues (ins := [out]) packet = output :=
  Proofs.cf_finishes_iff p input output

theorem cf_noCompletion_iff :
    (CF.lower p).Diverges evalOp (encodeValues input) ↔
      ∀ packet, ¬ Finishes (Join.model model) (Outer.Numbered.lower p) input packet :=
  Proofs.cf_noCompletion_iff p input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison
