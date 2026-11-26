module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.PhiView.Thms

/-! # Positional Φ latching agrees with the emitted CF and numbered γ/θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Atom Width Env)
open Silmaril.Isotope (Value)
open Diamond.MLIR.CF (Widths siteFrame destinationFrame source_site_eval)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

/-- Every admitted outer plan supplies both original CF incoming rows. -/
theorem readRows_exists : ∃ rows, readRows p = some rows :=
  Proofs.rows_exist p

variable {p} (rows : Rows p) (input old : Bank (regs := regs) model)

/-- The selected row reads the full post-edge bank in destination order,
including untouched registers and predicate slots. -/
theorem Rows.selected_bank :
    rows.selectedBank input old = encodeValues (p.outerBank model old (p.toControl.selected model old)) :=
  Proofs.selected_bank p rows input old

theorem Rows.actual_arrival :
    CF.outerArrival p input old = .inl (rows.selectedFrame input old) := by
  rw [CF.outer_arrival, selectedFrame, rows.selected_bank]
  rfl

/-- The existing positional Φ latch and the actual CF operands agree. -/
theorem Rows.latch_eq :
    rows.latch input old = pack (rows.selectedBank input old) :=
  Proofs.latch_eq p rows input old

/-- The packed branch has the same selected payload under the existing
explicit Φ transfer law. -/
theorem Rows.transfer_iff (label : Nat) (payload : Value Atom) :
    Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval Silmaril.MLIR.Arith.instr
      (arrivalEnv (p := p) input old).toLambdaSSA
      (.br p.stop.val (rows.edge (arrivalSide (p := p) old)).argument) () label payload () ↔
      label = p.stop.val ∧ payload = pack (rows.selectedBank input old) := by
  rw [← rows.latch_eq]
  simpa only [Rows.latch, Rows.edge, Rows.terminators, PhiView.EdgeOcc.target, PhiView.Successor.target, and_true] using
    PhiView.latch_eq_transfer Silmaril.MLIR.Arith.instr rows.view (rows.edge (arrivalSide (p := p) old))
      (arrivalEnv (p := p) input old).toLambdaSSA () () label payload

/-- The first original tail block runs with the latched argument packet.
The dominating external inputs remain in their original scope. -/
theorem Rows.first_tail :
    ((lower p).block (.site p.stop)).eval evalOp (fun term env => term.eval env)
        ((rows.selectedBank input old).append (encodeValues input)) =
      let next := (src p.stop).body.eval model (p.outerBank model old (p.toControl.selected model old))
      .inl (destinationFrame next ((src p.stop).terminator.select model next)) := by
  rw [rows.selected_bank]
  exact source_site_eval (entry := entry) input _ p.stop

theorem Rows.from_header (fuel : Nat) :
    (lower p).runFrom evalOp (fuel + p.outerVisits (p.toControl.selected model old) + 1)
        (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (rows.selectedFrame input old) := by
  rw [selectedFrame, rows.selected_bank]
  exact CF.from_header_eq_tail p input fuel old

/-- The actual outer γ returns the selected CF/Φ bank, before the shared
tail executes once. Whole-loop observations use the existing Comparison laws. -/
theorem Rows.numbered_latch (fuel : Nat) :
    ((Outer.Numbered.outerRegion p).toGraph.run (Join.model model) fuel old).map
        (fun bank => pack (encodeValues bank)) = some (rows.latch input old) := by
  rw [Outer.Numbered.outer_run, rows.latch_eq, rows.selected_bank]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi
