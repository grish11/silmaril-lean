module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Activation
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Correctness

/-! A single original coloured run can visit both γ checkpoints of each
reached activation before completing the emitted θ. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open Silmaril.MLIR.Arith (Width Env)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Finishes)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

theorem activation (old : Bank (regs := regs) model) :
    let next := nextBank p model old
    Nonempty (Activation p old (packetsAt p old) (next.get p.again).down next) :=
  Proofs.activation p old

theorem trace_of_windows {packets : List (Packets regs size)} {final : Bank (regs := regs) model}
    (windows : Windows p ((src entry).body.eval model input) packets final) :
    Nonempty (Trace p input packets final) :=
  Proofs.trace_of_windows p input windows

theorem trace_of_run (fuel : Nat) (value : sortValue model.value out)
    (run : (lower p).run semantics fuel input = some (.cons value .nil)) :
    ∃ packets final, final.get p.result = value ∧ Nonempty (Trace p input packets final) :=
  Proofs.trace_of_run p input fuel value run

/-- Complete typed packets coincide with the ordered CF successor/Φ
readbacks at the selected occurrences of this activation. -/
theorem packetsAt_cf (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (old : Bank (regs := regs) model) :
    (packetsAt p old).encode = cfPacketsAt p inner outer input old :=
  Proofs.packetsAt_cf p input inner outer old

theorem Windows.cf_packets (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    {old final : Bank (regs := regs) model} {packets : List (Packets regs size)}
    (windows : Windows p old packets final) :
    packets.map Packets.encode = (Windows.inputs p windows).map (cfPacketsAt p inner outer input) := by
  induction windows with
  | stop => exact congrArg (fun bank => [bank]) (packetsAt_cf p input inner outer _)
  | again _ _ ih => exact congrArg₂ List.cons (packetsAt_cf p input inner outer _) ih

/-- At the end of each observed window, the actual CF latch selects
the same complete feedback bank or the corresponding typed exit. -/
theorem Activation.cf_latch {old next : Bank (regs := regs) model} {packets : Packets regs size} {again : Bool}
    (window : Activation p old packets again next) :
    MLIR.CF.latchSuccessor p input old =
      .inl (if again then Diamond.MLIR.CF.siteFrame p.header next
        else Diamond.MLIR.CF.exitFrame (next.get p.result)) :=
  Proofs.cf_latch p input window

variable {p input}

theorem Visits.erase {M : Type} {step : M → M → Prop}
    {start last : M} {marks : List M} (visits : Visits step start marks last) :
    ReflTransGen step start last :=
  Proofs.erase_visits visits

/-- Concatenation forgets checkpoints and replays as Step of the
original emitted graph. -/
theorem Trace.replay {packets : List (Packets regs size)} {final : Bank (regs := regs) model}
    (trace : Trace p input packets final) :
    Finishes semantics (lower p) input (.cons (final.get p.result) .nil) :=
  Proofs.trace_replay trace

variable (p input)

theorem trace_iff_source (value : sortValue model.value out) :
    (∃ packets final, final.get p.result = value ∧ Nonempty (Trace p input packets final)) ↔
      ∃ bound, src.runFrom model bound entry input = some value :=
  Proofs.trace_iff_source p input value

/-- Compare completion with the real emitted CF at an independent visit
bound. The left witness retains all coloured join checkpoints. -/
theorem trace_iff_cf (output : Env [valueWidth out]) :
    (∃ packets final, encodeValues (ins := [out]) (.cons (final.get p.result) .nil) = output ∧
      Nonempty (Trace p input packets final)) ↔
      ∃ bound, (MLIR.CF.lower p).run evalOp bound (encodeValues input) = some output :=
  Proofs.trace_iff_cf p input output

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
