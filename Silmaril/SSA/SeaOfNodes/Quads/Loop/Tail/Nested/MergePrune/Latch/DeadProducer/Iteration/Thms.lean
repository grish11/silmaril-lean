module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Comparison.Thms

/-! # Exact observations of both emitters consuming one checked latch -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult nextBank sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

section Numbered

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch) (prepared : Prepared checked)

/-- The original γ selectors deliver the exact chosen predecessor column
to the emitted merge and shortened latch. -/
theorem numbered_packet_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (Numbered.DeadProducer.packetWith p projected checked prepared.final).toGraph.run (Join.model m)
        fuel (carry.project old) = some (observe p carry (nextBank p m old)) :=
  Numbered.DeadProducer.packetWith_run p m projected checked prepared.final (prepared.eval_eq m) fuel old

theorem numbered_activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (Numbered.DeadProducer.thetaWith p projected checked prepared.final).run (Join.model m)
        fuel (carry.project old) = some (MergePrune.Numbered.latchPacket p carry m (nextBank p m old)) :=
  Numbered.DeadProducer.thetaWith_run p m projected checked prepared.final (prepared.eval_eq m) fuel old

variable (result : KeptResult p (mask := carry)) (input : Bank (regs := regs) m)

theorem numbered_run (fuel : Nat) :
    (lowerNumbered p projected checked prepared result).run (Join.model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Numbered.DeadProducer.lowerWith_run p m projected checked prepared.final (prepared.eval_eq m) result input fuel

theorem numbered_returns_iff (value : sortValue m.value out) :
    (lowerNumbered p projected checked prepared result).Returns (Join.model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Numbered.DeadProducer.lowerWith_returns_iff p m projected checked prepared.final
    (prepared.eval_eq m) result input value

theorem numbered_noFiniteReturn_iff :
    (∀ fuel, (lowerNumbered p projected checked prepared result).run (Join.model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  Numbered.DeadProducer.lowerWith_noFiniteReturn_iff p m projected checked prepared.final
    (prepared.eval_eq m) result input

end Numbered

section CF

open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch) (prepared : Prepared checked)
variable (input : Bank (regs := regs) model)

theorem cf_latch_packet (old : Bank (regs := atLatch.kept) model) :
    ((lowerCF p projected checked prepared).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (MLIR.CF.packetFrame p (checked.latchTransfer.eval model old)) :=
  MLIR.CF.DeadProducer.lowerWith_latch_packet p projected checked prepared.final (prepared.eval_eq model) input old

theorem cf_run (fuel : Nat) :
    (lowerCF p projected checked prepared).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) :=
  MLIR.CF.DeadProducer.lowerWith_run p projected checked prepared.final (prepared.eval_eq model) input fuel

private theorem cf_agrees (fuel : Nat) :
    (lowerCF p projected checked prepared).run evalOp fuel (encodeValues input) =
      (MLIR.CF.lower p projected checked).run evalOp fuel (encodeValues input) :=
  MLIR.CF.DeadProducer.lowerWith_run_agrees p projected checked prepared.final (prepared.eval_eq model) input fuel

variable (result : KeptResult p (mask := carry))

private theorem numbered_agrees (fuel : Nat) :
    (lowerNumbered p projected checked prepared result).run (Join.model model) fuel input =
      (Numbered.lower p projected checked.whole result).run (Join.model model) fuel input :=
  Numbered.DeadProducer.lowerWith_run_agrees p model projected checked prepared.final (prepared.eval_eq model)
    result input fuel

/-- Match θ activations to selected source visits and the extra CF return visit. -/
theorem cf_at_activations (activations : Nat) :
    (lowerCF p projected checked prepared).run evalOp (sourceVisits p model activations input + 1)
        (encodeValues input) =
      ((lowerNumbered p projected checked prepared result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) := by
  simpa only [cf_agrees, numbered_agrees] using
    MLIR.CF.Comparison.cf_at_activations p projected checked result input activations

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (lowerCF p projected checked prepared).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((lowerNumbered p projected checked prepared result).run (Join.model model)
        activations input).map (encodeValues (ins := [out])) = some output := by
  simpa only [cf_agrees, numbered_agrees] using MLIR.CF.Comparison.cf_returns_iff p projected checked result input output

theorem cf_noFiniteReturn_iff :
    (lowerCF p projected checked prepared).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (lowerNumbered p projected checked prepared result).run (Join.model model)
        activations input = none := by
  simpa only [Silmaril.MLIR.CF.Cfg.Diverges, cf_agrees, numbered_agrees] using
    MLIR.CF.Comparison.cf_diverges_iff p projected checked result input

end CF

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration
