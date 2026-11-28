module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Thms

/-! # Exact original CF occurrences and budgets through the narrower cut -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF

open SeaOfNodes.Diamond (Dataflow ValueSort dataPorts)
open RVSDG (Wires extend)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (destinationFrameWith)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)

/-- Executing the emitted latch reads the full outgoing packet before
selecting its successor. -/
theorem latchCode_eval {sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
    (flow : Dataflow Op (dataPorts atLatch.kept) [] sigs)
    (packet : Wires (dataPorts atLatch.kept) (extend [] sigs) (packetPorts out carry))
    (input : Bank (regs := regs) model) (old : Bank (regs := atLatch.kept) model) :
    (latchCode (carry := carry) (merge := merge) (atLatch := atLatch) p flow packet).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (packetFrame p (packet.read old (flow.eval model old PUnit.unit))) :=
  Proofs.latchCode_eval p flow packet input old

/-- The emitted merge passes exactly the latch’s projected post-merge versions. -/
theorem merge_frame (input old : Bank (regs := regs) model) :
    ((lower p projected checked).block (.base .merge)).eval evalOp (fun term env => term.eval env)
        ((encodeValues (merge.project old)).append (encodeValues input)) =
      .inl (latchFrame p (atLatch.project ((src p.join).body.eval model old))) :=
  Proofs.merge_frame p projected checked input old

/-- The actual latch tests its resolved predicate and routes the exact exit word or simultaneous feedback. -/
theorem latch_frame (input old : Bank (regs := regs) model) :
    ((lower p projected checked).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues (atLatch.project old)).append (encodeValues input)) =
      let next := (src p.latch).body.eval model old
      .inl (if (next.get p.again).down then headerFrame p (carry.project next) else exitFrame p (next.get p.result)) :=
  Proofs.latch_frame p projected checked input old

/-- Every original block selects its original destination with the corresponding typed arguments. -/
theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame (carry := carry) (merge := merge) (atLatch := atLatch) p id old
    let next := (src id).body.eval model old
    ((lower p projected checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p) (exitFrame p) next ((src id).terminator.select model next)) :=
  Proofs.site_frame p projected checked input old id

/-- The selected original predecessor sends precisely its compiled projected incoming bank, including a direct edge from the inner split. -/
theorem selected_predecessor_frame (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    let frame := siteFrame p (p.predecessor occurrence) (predecessorBank p old occurrence)
    ((lower p projected checked).block frame.label).eval evalOp (fun term env => term.eval env)
      (frame.args.append (encodeValues input)) =
      .inl (mergeFrame p (incoming p merge model old occurrence)) :=
  Proofs.selected_predecessor_frame p projected checked input old

/-- The original selected path resumes at the common merge with its checked projected input and unchanged visit count. -/
theorem from_header_eq_merge (fuel : Nat) (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    (lower p projected checked).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input)
        (siteFrame p p.header old) =
      (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input)
        (mergeFrame p (incoming p merge model old occurrence)) :=
  Proofs.from_header_eq_merge p projected checked fuel input old

/-- The original blocks each cost one visit. Only the typed CF return adds a visit. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) :=
  Proofs.lower_run p projected checked fuel input

/-- A replacement with identical latch frames preserves the same CF
visit accounting and source observation. -/
theorem withLatch_lower_run
    (block : LatchBlock (carry := carry) (merge := merge) (atLatch := atLatch) p)
    (input : Bank (regs := regs) model)
    (agrees : ∀ old : Bank (regs := regs) model,
      block.eval evalOp (fun term env => term.eval env)
          ((encodeValues (atLatch.project old)).append (encodeValues input)) =
        ((lower p projected checked).block .latch).eval evalOp (fun term env => term.eval env)
          ((encodeValues (atLatch.project old)).append (encodeValues input)))
    (fuel : Nat) :
    (withLatch p (lower p projected checked) block).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) :=
  Proofs.withLatch_lower_run p projected checked block input agrees fuel

/-- Finite source and CF returns give the same encoded result, with a witness in each runner’s own budget. -/
theorem source_returns_iff (input : Bank (regs := regs) model) (output : Env [valueWidth out]) :
    (∃ fuel, (lower p projected checked).run evalOp fuel (encodeValues input) = some output) ↔
      ∃ fuel, (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) = some output :=
  Proofs.source_returns_iff p projected checked input output

/-- The source and emitted CF agree on absence of any finite return. -/
theorem source_diverges_iff (input : Bank (regs := regs) model) :
    (lower p projected checked).Diverges evalOp (encodeValues input) ↔
      ∀ fuel, src.runFrom model fuel entry input = none :=
  Proofs.source_diverges_iff p projected checked input

theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp fuel (encodeValues input) =
      (Nested.MLIR.CF.lower p projected).run evalOp fuel (encodeValues input) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [lower_run, Nested.MLIR.CF.lower_run]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF
