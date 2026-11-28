module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Correctness

/-! # Exact projected CF edge and return agreement -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (JumpAgrees destinationFrameWith returnFrame)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Checked p merge)

/-- Read each edge in the scope of the predecessor's own versions. -/
theorem jump_agrees (carry merge : Mask regs) :
    JumpAgrees (jump p.header p.join carry merge (out := out)) (siteFrame p.header p.join carry merge) :=
  Proofs.jump_agrees p

/-- The actual emitted block takes its original successor and sends that
successor exactly the projected post-block versions. -/
theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame p.header p.join carry merge (out := out) id old
    let next := (src id).body.eval model old
    ((lower p projected checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p.header p.join carry merge) (returnFrame .exit) next
        ((src id).terminator.select model next)) :=
  Proofs.site_frame p projected checked input old id

/-- Resume from the smaller CF join with the exact selected occurrence's bank. -/
theorem from_header_eq_merge (fuel : Nat) (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    (lower p projected checked).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input)
        (siteFrame p.header p.join carry merge p.header old) =
      (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input)
        (mergeFrame p.header p.join carry merge (incoming p merge model old occurrence)) :=
  Proofs.from_header_eq_merge p projected checked fuel input old

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun result => Env.cons (valueBits result) .nil) :=
  Proofs.lower_run p projected checked fuel input

/-- The source and projected CF agree on absence at every finite budget. -/
theorem source_diverges_iff (input : Bank (regs := regs) model) :
    (∀ fuel, src.runFrom model fuel entry input = none) ↔
      (lower p projected checked).Diverges evalOp (encodeValues input) :=
  Proofs.source_diverges_iff p projected checked input

/-- Join projection changes no bounded observation in the existing typed CFG. -/
theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp fuel (encodeValues input) =
      (Nested.MLIR.CF.lower p projected).run evalOp fuel (encodeValues input) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [lower_run, Nested.MLIR.CF.lower_run]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF
