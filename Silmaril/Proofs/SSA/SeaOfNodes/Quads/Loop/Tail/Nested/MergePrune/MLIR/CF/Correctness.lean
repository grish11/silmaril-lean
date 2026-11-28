module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Frame)
open Diamond.MLIR.CF (Widths JumpAgrees destinationFrameWith returnFrame entryNames_agree blockNames_agree
  block_eval_with runBlock_eq_of_frames_with)
open Diamond.MLIR.CF.Pruned (projectedBlock_eval)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Checked p merge)

theorem jump_agrees :
    JumpAgrees (jump p.header p.join carry merge (out := out)) (siteFrame p.header p.join carry merge) := by
  intro _ _ _ _ _ input locals ok versions id
  by_cases atHeader : id = p.header
  · simp only [jump, siteFrame, dite_eq_left atHeader, headerFrame]
    have bank := ok.operands_eval (ins := carry.kept) (carry.project versions)
    rw [carry.project_read model input locals versions] at bank
    exact congrArg (fun args => Frame.mk Label.header args) bank
  · by_cases atMerge : id = p.join
    · simp only [jump, siteFrame, dite_eq_right atHeader, dite_eq_left atMerge, mergeFrame]
      have bank := ok.operands_eval (ins := merge.kept) (merge.project versions)
      rw [merge.project_read model input locals versions] at bank
      exact congrArg (fun args => Frame.mk Label.merge args) bank
    · simp only [jump, siteFrame, dite_eq_right atHeader, dite_eq_right atMerge]
      exact congrArg (fun args => Frame.mk (Label.site id atHeader atMerge) args)
        (ok.operands_eval (ins := regs) versions)

theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame p.header p.join carry merge (out := out) id old
    let next := (src id).body.eval model old
    ((lower p projected checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p.header p.join carry merge) (returnFrame .exit) next
        ((src id).terminator.select model next)) := by
  by_cases atHeader : id = p.header
  · subst id
    have frame : siteFrame p.header p.join carry merge (out := out) p.header old =
        headerFrame p.header p.join carry merge old := by simp [siteFrame]
    dsimp only
    rw [frame]
    exact projectedBlock_eval (jump_agrees p) .exit (src p.header) projected (encodeValues input) old
  · by_cases atMerge : id = p.join
    · subst id
      have frame : siteFrame p.header p.join carry merge (out := out) p.join old =
          mergeFrame p.header p.join carry merge (merge.project old) := by simp [siteFrame, atHeader]
      dsimp only
      rw [frame]
      exact projectedBlock_eval (jump_agrees p) .exit (src p.join) checked (encodeValues input) old
    · have frame : siteFrame p.header p.join carry merge (out := out) id old =
          ⟨.site id atHeader atMerge, encodeValues old⟩ := by simp [siteFrame, atHeader, atMerge]
      dsimp only
      rw [frame]
      exact block_eval_with (jump_agrees p) (src id) _ _ old (blockNames_agree (encodeValues input) old)

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun result => Env.cons (valueBits result) .nil) :=
  runBlock_eq_of_frames_with (lower p projected checked) (encodeValues input)
    (siteFrame p.header p.join carry merge) .exit (fun id old => site_frame p projected checked input old id)
    rfl fuel entry input _ _ (block_eval_with (jump_agrees p) (src entry) _ _ _ (entryNames_agree input))

theorem source_diverges_iff (input : Bank (regs := regs) model) :
    (∀ fuel, src.runFrom model fuel entry input = none) ↔
      (lower p projected checked).Diverges evalOp (encodeValues input) := by
  constructor
  · intro exhausted fuel
    cases fuel with
    | zero => rfl
    | succ fuel => rw [lower_run, exhausted]; rfl
  · intro exhausted fuel
    have observed := exhausted (fuel + 1)
    rw [lower_run, Option.map_eq_none_iff] at observed
    exact observed

private theorem from_run (fuel : Nat) (input old : Bank (regs := regs) model) (id : Fin size) :
    (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.header p.join carry merge id old) =
      (src.runFrom model fuel id old).map (fun result => Env.cons (valueBits result) .nil) :=
  runBlock_eq_of_frames_with (lower p projected checked) (encodeValues input)
    (siteFrame p.header p.join carry merge) .exit (fun id old => site_frame p projected checked input old id)
    rfl fuel id old _ _ (site_frame p projected checked input old id)

private theorem join_ne_header : p.join ≠ p.header := by
  intro same
  have absent := (List.nodup_cons.mp (List.nodup_cons.mp p.distinct).2).1
  exact absent (by simp [← same])

theorem from_header_eq_merge (fuel : Nat) (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    (lower p projected checked).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input)
        (siteFrame p.header p.join carry merge p.header old) =
      (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input)
        (mergeFrame p.header p.join carry merge (incoming p merge model old occurrence)) := by
  dsimp only
  have frame : siteFrame p.header p.join carry merge (out := out) p.join
        (p.mergeBank model old (p.selected model old)) =
      mergeFrame p.header p.join carry merge (incoming p merge model old (p.selected model old)) := by
    simp [siteFrame, join_ne_header p, incoming]
  rw [← frame, from_run, from_run, p.run_to_merge]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Proofs
