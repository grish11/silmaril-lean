module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (Names NamesAgree encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Frame)
open RVSDG (Tuple)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask)

private theorem jump_agrees :
    JumpAgrees (jump p.header mask (out := out)) (siteFrame p.header mask) := by
  intro _ _ _ _ _ input locals ok versions id
  by_cases different : id ≠ p.header
  · simp only [jump, siteFrame, dite_eq_left different]
    exact congrArg (fun args => Frame.mk (Label.site id different) args) (ok.operands_eval (ins := regs) versions)
  · simp only [jump, siteFrame, dite_eq_right different, headerFrame]
    have bank := ok.operands_eval (ins := mask.kept) (mask.project versions)
    rw [mask.project_read model input locals versions] at bank
    exact congrArg (fun args => Frame.mk Label.header args) bank

section Entry

variable {Γ : List Width} (names : Tuple (Names Γ) (dataPorts regs)) (env : Env Γ)

private theorem entry_eval_with (input : Bank (regs := regs) model) (ok : NamesAgree env names input) :
    (lowerWith checked names).entry.eval evalOp (fun term env => term.eval env) env =
      let next := (src entry).body.eval model input
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src entry).terminator.select model next)) :=
  CF.block_eval_with jump_agrees _ _ _ _ ok

private theorem header_eval_with (old : Bank (regs := regs) model) :
    ((lowerWith checked names).block .header).eval evalOp (fun term env => term.eval env)
        ((encodeValues (mask.project old)).append env) =
      let next := (src p.header).body.eval model old
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src p.header).terminator.select model next)) := by
  refine (CF.transfer_eval jump_agrees (past := []) (locals := PUnit.unit)
    ⟨CF.blockNames_agree env (mask.project old), trivial⟩
    checked.flow checked.outgoing (src p.header).terminator).trans ?_
  change
    (let next := checked.headerBank model (mask.project old)
     Sum.inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
       ((src p.header).terminator.select model next))) = _
  rw [checked.header_agrees model old]

theorem site_frame_with (old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame p.header mask (out := out) id old
    let next := (src id).body.eval model old
    ((lowerWith checked names).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append env) =
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src id).terminator.select model next)) := by
  by_cases different : id ≠ p.header
  · have current : siteFrame p.header mask (out := out) id old =
        ⟨.site id different, encodeValues old⟩ := by simp [siteFrame, different]
    dsimp only
    rw [current]
    exact CF.block_eval_with jump_agrees (src id) ⟨blockNames Γ regs, PUnit.unit⟩
      _ old (CF.blockNames_agree env old)
  · have same : id = p.header := not_ne_iff.mp different
    subst id
    have current : siteFrame p.header mask (out := out) p.header old = headerFrame p.header mask old := by
      simp [siteFrame]
    dsimp only
    rw [current]
    exact header_eval_with checked names env old

theorem lowerWith_run (fuel : Nat) (input : Bank (regs := regs) model) (ok : NamesAgree env names input) :
    (lowerWith checked names).run evalOp (fuel + 1) env =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  CF.runBlock_eq_of_frames_with (lowerWith checked names) env (siteFrame p.header mask) .exit
    (fun id old => site_frame_with checked names env old id) rfl fuel entry input _ _
    (entry_eval_with checked names env input ok)

end Entry

private theorem entry_eval (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      let next := (src entry).body.eval model input
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src entry).terminator.select model next)) :=
  entry_eval_with checked (entryNames regs) (encodeValues input) input (CF.entryNames_agree input)

theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame p.header mask (out := out) id old
    let next := (src id).body.eval model old
    ((lower checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src id).terminator.select model next)) :=
  site_frame_with checked (entryNames regs) (encodeValues input) old id

theorem entry_frame (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl (headerFrame p.header mask ((src entry).body.eval model input)) := by
  rw [entry_eval]
  simp [p.entryEdge, Tail.Terminator.select, destinationFrameWith, siteFrame]

theorem latch_frame (input old : Bank (regs := regs) model) :
    let current := siteFrame p.header mask (out := out) p.latch old
    let next := (src p.latch).body.eval model old
    ((lower checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (if (next.get p.again).down then headerFrame p.header mask next
        else exitFrame p.header mask (next.get p.result)) := by
  refine (site_frame checked input old p.latch).trans ?_
  simp only [p.latchEdge, Tail.Terminator.select]
  split <;> simp_all [destinationFrameWith, siteFrame]

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  lowerWith_run checked (entryNames regs) (encodeValues input) fuel input (CF.entryNames_agree input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Proofs
