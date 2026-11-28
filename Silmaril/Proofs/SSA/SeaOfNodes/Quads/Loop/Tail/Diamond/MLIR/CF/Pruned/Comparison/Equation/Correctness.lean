module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation.Proofs

open SeaOfNodes.Diamond (Val ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)
open RVSDG (Tuple)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {w : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data w) leftSize}
variable {rightSource : Source Op regs (.data w) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

theorem rvsdg_observe_eq_native (checked : Checked left leftMask) (input : Bank (regs := regs) model) :
    checked.lower.denotePart (Join.model model) input = left.lower.denotePart (Join.model model) input := by
  apply Part.ext
  intro result
  rw [checked.lower.mem_denote, left.lower.mem_denote, ← checked.lower.returns_iff, ← left.lower.returns_iff]
  exact exists_congr fun fuel => by rw [checked.run_agrees model fuel input]

private def decodeResult (result : Outcome [w]) : Tuple (Val Word) [.value (.data w)] :=
  match result with
  | .returned env => .cons (env.get .here) .nil
  | .aborted => .cons (BitVec.ofNat w.val 0 : Word w) .nil

private theorem decodeResult_encode (values : Tuple (Val Word) [.value (.data w)]) :
    decodeResult (.returned (encodeValues (ins := [.data w]) values)) = values := by
  cases values with | cons value tail => cases tail; rfl

theorem cf_at_iff (lhs : Checked left leftMask) (rhs : Checked right rightMask)
    (input : Bank (regs := regs) model) :
    observeCF lhs (encodeValues input) = observeCF rhs (encodeValues input) ↔
      left.lower.denotePart (Join.model model) input = right.lower.denotePart (Join.model model) input := by
  unfold observeCF
  rw [Comparison.denotePart_eq, Comparison.denotePart_eq, rvsdg_observe_eq_native, rvsdg_observe_eq_native]
  constructor
  · intro equal
    let encode (values : Tuple (Val Word) [.value (.data w)]) : Outcome [w] :=
      .returned (encodeValues (ins := [.data w]) values)
    have cancel (obs : Part (Tuple (Val Word) [.value (.data w)])) :
        (obs.map encode).map (decodeResult (w := w)) = obs :=
      (Part.map_map (decodeResult (w := w)) encode obs).trans
        (Part.map_id' (fun values => decodeResult_encode values) obs)
    exact (cancel _).symm.trans ((congrArg (Part.map (decodeResult (w := w))) equal).trans (cancel _))
  · exact congrArg _

theorem encodeValues_surjective (regs : List (ValueSort Width)) :
    Function.Surjective (encodeValues (ins := regs)) := by
  induction regs with
  | nil =>
    intro env
    cases env
    exact ⟨.nil, rfl⟩
  | cons slot rest ih =>
    intro env
    cases env with
    | cons value tail =>
      obtain ⟨bank, encoded⟩ := ih tail
      cases slot with
      | data width => exact ⟨.cons value bank, congrArg (Env.cons value) encoded⟩
      | predicate =>
        refine ⟨.cons ⟨value.getLsbD 0⟩ bank, ?_⟩
        have bit : BitVec.ofBool (value.getLsbD 0) = value :=
          BitVec.setWidth_one.symm.trans (BitVec.setWidth_eq value)
        exact congrArg₂ Env.cons bit encoded

theorem rvsdg_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (prunedEquation lhs rhs).Holds (Join.model model) ↔ (nativeEquation left right).Holds (Join.model model) := by
  change (∀ input : Bank (regs := regs) model,
      lhs.lower.denotePart (Join.model model) input = rhs.lower.denotePart (Join.model model) input) ↔
    ∀ input : Bank (regs := regs) model,
      left.lower.denotePart (Join.model model) input = right.lower.denotePart (Join.model model) input
  simp only [rvsdg_observe_eq_native]

theorem cf_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (∀ input : Env (Widths regs), observeCF lhs input = observeCF rhs input) ↔
      (nativeEquation left right).Holds (Join.model model) := by
  constructor
  · intro agrees input
    exact (cf_at_iff lhs rhs input).mp (agrees (encodeValues input))
  · intro holds env
    obtain ⟨input, rfl⟩ := encodeValues_surjective regs env
    exact (cf_at_iff lhs rhs input).mpr (holds input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation.Proofs
