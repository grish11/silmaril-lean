module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Example.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Waiting
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Continuation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Mathlib.Data.List.Chain

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input regs width)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example (rows)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi (headerBank side)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example renaming rows → outerRows
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Join.Finite (lastBank)
open Blocks (Bank)
open Relation (ReflTransGen)
open RVSDG.NestedTheta (Term Graph)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending finishes_term_iff finishes_iff Finishes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)

local notation "EntryCode" => entryCode (src := Numbered.Example.source) (entry := 0)
local notation "Preheader" => Term.ofBase EntryCode
local notation "EntryMark" => Marking semantics Preheader
local notation "BodyMark" => Marking semantics (thetaBody plan)
local notation "RootFire" => Fire semantics (emitted plan) input PUnit.unit
local notation "BankType" => Bank (regs := regs) model

private theorem recorded_of_reaches {M : Type} {step : M → M → Prop} {start last : M}
    (steps : ReflTransGen step start last) :
    ∃ rest, List.IsChain step (start :: rest) ∧ rest.getLastD start = last := by
  induction steps using ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .singleton _, rfl⟩
  | @head before next step _ ih =>
    obtain ⟨rest, legal, last⟩ := ih
    exact ⟨next :: rest, List.isChain_cons_cons.mpr ⟨step, legal⟩, List.getLastD_cons.trans last⟩

private theorem enter_body (preheader : EntryMark)
    (steps : ReflTransGen (Fire semantics Preheader input PUnit.unit) (pending semantics Preheader) preheader)
    (done : finished semantics Preheader input PUnit.unit preheader = some (activation 0)) :
    ReflTransGen RootFire (pending semantics (emitted plan))
      (atBody plan preheader (activation 0) (pending semantics (thetaBody plan))) := by
  let cut := entryCut plan
  have ready := cut.read_after semantics input PUnit.unit preheader _ done
  change RVSDG.Petri.read (baseCut entryCode _).wires _ _ = _ at ready
  rw [Proofs.base_cut_wires] at ready
  exact (cut.prefix_reaches semantics input PUnit.unit steps).trans
    (cut.tail_reaches semantics input PUnit.unit preheader (.single (.enter ready rfl)))

private theorem root_body (preheader : EntryMark) (old : BankType) {before after : BodyMark}
    (steps : ReflTransGen (Fire semantics (thetaBody plan) old PUnit.unit) before after) :
    ReflTransGen RootFire (atBody plan preheader old before) (atBody plan preheader old after) := by
  let cut := entryCut plan
  let tail := iterateThenReturnWith (thetaBody plan) plan.result (endWires EntryCode)
  exact cut.tail_reaches semantics input PUnit.unit preheader
    (steps.lift (p := Fire semantics tail input (cut.tokens semantics PUnit.unit preheader))
      (fun mark => (.waiting (0 : Fin 1) (old, mark), PUnit.unit)) (fun _ _ step => .advance step))

private theorem fire_latch (preheader : EntryMark) {old next : BankType} {again : Bool}
    (window : Activation plan old (packetsAt plan old) again next) :
    RootFire (atBody plan preheader old window.final) (afterLatch plan preheader again next) := by
  cases again with
  | false =>
    apply (entryCut plan).lift_tail_step semantics input PUnit.unit preheader
    exact .commit window.latched rfl
  | true =>
    apply (entryCut plan).lift_tail_step semantics input PUnit.unit preheader
    exact .restart window.latched rfl rfl

-- Each exact cut must occur on the supplied body record. The matching
-- root step may then only restart or commit the original θ.
private theorem window_checked (preheader : EntryMark)
    (preDone : (finished semantics Preheader input PUnit.unit preheader).isSome)
    (old : BankType)
    (window : Activation plan old (packetsAt plan old) ((nextBank plan model old).get plan.again).down
      (nextBank plan model old)) :
    let next := nextBank plan model old
    ReflTransGen RootFire (atBody plan preheader old (pending semantics (thetaBody plan)))
      (afterLatch plan preheader (next.get plan.again).down next) ∧
    readOuter plan old window.final = some (packetsAt plan old).outer.2 ∧
    (plan.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := plan) old),
      encodeValues (packetsAt plan old).outer.2) = (cfPacketsAt plan rows outerRows input old).2 := by
  let steps := window.entered.trans (window.joined.trans window.continued)
  have completed := Option.isSome_iff_exists.mpr ⟨_, window.latched⟩
  obtain ⟨record, legal, last⟩ := recorded_of_reaches steps
  have recordDone : (finished semantics (thetaBody plan) old PUnit.unit
      (record.getLastD (pending semantics (thetaBody plan)))).isSome := last ▸ completed
  obtain ⟨earlier, before, after, later, split, absent, beforeRead, step, read, stayed⟩ :=
    first_outer_read plan old record legal recordDone
  rw [last] at stayed
  have bank : readOuter plan old window.final = some (packetsAt plan old).outer.2 := by
    change finished semantics (outerRegion plan) old PUnit.unit
      ((outerCut plan).2.2.observe semantics after) = _ at read
    change finished semantics (outerRegion plan) old PUnit.unit
      ((outerCut plan).2.2.observe semantics window.final) = _
    exact stayed ▸ read
  have fired := fire_latch preheader window
  have decided := latch_step plan old input preDone steps completed fired
  exact ⟨(root_body preheader old steps).tail (decided.1 ▸ fired), bank,
    readOuter_cf plan old input rows outerRows steps bank⟩

set_option maxHeartbeats 1000000 in
example : Finishes semantics (lower plan) input (.cons (152 : Word width) .nil) := by
  have preheaderReturns : (Term.toGraph Preheader).Returns semantics input (activation 0) := ⟨0, rfl⟩
  obtain ⟨pre, enters, readPre⟩ := (finishes_term_iff semantics Preheader input (activation 0)).mp
    ((finishes_iff semantics (Term.toGraph Preheader) input (activation 0)).mpr preheaderReturns)
  have preDone := Option.isSome_iff_exists.mpr ⟨_, readPre⟩
  obtain ⟨first⟩ := Petri.activation plan (activation 0)
  obtain ⟨second⟩ := Petri.activation plan (activation 1)
  obtain ⟨last⟩ := Petri.activation plan (activation 2)
  have firstNext := (window_checked pre preDone (activation 0) first).1
  have secondNext := (window_checked pre preDone (activation 1) second).1
  have exit := (window_checked pre preDone (activation 2) last).1
  have start := enter_body pre enters readPre
  have reached := start.trans (firstNext.trans (secondNext.trans exit))
  refine (finishes_term_iff semantics (emitted plan) input _).mpr ⟨_, reached, ?_⟩
  let cut := entryCut plan
  refine (cut.finished_attach semantics input PUnit.unit pre (.done stoppingBank, PUnit.unit) readPre).trans ?_
  let colours := (cut.tokens semantics PUnit.unit pre).snoc (stoppingBank.map fun _ => some)
  change RVSDG.Petri.collect (.cons
    (RVSDG.Petri.colour input colours ((lastBank _ _).get plan.result)) .nil) = _
  have returned : RVSDG.Petri.colour input colours ((lastBank _ _).get plan.result) = some (152 : Word width) := by
    rw [lastBank, get_tabulate]
    exact Proofs.last_colour plan.result _ stoppingBank
  rw [returned]
  rfl

-- The selected child is checked independently of the root witness above.
set_option maxHeartbeats 1000000 in
example :
    let child := Prefix.outerArm plan.toRoutes 1
    let header := headerBank plan.toRoutes (activation 2)
    ∃ mark : Marking semantics child,
      ReflTransGen (Fire semantics child header PUnit.unit) (pending semantics child) mark ∧
      (finished semantics child header PUnit.unit mark).isSome ∧
      (readInner plan (activation 2) 1 mark).map
        (fun bank => (plan.toRoutes.innerEdgeOccurrence (side plan.toRoutes (activation 2)), bank)) = none := by
  let code := plan.outerFalse.quads.lowerFrom (initial regs) .jump
  let child := Term.ofBase code
  let header := headerBank plan.toRoutes (activation 2)
  let value := code.run semantics header
  have ret : child.toGraph.Returns semantics header value := by
    refine ⟨0, ?_⟩
    rw [← Graph.run_toTerm, Term.toTerm_toGraph]
    exact Term.run_ofBase code semantics 0 header
  obtain ⟨mark, reached, done⟩ := (finishes_term_iff semantics child header value).mp
    ((finishes_iff semantics child.toGraph header value).mpr ret)
  have completed := Option.isSome_iff_exists.mpr ⟨_, done⟩
  exact ⟨mark, reached, completed, completed_child_packet plan (activation 2) 1 (by rfl) reached completed⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
