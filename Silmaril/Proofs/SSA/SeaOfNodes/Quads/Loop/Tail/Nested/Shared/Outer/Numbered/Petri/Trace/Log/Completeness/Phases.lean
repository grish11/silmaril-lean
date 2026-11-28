module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Continuation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Thms

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending finished_no_step)
open RVSDG.NestedTheta.Petri.Replay (pending_theta unfinished_theta committed_theta)
open RVSDG.Petri (Vertex)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

local notation "entryWires" => endWires (entryCode (src := src) (entry := entry))

theorem pending_cell {before : RootMark p}
    (was : thetaPending p before = true) :
    (entryCut p).rest semantics before = (.pending, PUnit.unit) := by
  apply Prod.ext ?_ (Subsingleton.elim (α := PUnit) _ _)
  unfold thetaPending at was
  split at was
  · rename_i _ eq
    exact eq
  · cases was

theorem start_pending : thetaPending p (pending semantics (emitted p)) = true := by
  let cut := entryCut p
  let tail := iterateThenReturnWith (thetaBody p) p.result entryWires
  have initial : pending semantics (emitted p) =
      cut.attach semantics (pending semantics (preheader p)) (pending semantics tail) :=
    (cut.attach_pending semantics).symm
  refine (congrArg (thetaPending p) initial).trans ?_
  unfold thetaPending
  rw [cut.rest_attach]
  rfl

theorem fresh_not_pending (pre : PreMark p) (bank : Bank (regs := regs) model) (body : BodyMark p) :
    thetaPending p (atBody p pre bank body) = false := by
  unfold thetaPending atBody
  rw [(entryCut p).rest_attach]

theorem pending_not_finished {mark : RootMark p} (still : thetaPending p mark = true) :
    ¬ (finished semantics (emitted p) input PUnit.unit mark).isSome := by
  intro done
  obtain ⟨result, returned⟩ := Option.isSome_iff_exists.mp done
  let cut := entryCut p
  obtain ⟨_, ready⟩ := cut.completed_prefix semantics input mark returned
  have same := cut.finished_attach semantics input PUnit.unit (cut.observe semantics mark)
    (cut.rest semantics mark) ready
  rw [cut.attach_observe_rest, pending_cell p still] at same
  have absent : finished semantics (emitted p) input PUnit.unit mark = none := same
  cases returned.symm.trans absent

theorem waiting_not_finished (pre : PreMark p) (old : Bank (regs := regs) model)
    (body : BodyMark p) {bank : Bank (regs := regs) model}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some bank) :
    ¬ (finished semantics (emitted p) input PUnit.unit (atBody p pre old body)).isSome := by
  have absent : finished semantics (emitted p) input PUnit.unit (atBody p pre old body) = none :=
    (entryCut p).finished_attach semantics input PUnit.unit pre
      (.waiting (0 : Fin 1) (old, body), PUnit.unit) preDone
  rw [absent]
  exact Bool.noConfusion

theorem from_pending {before after : RootMark p}
    (was : thetaPending p before = true) (step : RootFire p input before after) :
    thetaPending p after = true ∨
      ∃ bank, RVSDG.Petri.read entryWires input ((entryCut p).tokens semantics PUnit.unit
          ((entryCut p).observe semantics after)) = some bank ∧
        after = atBody p ((entryCut p).observe semantics after) bank (pending semantics (thetaBody p)) := by
  let cut := entryCut p
  rcases cut.split_step semantics input PUnit.unit step with ⟨_, steady⟩ | ⟨steady, fired⟩
  · apply Or.inl
    unfold thetaPending at was ⊢
    exact (congrArg (fun mark => match mark.1 with
      | Vertex.pending => true | _ => false) steady).symm.trans was
  · apply Or.inr
    rw [pending_cell p was, steady] at fired
    obtain ⟨bank, read, phase⟩ := pending_theta semantics (thetaBody p) entryWires _
      input (cut.tokens semantics PUnit.unit (cut.observe semantics after)) fired
    refine ⟨bank, read, ?_⟩
    exact (cut.attach_observe_rest semantics after).symm.trans
      (congrArg (cut.attach semantics (cut.observe semantics after)) phase)

theorem advance {pre : PreMark p} {old : Bank (regs := regs) model} {body : BodyMark p}
    {after : RootMark p} {bank : Bank (regs := regs) model}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some bank)
    (waiting : finished semantics (thetaBody p) old PUnit.unit body = none)
    (step : RootFire p input (atBody p pre old body) after) :
    ∃ next, BodyFire p old body next ∧ after = atBody p pre old next := by
  let cut := entryCut p
  let tail := iterateThenReturnWith (thetaBody p) p.result entryWires
  let mark : RVSDG.NestedTheta.Petri.Marking semantics tail :=
    (.waiting (0 : Fin 1) (old, body), PUnit.unit)
  change RootFire p input (cut.attach semantics pre mark) after at step
  rcases cut.split_step semantics input PUnit.unit step with ⟨fires, _⟩ | ⟨steady, fires⟩
  · rw [cut.observe_attach] at fires
    exact False.elim (finished_no_step semantics _ _ _ preDone fires)
  · rw [cut.observe_attach] at steady fires
    rw [cut.rest_attach] at fires
    obtain ⟨next, one, phase⟩ := unfinished_theta semantics (thetaBody p) entryWires _
      input (cut.tokens semantics PUnit.unit pre) old body waiting fires
    refine ⟨next, one, ?_⟩
    exact (cut.attach_observe_rest semantics after).symm.trans
      ((congrArg (fun saved => cut.attach semantics saved (cut.rest semantics after)) steady.symm).trans
        (congrArg (cut.attach semantics pre) phase))

theorem committed_no_step {pre : PreMark p} {bank : Bank (regs := regs) model}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some bank)
    (result : Bank (regs := regs) model) {after : RootMark p}
    (step : RootFire p input (afterLatch p pre false result) after) : False := by
  let cut := entryCut p
  let tail := iterateThenReturnWith (thetaBody p) p.result entryWires
  let mark : RVSDG.NestedTheta.Petri.Marking semantics tail := (.done result, PUnit.unit)
  change RootFire p input (cut.attach semantics pre mark) after at step
  rcases cut.split_step semantics input PUnit.unit step with ⟨fires, _⟩ | ⟨_, fires⟩
  · rw [cut.observe_attach] at fires
    exact finished_no_step semantics _ _ _ preDone fires
  · rw [cut.observe_attach, cut.rest_attach] at fires
    exact committed_theta semantics (thetaBody p) entryWires _ input
      (cut.tokens semantics PUnit.unit pre) result fires

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs
