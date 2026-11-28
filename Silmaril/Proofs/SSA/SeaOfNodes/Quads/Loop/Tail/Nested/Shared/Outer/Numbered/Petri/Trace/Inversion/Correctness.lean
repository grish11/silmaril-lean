module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Inversion.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending finished_no_step finishes_term_iff finishes_iff)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)
open Shared.MLIR.CF.InnerPhi (headerBank side)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (old : Bank (regs := regs) model)

theorem outer_eq {mark : Marking semantics (thetaBody p)} {bank : Bank (regs := regs) model}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) mark)
    (observed : readOuter p old mark = some bank) :
    bank = (packetsAt p old).outer.2 := by
  let cut := (outerCut p).2.2
  have frontSteps := cut.observe_reaches semantics old PUnit.unit steps
  rw [cut.observe_pending] at frontSteps
  have finishes := (finishes_term_iff semantics (outerRegion p) old bank).mpr ⟨_, frontSteps, observed⟩
  obtain ⟨bound, ran⟩ := (finishes_iff semantics (outerRegion p).toGraph old bank).mp finishes
  exact Option.some.inj (ran.symm.trans (outer_run p model bound old))

theorem stable_outer {join final : Marking semantics (thetaBody p)} {bank : Bank (regs := regs) model}
    (observed : readOuter p old join = some bank)
    (later : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) join final) :
    (outerCut p).2.2.observe semantics join = (outerCut p).2.2.observe semantics final := by
  have frontSteps := (outerCut p).2.2.observe_reaches semantics old PUnit.unit later
  generalize same : (outerCut p).2.2.observe semantics final = marking at frontSteps ⊢
  clear same later final
  induction frontSteps with
  | refl => rfl
  | tail _ fire same =>
    rw [← same] at fire
    exact False.elim (finished_no_step semantics (outerRegion p) old PUnit.unit observed fire)

theorem body_eq {mark : Marking semantics (thetaBody p)}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) mark)
    (done : (finished semantics (thetaBody p) old PUnit.unit mark).isSome) :
    let next := nextBank p model old
    readOuter p old mark = some (packetsAt p old).outer.2 ∧
      finished semantics (thetaBody p) old PUnit.unit mark =
        some (RVSDG.Theta.bodyResult semantics (next.get p.again).down next) := by
  obtain ⟨packet, ready⟩ := Option.isSome_iff_exists.mp done
  obtain ⟨bank, bankRead⟩ := (outerCut p).2.2.completed_prefix semantics old mark ready
  have finishes := (finishes_term_iff semantics (thetaBody p) old packet).mpr ⟨mark, steps, ready⟩
  obtain ⟨bound, ran⟩ := (finishes_iff semantics (thetaBody p).toGraph old packet).mp finishes
  exact ⟨bankRead.trans (congrArg some (outer_eq p old steps bankRead)),
    ready.trans (ran.symm.trans (activation_run p model bound old))⟩

theorem completed_child_packet (arm : Fin 2)
    (selected : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm)
    {mark : Marking semantics (Prefix.outerArm p.toRoutes arm)}
    (steps : ReflTransGen (Fire semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old) PUnit.unit)
      (pending semantics (Prefix.outerArm p.toRoutes arm)) mark)
    (done : (finished semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old)
      PUnit.unit mark).isSome) :
    (readInner p old arm mark).map (fun bank =>
      (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old), bank)) = (packetsAt p old).inner := by
  by_cases entered : ((headerBank p.toRoutes old).get p.outerTest).down = true
  · have yes : arm = 0 := selected.symm.trans (by simp [Prefix.outerChoice, Join.Choice.eval, entered])
    clear selected
    subst arm
    obtain ⟨packet, ready⟩ := Option.isSome_iff_exists.mp done
    let cut := (innerCut p).2.2
    obtain ⟨bank, reads⟩ := cut.completed_prefix semantics _ _ ready
    have frontSteps := cut.observe_reaches semantics (headerBank p.toRoutes old) PUnit.unit steps
    change ReflTransGen (Fire semantics (innerPrefix p) (headerBank p.toRoutes old) PUnit.unit)
      (cut.observe semantics (pending semantics (Prefix.innerRegion p.toRoutes))) (cut.observe semantics mark) at frontSteps
    rw [cut.observe_pending] at frontSteps
    have finishes := (finishes_term_iff semantics (innerPrefix p) (headerBank p.toRoutes old) bank).mpr ⟨_, frontSteps, reads⟩
    obtain ⟨fuel, ran⟩ := (finishes_iff semantics (innerPrefix p).toGraph (headerBank p.toRoutes old) bank).mp finishes
    have exactBank := Option.some.inj (ran.symm.trans
      (Shared.MLIR.CF.InnerPhi.gamma_run p.toRoutes old fuel))
    change (finished semantics (innerPrefix p) (headerBank p.toRoutes old) PUnit.unit
      (cut.observe semantics mark)).map _ = _
    rw [reads, exactBank]
    simp only [packetsAt, entered, ite_true, Option.map_some]
  · have no : arm = 1 := selected.symm.trans (by simp [Prefix.outerChoice, Join.Choice.eval, entered])
    clear selected
    subst arm
    change none = (packetsAt p old).inner
    simp [packetsAt, entered]

theorem latch_step (input : Bank (regs := regs) model)
    {preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry)))}
    (preDone : (finished semantics (.ofBase (entryCode (src := src) (entry := entry)))
      input PUnit.unit preheader).isSome)
    {body : Marking semantics (thetaBody p)} {after : Marking semantics (emitted p)}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) body)
    (done : (finished semantics (thetaBody p) old PUnit.unit body).isSome)
    (step : Fire semantics (emitted p) input PUnit.unit (atBody p preheader old body) after) :
    let next := nextBank p model old
    after = afterLatch p preheader (next.get p.again).down next := by
  let cut := entryCut p
  let tail := iterateThenReturnWith (thetaBody p) p.result (endWires (entryCode (src := src) (entry := entry)))
  let before : Marking semantics tail := (.waiting (0 : Fin 1) (old, body), PUnit.unit)
  change Fire semantics (emitted p) input PUnit.unit (cut.attach semantics preheader before) after at step
  have observed := cut.observe_attach semantics preheader before
  have rest := cut.rest_attach semantics preheader before
  rcases cut.split_step semantics input PUnit.unit step with ⟨frontSteps, _⟩ | ⟨same, firing⟩
  · rw [observed] at frontSteps
    obtain ⟨_, completed⟩ := Option.isSome_iff_exists.mp preDone
    exact False.elim (finished_no_step semantics _ _ _ completed frontSteps)
  · rw [observed] at same firing
    rw [rest] at firing
    rw [← cut.attach_observe_rest semantics after, ← same]
    let next := nextBank p model old
    have ready := (body_eq p old steps done).2
    change finished semantics (thetaBody p) old PUnit.unit body =
      some (RVSDG.Theta.bodyResult semantics (next.get p.again).down next) at ready
    have vertex := RVSDG.NestedTheta.Petri.consume_theta semantics (thetaBody p)
      (endWires (entryCode (src := src) (entry := entry))) _ input (cut.tokens semantics PUnit.unit preheader)
      old body (next.get p.again).down next ready firing
    change cut.attach semantics preheader (cut.rest semantics after) =
      afterLatch p preheader (next.get p.again).down next
    cases tag : (next.get p.again).down with
    | false =>
      change cut.attach semantics preheader (cut.rest semantics after) =
        cut.attach semantics preheader (.done next, PUnit.unit)
      refine congrArg (cut.attach semantics preheader) (Prod.ext ?_ (Subsingleton.elim (α := PUnit) _ _))
      simpa only [tag, Bool.false_eq_true, ite_false] using vertex
    | true =>
      change cut.attach semantics preheader (cut.rest semantics after) =
        cut.attach semantics preheader (.waiting (0 : Fin 1) (next, pending semantics (thetaBody p)), PUnit.unit)
      refine congrArg (cut.attach semantics preheader) (Prod.ext ?_ (Subsingleton.elim (α := PUnit) _ _))
      simpa only [tag, ite_true] using vertex

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Inversion.Proofs
