module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Recorded

/-! Inversion laws for supplied firings at the shared-loop boundaries. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending)
open Shared.MLIR.CF.InnerPhi (headerBank side)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (old : Bank (regs := regs) model)
/-- The marks in the root inversion are those of the original numbered graph. -/
theorem lower_toTerm : (lower p).toTerm = emitted p :=
  RVSDG.NestedTheta.Term.toTerm_toGraph (emitted p)

/-- Any reached marking that exposes the outer cut reads the selected old
bank in full. A completed body is only needed in completed_activation. -/
theorem readOuter_eq {mark : Marking semantics (thetaBody p)} {bank : Bank (regs := regs) model}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) mark)
    (observed : readOuter p old mark = some bank) :
    bank = (packetsAt p old).outer.2 :=
  Inversion.Proofs.outer_eq p old steps observed

/-- A supplied finite activation from pending reads the exact outer Φ
bank and simultaneous latch packet as soon as its complete result exists. -/
theorem completed_activation {mark : Marking semantics (thetaBody p)}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) mark)
    (done : (finished semantics (thetaBody p) old PUnit.unit mark).isSome) :
    let next := nextBank p model old
    readOuter p old mark = some (packetsAt p old).outer.2 ∧
      finished semantics (thetaBody p) old PUnit.unit mark =
        some (RVSDG.Theta.bodyResult semantics (next.get p.again).down next) :=
  Inversion.Proofs.body_eq p old steps done

theorem readOuter_cf (input : Bank (regs := regs) model)
    (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    {mark : Marking semantics (thetaBody p)} {bank : Bank (regs := regs) model}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) mark)
    (observed : readOuter p old mark = some bank) :
    (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old), encodeValues bank) =
      (cfPacketsAt p inner outer input old).2 := by
  rw [readOuter_eq p old steps observed]
  exact congrArg Prod.snd (packetsAt_cf p input inner outer old)

/-- These adjacent markings belong to the supplied list of original
firings. The cut is unreadable earlier and stable through the completed
latch. Its first readability can depend on firing order. -/
theorem first_outer_read (rest : List (Marking semantics (thetaBody p)))
    (chain : List.IsChain (Fire semantics (thetaBody p) old PUnit.unit)
      (pending semantics (thetaBody p) :: rest))
    (done : (finished semantics (thetaBody p) old PUnit.unit
      (rest.getLastD (pending semantics (thetaBody p)))).isSome) :
    ∃ earlier before after later,
      pending semantics (thetaBody p) :: rest = earlier ++ before :: after :: later ∧
      (∀ point ∈ earlier, readOuter p old point = none) ∧ readOuter p old before = none ∧
      Fire semantics (thetaBody p) old PUnit.unit before after ∧
      readOuter p old after = some (packetsAt p old).outer.2 ∧
      (outerCut p).2.2.observe semantics after =
        (outerCut p).2.2.observe semantics (rest.getLastD (pending semantics (thetaBody p))) :=
  Inversion.Proofs.first_outer p old rest chain done

/-- Invert the retained child when the observed arm, input bank and legal
child run have been checked. The actual false arm exposes no inner packet. -/
theorem completed_child_packet (arm : Fin 2)
    (selected : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm)
    {mark : Marking semantics (Prefix.outerArm p.toRoutes arm)}
    (steps : ReflTransGen (Fire semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old) PUnit.unit)
      (pending semantics (Prefix.outerArm p.toRoutes arm)) mark)
    (done : (finished semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old)
      PUnit.unit mark).isSome) :
    (readInner p old arm mark).map (fun bank =>
      (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old), bank)) = (packetsAt p old).inner :=
  Inversion.Proofs.completed_child_packet p old arm selected steps done

/-- At a completed preheader and live completed body, invert the supplied
root firing itself. It resets the body with the exact simultaneous bank
or commits the same exit bank, according to the original latch bit. -/
theorem latch_step (input : Bank (regs := regs) model)
    {preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry)))}
    (preDone : (finished semantics (.ofBase (entryCode (src := src) (entry := entry)))
      input PUnit.unit preheader).isSome)
    {body : Marking semantics (thetaBody p)} {after : Marking semantics (emitted p)}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p)) body)
    (done : (finished semantics (thetaBody p) old PUnit.unit body).isSome)
    (step : Fire semantics (emitted p) input PUnit.unit (atBody p preheader old body) after) :
    let next := nextBank p model old
    after = afterLatch p preheader (next.get p.again).down next ∧
      MLIR.CF.latchSuccessor p input old =
        .inl (if (next.get p.again).down then Diamond.MLIR.CF.siteFrame p.header next
          else Diamond.MLIR.CF.exitFrame (next.get p.result)) :=
  ⟨Inversion.Proofs.latch_step p old input preDone steps done step,
    MLIR.CF.Comparison.latch_successor p input old⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
