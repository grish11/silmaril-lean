module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Waiting
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Continuation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending complete_reached)
open Shared.MLIR.CF.InnerPhi (headerBank side occurrence)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (old : Bank (regs := regs) model)

private theorem continue_activation (arm : Fin 2)
    (chosen : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm)
    (child : Marking semantics (Prefix.outerArm p.toRoutes arm))
    (childSteps : ReflTransGen
      (Fire semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old) PUnit.unit)
      (pending semantics (Prefix.outerArm p.toRoutes arm)) child)
    (inner : (readInner p old arm child).map (fun bank =>
      (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old), bank)) = (packetsAt p old).inner) :
    let next := nextBank p model old
    Nonempty (Activation p old (packetsAt p old) (next.get p.again).down next) := by
  let next := nextBank p model old
  let output := RVSDG.Theta.bodyResult semantics (next.get p.again).down next
  let cut := (outerCut p).2.2
  let rest := pending semantics (outerCut p).2.1
  obtain ⟨header, start⟩ := waiting_reaches_with p old .ret arm chosen child childSteps
  have reachedInner := cut.prefix_reaches semantics old PUnit.unit start
  have outerExec : (outerRegion p).Returns semantics old (packetsAt p old).outer.2 := by
    apply (Term.returns_toGraph (outerRegion p) semantics old _).mp
    refine ⟨0, ?_⟩
    exact outer_run p model 0 old
  obtain ⟨outerMark, joined, readOuter⟩ :=
    complete_reached semantics (outerRegion p) old _ start outerExec
  have reachesOuter := cut.prefix_reaches semantics old PUnit.unit (start.trans joined)
  have bodyExec : (thetaBody p).Returns semantics old output := by
    apply (Term.returns_toGraph (thetaBody p) semantics old output).mp
    refine ⟨0, ?_⟩
    exact activation_run p model 0 old
  obtain ⟨final, continues, complete⟩ :=
    complete_reached semantics (thetaBody p) old output reachesOuter bodyExec
  refine ⟨⟨header, arm, child, cut.attach semantics outerMark rest, final,
    chosen, reachedInner, inner, cut.prefix_between semantics old PUnit.unit joined rest, ?_, continues, complete⟩⟩
  change (finished semantics (outerRegion p) old PUnit.unit
    (cut.observe semantics (cut.attach semantics outerMark rest))).map _ = _
  rw [cut.observe_attach, readOuter]
  rfl

theorem activation :
    let next := nextBank p model old
    Nonempty (Activation p old (packetsAt p old) (next.get p.again).down next) := by
  by_cases entered : ((headerBank p.toRoutes old).get p.outerTest).down = true
  · have chosen : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = 0 := by
      simp [Prefix.outerChoice, Join.Choice.eval, entered]
    obtain ⟨child, steps, read⟩ := inner_reaches p old
    apply continue_activation p old 0 chosen child steps
    change (finished semantics (innerPrefix p) (headerBank p.toRoutes old) PUnit.unit
      ((innerCut p).2.2.observe semantics child)).map _ = _
    rw [read]
    simp only [packetsAt, entered, ite_true, Option.map_some]
  · have chosen : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = 1 := by
      simp [Prefix.outerChoice, Join.Choice.eval, entered]
    apply continue_activation p old 1 chosen (pending semantics _) .refl
    change none = (packetsAt p old).inner
    simp [packetsAt, entered]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs
