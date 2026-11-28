module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Replay
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Observations
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms

/-! Soundness of scanning a complete log of the checked shared-outer loop. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending Finishes finishes_term_iff)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)
variable {roots : List (RootMark p)}

/-- Every adjacent pair of the original supplied log fires legally, from
the original pending marking. The scanner does not insert firings. -/
theorem Complete.legal (checked : Complete p input roots) :
    List.IsChain (RootFire p input) (pending semantics (emitted p) :: roots) :=
  Proofs.complete_legal p input checked

theorem Complete.returned (checked : Complete p input roots) :
    finished semantics (emitted p) input PUnit.unit (roots.getLastD (pending semantics (emitted p))) =
      some (checked.result p input) :=
  Proofs.complete_result p input checked

theorem Complete.finishes (checked : Complete p input roots) :
    Finishes semantics (lower p) input (checked.result p input) :=
  (finishes_term_iff semantics (emitted p) input _).mpr
    ⟨_, Proofs.reaches _ _ (checked.legal p input), checked.returned p input⟩

variable {pre : PreMark p} {old : Bank (regs := regs) model}

/-- Reuse the recorded cut inversion to identify the first bank read
from the actual recovered activation. -/
theorem Slice.firstOuter_eq (s : Slice p input pre old (pending semantics (thetaBody p)) roots) :
    s.firstOuter = some (packetsAt p old).outer.2 :=
  Proofs.firstOuter_eq p input s

theorem Slice.packet_eq (s : Slice p input pre old (pending semantics (thetaBody p)) roots) :
    let next := nextBank p model old
    s.packet = RVSDG.Theta.bodyResult semantics (next.get p.again).down next :=
  Proofs.packet_eq p input s

theorem Slice.boundary (s : Slice p input pre old (pending semantics (thetaBody p)) roots)
    (preDone : (finished semantics (preheader p) input PUnit.unit pre).isSome) :
    let next := nextBank p model old
    s.after = afterLatch p pre (next.get p.again).down next :=
  Proofs.boundary p input s preDone

/-- Every recovered activation compares its selected positional CF/Φ
row and exact latch successor to the observed typed packets. -/
theorem Complete.observations_agree (checked : Complete p input roots)
    (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p) :
    ∀ seen ∈ checked.observations p input, seen.Agrees p input inner outer :=
  Proofs.recovered_agrees p input inner outer checked.recovery

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
