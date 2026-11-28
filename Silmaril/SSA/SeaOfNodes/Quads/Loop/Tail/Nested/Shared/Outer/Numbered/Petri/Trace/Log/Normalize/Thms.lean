module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Correctness

/-! Separate normalization for complete logs that may enter θ early. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model) (roots : List (RootMark p))

local notation "start" => pending semantics (emitted p)

/-- Normalization preserves the exact final marking and thus its result readback. -/
theorem normalize_final :
    (normalize p roots).getLastD start = roots.getLastD start :=
  Normalize.Proofs.final_eq p roots

/-- No θ marking changes are lost or reordered. This retains all typed
activation banks, child states, including γ choices, and feedback and exit. -/
theorem normalize_theta :
    thetaChanges p (normalize p roots) = thetaChanges p roots :=
  Normalize.Proofs.theta_eq p roots

/-- Adjacent legality starts at the original pending marking. Completion
is read from the original last marking. No entry-phase or segmentation
premise is required for the supplied log. -/
theorem normalize_scan (legal : List.IsChain (RootFire p input) (start :: roots))
    (done : (finished semantics (emitted p) input PUnit.unit (roots.getLastD start)).isSome) :
    (scan p input (normalize p roots)).isSome :=
  (scan_isSome_iff p input _).mpr (Normalize.Proofs.legal_complete p input roots legal done)

/-- The unchanged scanner refuses a log whose θ entry precedes complete
preheader publication. -/
theorem scan_rejects_early {before after : RootMark p}
    (earlier later : List (RootMark p)) (atStep : start :: roots = earlier ++ before :: after :: later)
    (wasPending : thetaPending p before = true) (entered : thetaPending p after = false)
    (incomplete : finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after) = none) :
    (scan p input roots).isSome = false :=
  Normalize.Proofs.scan_rejects_early p input roots earlier later atStep wasPending entered incomplete

/-- Acceptance includes legality and completion of the original unmodified
log, even when it entered θ early. -/
theorem scanNormalized_isSome_iff : (scanNormalized p input roots).isSome ↔ FireComplete p input roots :=
  Normalize.Proofs.scan_normalized_iff p input roots

/-- The scanner's returned tuple is the exact output of the original log. -/
theorem normalized_returned (checked : Complete p input (normalize p roots)) :
    finished semantics (emitted p) input PUnit.unit (roots.getLastD start) = some (checked.result p input) :=
  (congrArg (finished semantics (emitted p) input PUnit.unit) (normalize_final p roots)).symm.trans
    (checked.returned p input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
