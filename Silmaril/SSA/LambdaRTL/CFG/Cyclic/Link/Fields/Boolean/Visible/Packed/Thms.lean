module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Packed

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program

open Silmaril.Elgot.ITree (TraceLE TraceLEWithSilence ExchangePath SilentAfter silentAfter_bind_pure_iff)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril (HasTy TypeFormers)
open Silmaril.Isotope (BoundCtx)

theorem packedTreeOutput_injective {α : Type*} : Function.Injective (FiniteCFG.packedTreeOutput (α := α)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.packedTreeOutput_injective

variable {F : Type} {a b : Nat} (program : Program F a b)

/-- An admitted, typed elaboration of this named entry runs on the same
supplied record in the existing packed dispatcher. The only change is the
outward encoding of the terminating transfer. -/
theorem packed_observe {τ : Type*} [TypeFormers τ] [HasTy F τ] {n : Nat}
    {β : BoundCtx τ n} (input : Fin a) (flag : Bool) (captures : Fin n → Register)
    {R : Fin (program.compile input).blocks.length → τ} {L : Fin program.exits.length → τ}
    {target : FiniteCFG F (program.compile input).blocks.length program.exits.length n}
    (accepted : elaborate (program.compile input) program.exits captures = some target)
    (typed : target.HasType β R L) (ambient original : Env Atom)
    (inputs : ∀ i, original i.val = store flag (captures i)) :
    region primitive (extend ambient (Capture.packEnv n original))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (program.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result)) := by
  rw [Capture.packed_context_tree, ← run_tree primitive _ _ captures accepted (store flag) original inputs]
  rfl

/-- The dispatcher's outward tag is injective, so the decision applies
to the packed trees supplied by the entry equation on either side. -/
theorem refinementAt?_iff_packedOutput [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) :
    program.refinementAt? right input flag = true ↔
      TraceLE (program.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result))
        (right.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.refinementAt?_iff right input flag).trans (TraceLE.bind_pure_iff
    packedTreeOutput_injective).symm

theorem silentAfter?_iff_packedOutput [DecidableEq F] (input : Fin a) (flag : Bool)
    (path : ExchangePath (Event (F × Bool))) :
    program.silentAfter? input flag path = true ↔
      SilentAfter (program.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result)) path :=
  (program.silentAfter?_iff input flag path).trans (silentAfter_bind_pure_iff _ _ _).symm

theorem refinementAtWithSilence?_iff_packedOutput [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) :
    program.refinementAtWithSilence? right input flag = true ↔
      TraceLEWithSilence (program.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result))
        (right.observe input flag >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.refinementAtWithSilence?_iff right input flag).trans (TraceLEWithSilence.bind_pure_iff
    packedTreeOutput_injective).symm

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program
