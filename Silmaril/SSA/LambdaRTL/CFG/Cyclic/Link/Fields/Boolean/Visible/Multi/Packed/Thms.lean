module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Packed.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Program

open Silmaril.Elgot.ITree (TraceLE TraceLEWithSilence ExchangePath SilentAfter silentAfter_bind_pure_iff)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril (HasTy TypeFormers)
open Silmaril.Isotope (BoundCtx)

variable {F : Type} {a b n : Nat} (program : Program F a b n)

/-- Successful named elaboration and typing identify the same weak tree at
the existing packed dispatcher, given a record agreeing with the named
packet store. Only the public return encoding changes. -/
theorem packed_observe {τ : Type*} [TypeFormers τ] [HasTy F τ] {capturesCount : Nat}
    {β : BoundCtx τ capturesCount} (input : Fin a) (packet : Packet n) (captures : Fin capturesCount → Register n)
    {R : Fin (program.compile input).blocks.length → τ} {L : Fin program.exits.length → τ}
    {target : FiniteCFG F (program.compile input).blocks.length program.exits.length capturesCount}
    (accepted : elaborate (program.compile input) program.exits captures = some target)
    (typed : target.HasType β R L) (ambient original : Env Atom)
    (inputs : ∀ i, original i.val = store packet (captures i)) :
    region Visible.Program.primitive (extend ambient (Capture.packEnv capturesCount original))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) := by
  rw [Capture.packed_context_tree,
    ← run_tree Visible.Program.primitive _ _ captures accepted (store packet) original inputs]
  rfl

theorem refinementAt?_iff_packedOutput [DecidableEq F] (right : Program F a b n)
    (input : Fin a) (packet : Packet n) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result))
        (right.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.refinementAt?_iff right input packet).trans
    (TraceLE.bind_pure_iff Visible.Program.packedTreeOutput_injective).symm

theorem silentAfter?_iff_packedOutput [DecidableEq F] (input : Fin a) (packet : Packet n)
    (path : ExchangePath (Event (F × Bool))) :
    program.silentAfter? input packet path = true ↔
      SilentAfter (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) path :=
  (program.silentAfter?_iff input packet path).trans (silentAfter_bind_pure_iff _ _ _).symm

theorem refinementAtWithSilence?_iff_packedOutput [DecidableEq F] (right : Program F a b n)
    (input : Fin a) (packet : Packet n) :
    program.refinementAtWithSilence? right input packet = true ↔
      TraceLEWithSilence (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result))
        (right.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.refinementAtWithSilence?_iff right input packet).trans
    (TraceLEWithSilence.bind_pure_iff Visible.Program.packedTreeOutput_injective).symm

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Program
