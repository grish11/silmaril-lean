module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs

/-! # Packet-sensitive guarded weak-tree observations -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril.Elgot.ITree (ret vis)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits)

attribute [local instance] Recognize.requestTypes

/-- Pack a native exit packet in the same representation as a named exit
with its attached selected-register record. -/
def packedReturn {A : Syntax.Ty} (p : Packet (Exits A)) : Transfer Runtime :=
  LambdaSSA.FiniteCFG.packedTreeOutput (p.1.val, Recognize.encodeValue ULift.up p.2.val)

/-- The weak-tree roots at corresponding packet invocations use the same
query, reply routing, and complete returned packet as the typed endpoint. -/
def RootAgrees {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty}
    (g : Endpoint (Recognize.signature Φ) R A) (caller : Syntax.Payload (R.get g.control.entry))
    (tree : Packet R → RunTree Φ) : Prop :=
  ∀ p, tree p =
    match g.control.head caller p with
    | .exit i _ => ret (packedReturn (g.returnPacket caller p i))
    | .diverge => Silmaril.Elgot.ITree.diverge
    | .request f arg next => vis (.call f arg) (fun reply => tree (next reply.1 reply.2))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
