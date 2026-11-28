module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.State.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.State

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits)

attribute [local instance] Recognize.requestTypes

universe v

/-- Exact root replay preserves the payload-sensitive observation for any
store type, including primitive faults and genuine infinite transfers. -/
theorem observe_roots_on {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} {σ : Type v}
    (g : Endpoint (Recognize.signature Φ) R A)
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (tree : Packet R → RunTree Φ) (roots : RootAgrees g caller tree) (decode : ExitDecoder)
    (decodes : ∀ p : Packet (Exits A), decode (packedReturn p) = some (p.1, p.2.val))
    (p : Packet R) (s : σ) :
    decorateOn prim g.control.selected (observeOn prim (tree p) s decode) A =
      g.observeAt caller prim p s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.State.observe_roots_on
    g caller prim tree roots decode decodes p s

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
