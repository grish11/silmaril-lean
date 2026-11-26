module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits resultBehaviour)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

attribute [local instance] Recognize.requestTypes

variable {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} {states results : Nat}

/-- Exact replay at each weak-tree root gives the same complete finite result
as the payload-retaining typed native classifier. -/
theorem observe_roots (g : Endpoint (Recognize.signature Φ) R A)
    (codec : Fin results ≃ Packet (Exits A)) (caller : Syntax.Payload (R.get g.control.entry))
    (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (tree : Packet R → RunTree Φ) (roots : RootAgrees g caller tree) (decode : ExitDecoder)
    (decodes : ∀ p : Packet (Exits A), decode (packedReturn p) = some (p.1, p.2.val))
    (p : Packet R) (s : Fin states) :
    decorate prim g.control.selected (FixedCarrier.observe prim (tree p) s decode) A =
      resultBehaviour codec (g.runFinite codec caller prim configs stores p s) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.observe_roots
    g codec caller prim configs stores tree roots decode decodes p s

/-- Identify the original named weak tree, after typed payload decoding and
selection at the original tag, with the admitted native interpretation. -/
theorem observe_roots_native [DecidableEq Φ] (g : Endpoint (Recognize.signature Φ) R A)
    (codec : Fin results ≃ Packet (Exits A)) (caller : Syntax.Payload (R.get g.control.entry))
    (raw : Typed Φ [R.get g.control.entry] (Exits A)) (readback : g.checkNative raw = true)
    (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (tree : Packet R → RunTree Φ) (roots : RootAgrees g caller tree) (decode : ExitDecoder)
    (decodes : ∀ p : Packet (Exits A), decode (packedReturn p) = some (p.1, p.2.val))
    (s : Fin states) :
    decorate prim g.control.selected (FixedCarrier.observe prim (tree ⟨g.control.entry, caller⟩) s decode) A =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw g.control.selected) (Syntax.model prim (g.control.bindings caller)) s :=
  (observe_roots g codec caller prim configs stores tree roots decode decodes _ s).trans
    (g.observe_entry codec raw readback caller prim configs stores s).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
