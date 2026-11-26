module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB exitContinuation)
open ScheduleSearch (StateInventory)
open Syntax (Payload Primitives model)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {A : Syntax.Ty} {states results : Nat}

/-- The existing finite feedback traversal retains the typed exit payload at
the actual terminal packet, prior to any selection. -/
theorem Endpoint.close_classifies (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      resultBehaviour codec (execute (g.rows codec caller prim configs stores) (FixedCarrier.encode configs stores (p, s))) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.close_classifies
    g codec caller prim configs stores p s

/-- Selection inspects the original tag and replaces a selected return by
fresh top. The exact packet is retained at unselected returns. -/
theorem Endpoint.decorate_result (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states) (r : Result results states) :
    (resultBehaviour codec r).bind (fun i a s =>
      LambdaSSA.UB.Overlay.denote (exitContinuation (Γ := [R.get g.control.entry]) (L := Exits A) g.control.selected i)
        (extendModel (model prim (g.control.bindings caller)).raw a) s) =
      resultBehaviour codec (g.markExit codec r) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.decorate_result
    g codec caller prim r

/-- The observation of the exact native readback uses the original ordered
tag for selection. An unselected exit retains its payload and state. -/
theorem Endpoint.observe_entry [DecidableEq Φ] (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)) (readback : g.checkNative raw = true)
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (s : Fin states) :
    Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s =
      resultBehaviour codec (g.runFinite codec caller prim configs stores ⟨g.control.entry, caller⟩ s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.observe_entry
    g codec raw readback caller prim configs stores s

/-- The exact code identifies both the tag and the typed payload. -/
theorem result_order (codec : Fin results ≃ Packet (Exits A)) (r t : Result results states) :
    resultBehaviour codec r ≤ resultBehaviour codec t ↔ r.refines t :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.result_order
    codec r t

/-- The shared interpreter scan decides the shaped order at the original
typed native endpoints. -/
theorem Endpoint.acceptance_iff [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A)) (caller : Payload (R.get g.control.entry))
    (caller' : Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkAllInterpreters? h raw raw' codec caller caller' replies left right stores = some true ↔
      ∀ (prim : Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (model prim (h.control.bindings caller')) s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.acceptance_iff
    g h raw raw' codec caller caller' replies left right stores hg hh

/-- With both readbacks accepted, a negative verdict has a semantic
witness on the original native endpoints. -/
theorem Endpoint.rejection_iff [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A)) (caller : Payload (R.get g.control.entry))
    (caller' : Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkAllInterpreters? h raw raw' codec caller caller' replies left right stores = some false ↔
      ∃ (prim : Primitives Φ states) (s : Fin states),
        ¬ Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (model prim (h.control.bindings caller')) s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.rejection_iff
    g h raw raw' codec caller caller' replies left right stores hg hh

/-- The unit specialization re-emits the existing native guarded CFG. -/
theorem Endpoint.unit_native (g : Table S R) : (Endpoint.unit g).native = g.native :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.unit_native
    g

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
