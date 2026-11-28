module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs

/-! # Reachable product cutoff for complete ordered exit packets -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (Typed)
open ScheduleSearch (StateInventory)
open Syntax (Payload)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty} {results : Nat}

/-- Count the reachable typed pairs at the two supplied caller packets. -/
def Endpoint.reachableCutoff (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) : Nat :=
  (g.control.productVisits h.control a b replies left right).length

/-- Run the existing deterministic interpreter check at the reachable cutoff.
Both original typed readbacks must match. -/
def Endpoint.checkReachable? (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A))
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  let n := g.reachableCutoff h a b replies left right
  g.checkAllInterpreters? h raw raw' codec a b replies left right ⟨List.finRange n, List.mem_finRange⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
