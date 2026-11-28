module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Defs

/-! # A cutoff from the reachable synchronized product -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open ScheduleSearch (StateInventory)
open Syntax (Payload)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty}

/-- Maximize the distinct reachable-pair count over the exhaustive shared
caller domain. Each count includes the entry and the final test pair. -/
def Table.reachableCutoff (g : Table S R) (h : Table S T) (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) : Nat :=
  ((callers.packets.map fun input =>
    (g.productVisits h (decodeLeft input) (decodeRight input) replies left right).length).max?).getD 0

/-- Compare on the computed carrier, keeping the original exact readback gate. -/
def Table.checkReachableEntries? (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  let n := g.reachableCutoff h callers decodeLeft decodeRight replies left right
  g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right ⟨List.finRange n, List.mem_finRange⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
