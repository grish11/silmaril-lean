module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Defs

/-! # One finite carrier for entry-ranked guarded CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open ScheduleSearch (StateInventory)
open Syntax (Payload)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty}

/-- At most the smaller entry rank many synchronized replies can precede
a distinguishing test. One extra store holds that final test. -/
def Table.rankedCutoff (g : Table S R) (h : Table S T) : Nat :=
  min ((g.ranks.get g.entry).getD 0) ((h.ranks.get h.entry).getD 0) + 1

def Table.rankedStores (g : Table S R) (h : Table S T) : StateInventory (g.rankedCutoff h) :=
  ⟨List.finRange _, List.mem_finRange⟩

/-- Exact native readback and entry rank are both required. The two
decoders may supply different native entry types and values. -/
def Table.checkRankedEntries? [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  if g.entryCheck && h.entryCheck then
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right (g.rankedStores h)
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
