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

/-- One store for the terminal test, plus the smaller available entry
rank. The checker requires at least one rank before using this bound. -/
def Table.rankedCutoff (g : Table S R) (h : Table S T) : Nat :=
  (match g.ranks.get g.entry, h.ranks.get h.entry with
  | some a, some b => min a b
  | some a, none => a
  | none, some b => b
  | none, none => 0) + 1

def Table.rankedStores (g : Table S R) (h : Table S T) : StateInventory (g.rankedCutoff h) :=
  ⟨List.finRange _, List.mem_finRange⟩

/-- Both endpoints must pass exact native readback. One reachable entry rank
suffices. The decoders may supply different native entry types and values. -/
def Table.checkRankedEntries? [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  if g.entryCheck || h.entryCheck then
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right (g.rankedStores h)
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
