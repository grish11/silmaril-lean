module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Correctness

/-! # Exact shared-entry verdicts on a fixed finite carrier -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {states : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry)}
  {decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory states}

/-- An absent verdict reports unsupported readback at an original endpoint. -/
theorem Table.compareEntries_none_iff :
    g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false := by
  cases hg : g.checkNative raw <;> cases hh : h.checkNative raw' <;> simp [compareEntries?, hg, hh]

/-- For exact-readback endpoints, acceptance is equivalent to the shaped
order at every shared caller, interpreter, and initial state of this carrier. -/
theorem Table.compareEntries_accepts_iff :
    g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some .refines ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
        ∀ (input : Syntax.Payload A) (prim : Syntax.Primitives Φ states) (s : Fin states),
          Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
            Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.accepts_iff

/-- The returned shared caller, initial state and reconstructed interpreter
refute the installed shaped order on the two original decorated CFGs. -/
theorem Table.compareEntries_counterexample {w : EntryCounterexample Φ A states}
    (found : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
      some (.counterexample w)) :
    w.input ∈ callers.packets ∧ w.initial ∈ stores.values ∧
      ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model w.interpreter (g.bindings (decodeLeft w.input))) w.initial ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model w.interpreter (h.bindings (decodeRight w.input))) w.initial :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.counterexample
    found

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
