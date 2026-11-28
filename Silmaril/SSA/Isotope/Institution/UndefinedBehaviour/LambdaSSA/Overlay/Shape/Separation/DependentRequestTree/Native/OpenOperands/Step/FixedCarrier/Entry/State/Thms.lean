module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Rejection

/-! # Monotone rejection under finite carrier embeddings -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {n m : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry)}
  {decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry)}
  {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory n} {w : EntryCounterexample Φ A n}

/-- A concrete refutation stays directed at the original endpoints, with
the same caller and the image of its starting state. -/
theorem EntryCounterexample.mapState_refutes (e : Fin n ↪ Fin m)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory n)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
          (Syntax.model w.interpreter (g.bindings (decodeLeft w.input))) w.initial ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model w.interpreter (h.bindings (decodeRight w.input))) w.initial) :
    let mapped := w.mapState e
    ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model mapped.interpreter (g.bindings (decodeLeft mapped.input))) mapped.initial ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model mapped.interpreter (h.bindings (decodeRight mapped.input))) mapped.initial :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.State.mapState_refutes
    e hg hh left right stores failed

variable {callers : CallerEnumeration A} {replies : ReplyEnumeration S}

/-- Rejection persists under a state embedding. The transported witness
keeps its caller, while the larger search may find a different witness first. -/
theorem Table.compareEntries_rejection_mono (e : Fin n ↪ Fin m)
    (largerLeft : ConfigurationEnumeration R) (largerRight : ConfigurationEnumeration T) (larger : StateInventory m)
    (found : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
      some (.counterexample w)) :
    (¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model (w.mapState e).interpreter (g.bindings (decodeLeft w.input))) (e w.initial) ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model (w.mapState e).interpreter (h.bindings (decodeRight w.input))) (e w.initial)) ∧
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies largerLeft largerRight larger =
        some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.State.rejection_mono
    e largerLeft largerRight larger found

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
