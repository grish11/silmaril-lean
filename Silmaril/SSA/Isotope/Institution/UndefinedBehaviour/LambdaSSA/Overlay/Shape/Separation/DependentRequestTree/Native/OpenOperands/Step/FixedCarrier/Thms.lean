module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Classification
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Decision
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Restrictions

/-! # Fixed-carrier refinement of original guarded native CFGs -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open TwoRequest (Exits resultBehaviour)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}

/-- On distinct keys, the enumerator lists exactly the restrictions of
total deterministic typed interpreters over the fixed carrier. -/
theorem InterpreterScript.assignments_iff [DecidableEq Φ] (replies : ReplyEnumeration S)
    (stores : StateInventory states) {keys : List (Query Φ states)} (distinct : keys.Nodup)
    (script : List (Row Φ states)) :
    script ∈ assignments replies stores keys ↔
      ∃ prim : Syntax.Primitives Φ states, script = keys.map fun q => ⟨q, q.read prim⟩ :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.assignments_iff
    replies stores distinct script

theorem InterpreterScript.restricted [DecidableEq Φ] (replies : ReplyEnumeration S)
    (stores : StateInventory states) (keys : List (Query Φ states)) (prim : Syntax.Primitives Φ states) :
    ∃ script ∈ assignments replies stores keys,
      ∀ q ∈ keys, q.read (interpret script) = q.read prim :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.restricted
    replies stores keys prim

/-- The scan gives the full installed observation. If the finite bound is
exhausted by repeats, the actual feedback has an infinite replay. -/
theorem Table.observe_runFinite (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.Primitives Φ states) (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R) (s : Fin states) :
    g.observeAt caller prim p s = resultBehaviour (g.runFinite caller prim configs stores p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.classify
    g caller prim configs stores p s

/-- The whole decorated observation at any typed block invocation depends
only on the finite support of complete query keys. -/
theorem Table.observeAt_congr (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) {prim other : Syntax.Primitives Φ states}
    (agree : ∀ q ∈ g.queries caller configs stores, q.read prim = q.read other) (p : Packet R) (s : Fin states) :
    g.observeAt caller prim p s = g.observeAt caller other p s := by
  rw [g.observe_runFinite caller prim configs stores, g.observe_runFinite caller other configs stores,
    Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.runFinite_congr
      g caller configs stores agree]

/-- Independently run the two original typed CFGs under each common
interpreter restriction and compare the installed shaped observations. -/
theorem Table.checkAllInterpreters_iff [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) :
    g.checkAllInterpreters h caller caller' replies left right stores = true ↔
      ∀ (prim : Syntax.Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings caller')) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.checkAllInterpreters_iff
    g h raw raw' hg hh caller caller' replies left right stores

/-- The checked API accepts precisely readback-certified endpoints whose
observations are ordered for every total interpreter and initial state. -/
theorem Table.checkAllInterpreters?_accepts_iff [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) :
    g.checkAllInterpreters? h raw raw' caller caller' replies left right stores = some true ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
      ∀ (prim : Syntax.Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings caller')) s := by
  cases hg : g.checkNative raw <;> cases hh : h.checkNative raw' <;> simp [checkAllInterpreters?, hg, hh]
  exact g.checkAllInterpreters_iff h raw raw' hg hh caller caller' replies left right stores

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
