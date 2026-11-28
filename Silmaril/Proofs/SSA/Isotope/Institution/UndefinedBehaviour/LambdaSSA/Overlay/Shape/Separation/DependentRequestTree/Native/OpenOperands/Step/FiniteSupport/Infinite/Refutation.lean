module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Replay
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Treatment

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open ScheduleSearch (StateInventory)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v}
  {g : Table S R} {h : Table S T} {prim : StatePrimitives Φ σ} {s : σ}
  {rows : List (RunRow Φ σ)} {stop : RunStop σ}

theorem divergence_order (stop : RunStop σ) :
    ((RunStop.diverge : RunStop σ).behaviour ≤ stop.behaviour ↔
      stop = .diverge ∨ ∃ i t, stop = .exit i true t) ∧
    (stop.behaviour ≤ (RunStop.diverge : RunStop σ).behaviour ↔ stop = .diverge) := by
  cases stop with
  | exit i selected t => cases selected <;> simp [RunStop.behaviour, WithTop.coe_le_coe]
  | fault | diverge => simp [RunStop.behaviour, WithTop.coe_le_coe]

variable [DecidableEq Φ] [DecidableEq σ]
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {input : Payload A}

private theorem infinite_image (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (input : Payload A)
    (endless : Feedback.Infinite (g.feedback a prim) (blockPoint ⟨g.entry, a⟩ s))
    (finite : FiniteRun h b prim ⟨h.entry, b⟩ s rows stop) :
    let support := RunSupport.ofRows s rows
    let w := support.witness input rows
    (g.observeAt a w.interpreter ⟨g.entry, a⟩ w.initial).mapState support.embed =
      g.observeAt a prim ⟨g.entry, a⟩ s := by
  obtain ⟨run⟩ := of_infinite endless
  let support := RunSupport.ofRows s rows
  let w := support.witness input rows
  have treated := treatment finite run input
  change (g.observeAt a w.interpreter ⟨g.entry, a⟩ (support.code s)).mapState support.embed = _
  rw [treated_observation run support w.interpreter treated, observes run]
  simp [Behaviour.mapState, Outcome.mapState]

theorem compress_mixed_refutation (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (mixed :
      (Feedback.Infinite (g.feedback (decodeLeft input) prim) (blockPoint ⟨g.entry, decodeLeft input⟩ s) ∧
        FiniteRun h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ s rows stop) ∨
      (FiniteRun g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ s rows stop ∧
        Feedback.Infinite (h.feedback (decodeRight input) prim) (blockPoint ⟨h.entry, decodeRight input⟩ s)))
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let support := RunSupport.ofRows s rows
    let w := support.witness input rows
    support.values.length ≤ 1 + rows.length ∧
    ((Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s) ∧
    ((Shape.denote (withExitUB raw' h.selected)
        (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) ∧
    (¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial) ∧
    ∀ stores : StateInventory support.values.length,
      g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
        some (.counterexample witness) := by
  let support := RunSupport.ofRows s rows
  let w := support.witness input rows
  have observe₀ : (Shape.denote (withExitUB raw g.selected)
      (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial).mapState support.embed =
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s := by
    rw [g.observe_entry raw hg, g.observe_entry raw hg]
    rcases mixed with ⟨infinite, finite⟩ | ⟨finite, _⟩
    · exact infinite_image (decodeLeft input) (decodeRight input) input infinite finite
    · exact (finite.reconstructs input).1
  have observe₁ : (Shape.denote (withExitUB raw' h.selected)
      (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial).mapState support.embed =
    Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s := by
    rw [h.observe_entry raw' hh, h.observe_entry raw' hh]
    rcases mixed with ⟨_, finite⟩ | ⟨finite, infinite⟩
    · exact (finite.reconstructs input).1
    · exact infinite_image (decodeRight input) (decodeLeft input) input infinite finite
  have refutes : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial :=
    fun ordered => failed (Eq.mp (congrArg₂ (· ≤ ·) observe₀ observe₁)
      ((Behaviour.mapState_le_iff support.embed _ _).mpr ordered))
  exact ⟨RunSupport.ofRows_bound s rows, observe₀, observe₁, refutes,
    Table.checkers_reject_of_counterexample hg hh w refutes callers replies left right⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite
