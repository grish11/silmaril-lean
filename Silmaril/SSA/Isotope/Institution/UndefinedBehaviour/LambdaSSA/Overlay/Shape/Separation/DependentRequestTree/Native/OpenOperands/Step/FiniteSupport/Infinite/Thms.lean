module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Replay
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Treatment
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Refutation

/-! # Observation compression when one guarded replay is infinite -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)
open TwoRequest (Exits)
open ScheduleSearch (StateInventory)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v} {τ : Type w}
  {g : Table S R} {h : Table S T} {prim : StatePrimitives Φ σ} {s : σ}
  {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)} {p : Packet R} {q : Packet T}
  {rows : List (RunRow Φ σ)} {stop : RunStop σ}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}

theorem GuardedReplay.of_infinite (infinite : Feedback.Infinite (g.feedback a prim) (blockPoint p s)) :
    Nonempty (GuardedReplay g a prim p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.of_infinite
    infinite

theorem GuardedReplay.is_infinite (run : GuardedReplay g a prim p s) :
    Feedback.Infinite (g.feedback a prim) (blockPoint p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.is_infinite
    run

/-- In the retained branch the coded runner has an actual infinite path. -/
theorem GuardedReplay.mapped_is_infinite (run : GuardedReplay g a prim p s) (code : σ → τ)
    (other : StatePrimitives Φ τ) (steps : ∀ j, run.mappedStep code other j) :
    Feedback.Infinite (g.feedback a other) (blockPoint p (code s)) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.is_infinite
    (Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.mapped
      run code other steps)

/-- At the first missing key the coded runner ends in primitive divergence
and admits no infinite replay from that start. -/
theorem GuardedReplay.no_infinite_after_cut (run : GuardedReplay g a prim p s) (code : σ → τ)
    (other : StatePrimitives Φ τ) (cut : Nat) (steps : ∀ j < cut, run.mappedStep code other j)
    (terminal : (g.head a (run.point cut).1).execute other (code (run.point cut).2) = .diverge) :
    ¬ Feedback.Infinite (g.feedback a other) (blockPoint p (code s)) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.no_infinite_after_cut
    run code other cut steps terminal

theorem Table.observe_infinite (infinite : Feedback.Infinite (g.feedback a prim) (blockPoint p s)) :
    g.observeAt a prim p s = WithTop.some {Outcome.diverge} := by
  obtain ⟨run⟩ := GuardedReplay.of_infinite infinite
  exact Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.observes run

/-- Two infinite guarded runs have equal original decorated observations. -/
theorem Table.both_infinite_observations [DecidableEq Φ] (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (lower : Feedback.Infinite (g.feedback a prim) (blockPoint ⟨g.entry, a⟩ s))
    (upper : Feedback.Infinite (h.feedback b prim) (blockPoint ⟨h.entry, b⟩ s)) :
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s =
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s := by
  rw [g.observe_entry raw hg, h.observe_entry raw' hh, Table.observe_infinite lower, Table.observe_infinite upper]

/-- Ordinary divergence is below itself and fresh top. In the reverse
direction only ordinary divergence refines ordinary divergence. -/
theorem RunStop.divergence_order (stop : RunStop σ) :
    ((RunStop.diverge : RunStop σ).behaviour ≤ stop.behaviour ↔
      stop = .diverge ∨ ∃ i t, stop = .exit i true t) ∧
    (stop.behaviour ≤ (RunStop.diverge : RunStop σ).behaviour ↔ stop = .diverge) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.divergence_order
    stop

variable [DecidableEq σ]

/-- A finite-run script truncates an infinite run at the first unlisted
key, or stays inside the script indefinitely. Its support size is bounded
by one plus the number of recorded finite queries. -/
theorem GuardedReplay.treatment [DecidableEq Φ] (run : GuardedReplay g a prim p s)
    (finite : FiniteRun h b prim q s rows stop) (input : Payload A) :
    let support := RunSupport.ofRows s rows
    run.Treatment rows support (support.witness input rows).interpreter :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.treatment
    finite run input

theorem GuardedReplay.Treatment.observes {run : GuardedReplay g a prim p s} {support : RunSupport σ s}
    {other : Syntax.Primitives Φ support.values.length} (treated : run.Treatment rows support other) :
    g.observeAt a other p (support.code s) = WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.treated_observation
    run support other treated

variable [DecidableEq Φ]
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {input : Payload A}

/-- With either endpoint infinite, the finite endpoint's script
preserves both original observations and yields a rejecting carrier. -/
theorem Table.compress_mixed_refutation (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
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
        some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite.compress_mixed_refutation
    hg hh mixed failed callers replies left right

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
