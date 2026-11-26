module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Classification

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {σ : Type v} {τ : Type w} {g : Table S R} {h : Table S T}

private theorem execute_mapped (f : σ → τ) (prim : StatePrimitives Φ σ) (other : StatePrimitives Φ τ)
    (agree : ∀ op arg s, other op arg (f s) = (prim op arg s).mapState f) (head : Head S R) (s : σ) :
    head.execute other (f s) = (head.execute prim s).mapState f := by
  cases head with
  | exit => rfl
  | request op arg next =>
    simp only [Head.execute, agree]
    cases prim op arg s <;> rfl

private theorem observe_mapped (g : Table S R) (a : Payload (R.get g.entry))
    (f : σ → τ) (prim : StatePrimitives Φ σ) (other : StatePrimitives Φ τ)
    (agree : ∀ op arg s, other op arg (f s) = (prim op arg s).mapState f) (p : Packet R) (s : σ) :
    g.observeAt a other p (f s) = (g.observeAt a prim p s).mapState f := by
  rcases finite_or_infinite g a prim p s with ⟨rows, stop, finite⟩ | infinite
  · rw [finite.replay f other (fun row mem => (agree _ _ _).trans
      (congrArg (Syntax.StateReply.mapState f) (finite.records row mem))), finite.observes]
    cases stop with
    | exit i selected t =>
      cases selected <;> simp [RunStop.behaviour, RunStop.mapState, Behaviour.mapState, Outcome.mapState]
    | fault | diverge => simp [RunStop.behaviour, RunStop.mapState, Behaviour.mapState, Outcome.mapState]
  · obtain ⟨path⟩ := GuardedReplay.of_infinite infinite
    have steps (j : Nat) : path.mappedStep f other j := by
      unfold GuardedReplay.mappedStep
      rw [execute_mapped f prim other agree, path.step j]
      rfl
    rw [Table.observe_infinite (path.mapped_is_infinite f other steps), Table.observe_infinite infinite]
    simp [Behaviour.mapState, Outcome.mapState]

def liftPrimitives (prim : StatePrimitives Φ σ) : StatePrimitives Φ (ULift.{w} σ) :=
  fun op arg t => (prim op arg t.down).mapState ULift.up

theorem ulift_order_iff [DecidableEq Φ]
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
    {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (prim : StatePrimitives Φ σ) (s : σ) :
    let lifted : StatePrimitives Φ (ULift.{w} σ) := liftPrimitives prim
    Shape.denote (withExitUB raw g.selected) (Syntax.model lifted (g.bindings a)) (ULift.up s) ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model lifted (h.bindings b)) (ULift.up s) ↔
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s := by
  let e : σ ↪ ULift.{w} σ := ⟨ULift.up, fun _ _ eq => congrArg ULift.down eq⟩
  let lifted : StatePrimitives Φ (ULift.{w} σ) := liftPrimitives prim
  have agree (op : Φ) (arg : Payload (instrSrc op)) (t : σ) : lifted op arg (e t) = (prim op arg t).mapState e :=
    rfl
  change Shape.denote (withExitUB raw g.selected) (Syntax.model lifted (g.bindings a)) (e s) ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model lifted (h.bindings b)) (e s) ↔ _
  rw [g.observe_entry raw hg, h.observe_entry raw' hh, g.observe_entry raw hg, h.observe_entry raw' hh,
    observe_mapped g a e prim lifted agree, observe_mapped h b e prim lifted agree, Behaviour.mapState_le_iff]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model
