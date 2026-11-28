module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration Head HeadObserver StateTransition blockPoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent (evalHead)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Table Row
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
  (head_feedback_mapState)
open CFG.Dependent (Packet)
open Syntax (Payload StatePrimitives model)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}

private theorem head_mark (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (p : Packet R) {i : Tag} {selected : Bool}
    (head : g.head configs caller p = .exit i selected) : g.selected i = selected := by
  unfold Table.head at head
  cases found : g.scan caller configs.configs.length p with
  | none => simp [found] at head
  | some code =>
    have eq : code = .exit i selected := by simpa only [found, Option.getD_some] using head
    subst code
    obtain ⟨⟨j, packet⟩, _, step⟩ := g.scan_ready caller _ p found
    unfold Table.step at step
    cases row : g.row j with
    | jump => simp [row, Row.step] at step
    | dispatch =>
      simp only [row, Row.step] at step
      split at step <;> cases step
    | guarded rowCode =>
      cases rowCode with
      | exit tag =>
        simp only [row, Row.step, evalHead, Sum.inr.injEq, Head.exit.injEq] at step
        exact step.1 ▸ step.2
      | request | diverge => simp [row, Row.step, evalHead] at step

theorem observeAt_mapState {σ : Type v} {τ : Type w} (g : Table S R)
    (configs : ConfigurationEnumeration R) (caller : Payload (R.get g.entry))
    (e : σ ↪ τ) (prim : StatePrimitives Φ σ) (other : StatePrimitives Φ τ)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e) (p : Packet R) (s : σ) :
    g.observeAt configs caller other p (e s) = Behaviour.mapState e (g.observeAt configs caller prim p s) := by
  simp only [Table.observeAt, CFG.Dependent.Native.denote_exitContinuation]
  apply head_feedback_mapState (A := .unit) (g.head configs caller) (fun _ _ => .unit) e prim other agree
  · intro p s
    rw [g.normalized_step]
    cases (g.head configs caller p).execute prim s <;> rfl
  · intro p s
    rw [g.normalized_step]
    cases (g.head configs caller p).execute other s <;> rfl

@[expose] noncomputable def observer (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) : HeadObserver.{u,v} S R where
  head := g.head configs caller
  returnValue _ _ := .unit
  observe := fun prim => g.observeAt configs caller prim
  step := by
    intro σ prim p s
    rw [g.observe_step]
    cases head : g.head configs caller p with
    | exit i selected => simp only [Head.execute, head_mark g configs caller p head]
    | diverge => rfl
    | request f arg next =>
      simp only [Head.execute]
      cases prim f arg s <;> rfl
  infinite := by
    intro σ prim configs' store next
    let path := fun n => blockPoint (configs' n) (store n)
    have loop := close_infinite_of_singleton (f := g.normalizedFeedback configs caller prim) path
      (fun n => ⟨(configs' (n + 1)).1, (configs' (n + 1)).2.val, store (n + 1), rfl,
        (g.normalized_step configs caller prim (configs' n) (store n)).trans
          (congrArg StateTransition.routed (next n))⟩)
    rw [Table.observeAt, loop]
    exact Syntax.diverge_bind _
  mapState := fun e prim other => observeAt_mapState g configs caller e prim other

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
