module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Steps
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Scan
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Observation

/-! # Native adequacy of packet-indexed silent exposure -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives model)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v}

/-- A silent hop selects one typed packet, transfers at the unchanged
store, and issues no primitive request. -/
theorem Table.feedback_step (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint p s) =
      match g.step caller p with
      | .inl q => (StateTransition.repeat q s).routed
      | .inr head => (head.execute prim s).routed :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.feedback_step
    g caller prim p s

/-- A successful bounded scan reaches the exposed head by typed silent hops. -/
theorem Table.scan_ready (g : Table S R) (caller : Payload (R.get g.entry)) (fuel : Nat)
    (p : Packet R) {head : Head S R} (resolved : g.scan caller fuel p = some head) :
    ∃ q, Relation.ReflTransGen (fun a b => g.step caller a = .inl b) p q ∧ g.step caller q = .inr head :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.scan_ready
    g caller fuel p resolved

/-- Exhaustion at an exhaustive inventory bound yields a genuine infinite
silent path and a repeated full configuration within that bound. -/
theorem Table.exhausted_replay (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (p : Packet R)
    (exhausted : g.scan caller configs.configs.length p = none) :
    ∃ path : Nat → Packet R, path 0 = p ∧
      (∀ n, g.step caller (path n) = .inl (path (n + 1))) ∧
      ∃ i j : Nat, i < j ∧ j ≤ configs.configs.length ∧ path i = path j :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.exhausted_replay
    g configs caller p exhausted

/-- The native evaluator sees exactly ordinary divergence for a certified
silent cycle, independently of the primitive interpreter. -/
theorem Table.exhausts_close (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ)
    (exhausted : g.scan caller configs.configs.length p = none) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.exhausts_close
    g configs caller prim p s exhausted

/-- The computed head supplies the exact local step of normalized feedback. -/
theorem Table.normalized_step (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.normalizedFeedback configs caller prim (blockPoint p s) =
      ((g.head configs caller p).execute prim s).routed :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.normalized_step
    g configs caller prim p s

/-- Closing the computed heads preserves complete feedback observations,
including infinite replays of productive requests. -/
theorem Table.close_normalized (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.normalizedFeedback configs caller prim) (blockPoint p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.close_normalized
    g configs caller prim p s

/-- The exact normalized head supplies one step of the decorated observation.
Successful requests resume with their reply payload and final machine state. -/
theorem Table.observe_step (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.observeAt configs caller prim p s =
      match (g.head configs caller p).execute prim s with
      | .exit i _ t => if g.selected i then ⊤ else WithTop.some {Outcome.ret i .unit t}
      | .repeat q t => g.observeAt configs caller prim q t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.observe_step
    g configs caller prim p s

/-- Exact readback transfers the computed heads' closed observations to
the original typed packed CFG and its selected ordered exit continuations. -/
theorem Table.observe_entry [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (configs : ConfigurationEnumeration R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      g.observeAt configs caller prim ⟨g.entry, caller⟩ s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.observe_entry
    g raw checked configs caller prim s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
