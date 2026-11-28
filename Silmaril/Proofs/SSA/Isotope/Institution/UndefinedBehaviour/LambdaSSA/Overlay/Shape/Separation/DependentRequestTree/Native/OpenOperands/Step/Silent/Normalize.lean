module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Steps
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Cycle
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Row Table
open OpenOperands (Head StateTransition blockPoint FiniteRun RunStop RunRow replyDestination GuardedReplay)
open OpenOperands.Silent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB exitContinuation)
open Syntax (Payload StatePrimitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Relation (ReflTransGen TransGen)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v}

private noncomputable def closeResult (f : Feedback.Run R Exits Unit σ) : StateTransition R σ → Behaviour Exits.length Unit σ
  | .exit i _ t => WithTop.some {Outcome.ret i .unit t}
  | .repeat next t => Feedback.close f (blockPoint next t)
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

private theorem close_segment {f : Feedback.Run R Exits Unit σ} {p q : Feedback.Point R.length Unit σ}
    (path : ReflTransGen (Branch f) p q) {step : StateTransition R σ} (run : f q = step.routed) :
    Feedback.close f p = closeResult f step := by
  rw [close_along path]
  cases step with
  | exit i marked s => exact close_terminal (R := R) (L := Exits) (o := .ret i .unit s) run
  | «repeat» next s => exact close_branch (i := next.1) run
  | fault t => exact close_terminal (o := .fault t) run
  | diverge => exact close_terminal (o := .diverge) run

private theorem finite_closes (g : Table S R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    {p : Packet R} {s : σ} {rows : List (RunRow Φ σ)} {stop : RunStop σ}
    (finite : FiniteRun g.normalize caller prim p s rows stop) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.normalize.feedback caller prim) (blockPoint p s) := by
  have original (p : Packet R) (s : σ) :
      Feedback.close (g.feedback caller prim) (blockPoint p s) =
        closeResult (g.feedback caller prim) ((g.normalize.head caller p).execute prim s) := by
    cases found : g.resolve R.length p.1 with
    | none =>
      rw [normalize_head g caller, found]
      exact exhausts_close g caller prim p s found
    | some row =>
      obtain ⟨q, path, run⟩ := normalized_segment g caller prim p s (by simp [found])
      exact close_segment path run
  have normal (p : Packet R) (s : σ) :
      Feedback.close (g.normalize.feedback caller prim) (blockPoint p s) =
        closeResult (g.normalize.feedback caller prim) ((g.normalize.head caller p).execute prim s) :=
    close_segment .refl (g.normalize.feedback_step caller prim p s)
  induction finite with
  | exit head | silent head => rw [original, normal, head]; rfl
  | «repeat» head answer _ ih =>
    rw [original, normal, head, Head.execute, answer]
    exact ih
  | fault head answer => rw [original, normal, head, Head.execute, answer]; rfl
  | diverge head answer => rw [original, normal, head, Head.execute, answer]; rfl

private theorem infinite_closes (g : Table S R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    {p : Packet R} {s : σ} (run : GuardedReplay g.normalize caller prim p s) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.normalize.feedback caller prim) (blockPoint p s) := by
  let starts := fun n => blockPoint (run.point n).1 (run.point n).2
  have first : starts 0 = blockPoint p s := congrArg (fun x => blockPoint x.1 x.2) run.start
  have original (n : Nat) : TransGen (Branch (g.feedback caller prim)) (starts n) (starts (n + 1)) := by
    have resolves : g.resolve R.length (run.point n).1.1 ≠ none := by
      intro noneFound
      have step := run.step n
      rw [normalize_head g caller, noneFound] at step
      cases step
    obtain ⟨q, path, step⟩ := normalized_segment g caller prim (run.point n).1 (run.point n).2 resolves
    rw [run.step n] at step
    exact TransGen.tail' path ⟨(run.point (n + 1)).1.1, (run.point (n + 1)).1.2.val, _, rfl, step⟩
  have normal (n : Nat) : TransGen (Branch (g.normalize.feedback caller prim)) (starts n) (starts (n + 1)) := by
    have step := g.normalize.feedback_step caller prim (run.point n).1 (run.point n).2
    rw [run.step n] at step
    exact .single ⟨(run.point (n + 1)).1.1, (run.point (n + 1)).1.2.val, _, rfl, step⟩
  rw [← first, close_along_infinite starts original, close_along_infinite starts normal]

theorem close_normalized (g : Table S R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.normalize.feedback caller prim) (blockPoint p s) := by
  rcases g.normalize.finite_or_infinite caller prim p s with ⟨_, _, finite⟩ | infinite
  · exact finite_closes g caller prim finite
  · obtain ⟨replay⟩ := GuardedReplay.of_infinite infinite
    exact infinite_closes g caller prim replay

theorem normalize_observes [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      Shape.denote (withExitUB g.normalize.native g.selected) (model prim (g.visible.bindings caller)) s := by
  have same : raw = g.native := Subtype.ext (CFG.Dependent.Native.sameRegion_eq checked)
  subst raw
  let M := (model prim (g.visible.bindings caller)).raw
  change (denote (.native g.native) M s).bind _ =
    (denote (.native g.normalize.native) M s).bind _
  rw [native_close g caller prim s]
  have target := native_close (Table.ofGuarded g.normalize) caller prim s
  change denote (.native g.normalize.native) M s =
    Feedback.close (g.normalize.feedback caller prim) (blockPoint ⟨g.entry, caller⟩ s) at target
  rw [target, close_normalized g caller prim]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
