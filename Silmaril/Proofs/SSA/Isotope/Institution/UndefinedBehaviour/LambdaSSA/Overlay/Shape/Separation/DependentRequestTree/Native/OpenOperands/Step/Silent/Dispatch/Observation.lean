module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Scan
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Steps
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Mathlib.Logic.Function.Iterate

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration Head StateTransition blockPoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Syntax (Payload StatePrimitives model)
open Relation (ReflTransGen TransGen)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v}

/-- Native singleton internal branches also carry the exact post-request store. -/
private abbrev Branch (f : Feedback.Run R Exits Unit σ) (p q : Feedback.Point R.length Unit σ) : Prop :=
  ∃ i a s, q = .block i a s ∧ f p = WithTop.some {Outcome.ret (Feedback.internal R Exits i) a s}

private noncomputable def continuation (f : Feedback.Run R Exits Unit σ) :
    StateTransition R σ → Behaviour Exits.length Unit σ
  | .exit i _ t => WithTop.some {Outcome.ret i .unit t}
  | .repeat q t => Feedback.close f (blockPoint q t)
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

private theorem close_step {f : Feedback.Run R Exits Unit σ} {p : Feedback.Point R.length Unit σ}
    {step : StateTransition R σ} (run : f p = step.routed) :
    Feedback.close f p = continuation f step := by
  cases step with
  | exit i marked t => exact close_terminal (R := R) (L := Exits) (o := .ret i .unit t) run
  | «repeat» q t => exact close_branch (i := q.1) run
  | fault t => exact close_terminal (R := R) (L := Exits) (o := .fault t) run
  | diverge => exact close_terminal (R := R) (L := Exits) (o := .diverge) run

theorem normalized_step (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.normalizedFeedback configs caller prim (blockPoint p s) =
      ((g.head configs caller p).execute prim s).routed := by
  obtain ⟨i, a⟩ := p
  unfold Table.normalizedFeedback blockPoint
  exact dite_eq_left a.property

private theorem original_close_step (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      continuation (g.feedback caller prim) ((g.head configs caller p).execute prim s) := by
  cases found : g.scan caller configs.configs.length p with
  | none =>
    rw [Table.head, found]
    exact exhausts_close g configs caller prim p s found
  | some head =>
    obtain ⟨q, reaches, ready⟩ := scan_ready g caller _ p found
    rw [Table.head, found, close_silent g caller prim s reaches]
    exact close_step ((feedback_step g caller prim q s).trans (by rw [ready]; rfl))

private theorem original_progress (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p q : Packet R) (s t : σ)
    (next : (g.head configs caller p).execute prim s = .repeat q t) :
    TransGen (Branch (g.feedback caller prim)) (blockPoint p s) (blockPoint q t) := by
  unfold Table.head at next
  cases found : g.scan caller configs.configs.length p with
  | none => simp [found, Head.execute] at next
  | some head =>
    have run : head.execute prim s = .repeat q t := by simpa only [found, Option.getD_some] using next
    obtain ⟨ready, reaches, exposes⟩ := scan_ready g caller _ p found
    have prefixPath : ReflTransGen (Branch (g.feedback caller prim)) (blockPoint p s) (blockPoint ready s) := by
      clear exposes
      induction reaches with
      | refl => exact .refl
      | tail _ edge ih =>
        exact ih.tail ⟨_, _, s, rfl, (feedback_step g caller prim _ s).trans (by rw [edge]; rfl)⟩
    exact TransGen.tail' prefixPath ⟨q.1, q.2.val, t, rfl,
      (feedback_step g caller prim ready s).trans (by simp only [exposes]; rw [run]; rfl)⟩

theorem close_normalized (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.normalizedFeedback configs caller prim) (blockPoint p s) := by
  classical
  let execute (x : Packet R × σ) := (g.head configs caller x.1).execute prim x.2
  let advance (x : Packet R × σ) := match execute x with
    | .repeat q t => (q, t)
    | _ => x
  let path (n : Nat) := (advance^[n]) (p, s)
  let point (n : Nat) := blockPoint (path n).1 (path n).2
  let repeats (n : Nat) := ∃ q t, execute (path n) = .repeat q t
  have step (n : Nat) (continues : repeats n) :
      execute (path n) = .repeat (path (n + 1)).1 (path (n + 1)).2 := by
    obtain ⟨q, t, run⟩ := continues
    have arrives : path (n + 1) = (q, t) := by
      change (advance^[n + 1]) (p, s) = _
      rw [Function.iterate_succ_apply']
      dsimp only [advance]
      rw [run]
    rw [arrives]
    exact run
  let f := g.feedback caller prim
  let h := g.normalizedFeedback configs caller prim
  have source (n : Nat) : Feedback.close f (point n) = continuation f (execute (path n)) :=
    original_close_step g configs caller prim _ _
  have target (n : Nat) : Feedback.close h (point n) = continuation h (execute (path n)) :=
    close_step (normalized_step g configs caller prim _ _)
  change Feedback.close f (point 0) = Feedback.close h (point 0)
  by_cases stops : ∃ n, ¬ repeats n
  · let stop := Nat.find stops
    have prior (n : Nat) (before : n < stop) : repeats n := by
      by_contra failed
      exact (Nat.not_le_of_lt before) (Nat.find_min' stops failed)
    have prefixPath (n : Nat) (within : n ≤ stop) :
        Feedback.close f (point 0) = Feedback.close f (point n) ∧
          Feedback.close h (point 0) = Feedback.close h (point n) := by
      induction n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n ih =>
        obtain ⟨left, right⟩ := ih (Nat.le_of_succ_le within)
        have next := step n (prior n (Nat.lt_of_succ_le within))
        rw [source n, next] at left
        rw [target n, next] at right
        exact ⟨left, right⟩
    obtain ⟨left, right⟩ := prefixPath stop le_rfl
    rw [left, right, source stop, target stop]
    have done : ¬ repeats stop := Nat.find_spec stops
    cases last : execute (path stop) with
    | exit | fault | diverge => rfl
    | «repeat» q t => exact (done ⟨q, t, last⟩).elim
  · have runs (n : Nat) : repeats n := by
      by_contra failed
      exact stops ⟨n, failed⟩
    have allSegments (n : Nat) : TransGen (Branch f) (point n) (point (n + 1)) :=
      original_progress g configs caller prim _ _ _ _ (step n (runs n))
    obtain ⟨expanded, first, edges⟩ := Feedback.transitive_segments_path point allSegments
    have diverges : Feedback.close f (point 0) = WithTop.some {Outcome.diverge} :=
      (congrArg (Feedback.close f) first.symm).trans (close_infinite_of_singleton expanded edges)
    refine diverges.trans ?_
    symm
    exact close_infinite_of_singleton point (fun n =>
      ⟨(path (n + 1)).1.1, (path (n + 1)).1.2.val, (path (n + 1)).2, rfl,
        (normalized_step g configs caller prim _ _).trans (congrArg StateTransition.routed (step n (runs n)))⟩)

theorem observe_step (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.observeAt configs caller prim p s =
      match (g.head configs caller p).execute prim s with
      | .exit i _ t => if g.selected i then ⊤ else WithTop.some {Outcome.ret i .unit t}
      | .repeat q t => g.observeAt configs caller prim q t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  unfold Table.observeAt
  rw [close_step (normalized_step g configs caller prim p s)]
  cases (g.head configs caller p).execute prim s with
  | exit i marked t =>
    dsimp only [continuation]
    exact (Syntax.singleton_return_bind i .unit t _).trans
      (CFG.Dependent.Native.denote_exitContinuation (Γ := [R.get g.entry]) (L := Exits)
        (model prim (g.visible.bindings caller)).raw g.selected i .unit t)
  | «repeat» => rfl
  | fault =>
    simp [continuation, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]
  | diverge => exact Syntax.diverge_bind _

theorem observe_entry [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (configs : ConfigurationEnumeration R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      g.observeAt configs caller prim ⟨g.entry, caller⟩ s := by
  have same : raw = g.native := Subtype.ext (CFG.Dependent.Native.sameRegion_eq checked)
  subst raw
  change (denote (.native g.native) (model prim (g.visible.bindings caller)).raw s).bind _ = _
  rw [native_close g caller prim s, close_normalized g configs caller prim]
  rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
