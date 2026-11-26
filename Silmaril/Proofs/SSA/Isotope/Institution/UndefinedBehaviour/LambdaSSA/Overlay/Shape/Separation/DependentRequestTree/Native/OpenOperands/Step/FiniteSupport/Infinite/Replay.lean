module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent (Packet)
open Syntax (Payload StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v} {τ : Type w}
  {g : Table S R} {caller : Payload (R.get g.entry)} {prim : StatePrimitives Φ σ} {p : Packet R} {s : σ}

private theorem typed_point_inj {a b : Packet R × σ} (same : blockPoint a.1 a.2 = blockPoint b.1 b.2) :
    a = b := by
  obtain ⟨label, payload, store⟩ := Feedback.Point.block.inj same
  exact Prod.ext (CFG.Dependent.Packet.raw_injective (Prod.ext label payload)) store

theorem of_infinite (infinite : Feedback.Infinite (g.feedback caller prim) (blockPoint p s)) :
    Nonempty (GuardedReplay g caller prim p s) := by
  obtain ⟨path, start, steps⟩ := infinite
  have typed (n : Nat) : ∃ q t, path n = blockPoint (R := R) q t := by
    induction n with
    | zero => exact ⟨p, s, start⟩
    | succ n ih =>
      obtain ⟨q, t, atBlock⟩ := ih
      have hop := steps n
      rw [atBlock] at hop
      obtain ⟨next, final, _, atNext⟩ := (g.feedback_step_iff caller prim q t _).mp hop
      exact ⟨next, final, atNext⟩
  choose cfg store atPoint using typed
  refine ⟨⟨fun i => (cfg i, store i), typed_point_inj ((atPoint 0).symm.trans start), ?_⟩⟩
  intro i
  have hop := steps i
  rw [atPoint i] at hop
  obtain ⟨next, t, run, arrived⟩ := (g.feedback_step_iff caller prim (cfg i) (store i) _).mp hop
  have same : (cfg (i + 1), store (i + 1)) = (next, t) :=
    typed_point_inj ((atPoint (i + 1)).symm.trans arrived)
  exact run.trans (congrArg (fun point : Packet R × σ => StateTransition.repeat point.1 point.2) same.symm)

theorem is_infinite (run : GuardedReplay g caller prim p s) :
    Feedback.Infinite (g.feedback caller prim) (blockPoint p s) := by
  refine ⟨fun i => blockPoint (run.point i).1 (run.point i).2, ?_, fun i => ?_⟩
  · exact congrArg (fun point : Packet R × σ => blockPoint point.1 point.2) run.start
  · exact (g.feedback_step_iff caller prim _ _ _).mpr
      ⟨(run.point (i + 1)).1, (run.point (i + 1)).2, run.step i, rfl⟩

theorem observes (run : GuardedReplay g caller prim p s) :
    g.observeAt caller prim p s = WithTop.some {Outcome.diverge} := by
  let path (i : Nat) := blockPoint (run.point i).1 (run.point i).2
  have singleton (i : Nat) : ∃ j a t, path (i + 1) = .block j a t ∧
      g.feedback caller prim (path i) = WithTop.some {Outcome.ret (Feedback.internal R Exits j) a t} := by
    refine ⟨_, _, _, rfl, ?_⟩
    change g.feedback caller prim (blockPoint (run.point i).1 (run.point i).2) = _
    rw [g.feedback_step, run.step i]
    rfl
  have closed := close_infinite_of_singleton path singleton
  have start : path 0 = blockPoint p s :=
    congrArg (fun point : Packet R × σ => blockPoint point.1 point.2) run.start
  rw [Table.observeAt, ← start, closed]
  simp [Behaviour.bind, Behaviour.possible, WithTop.untopD_coe]
  ext o
  cases o <;> simp [Outcome.bind]

theorem request_view (run : GuardedReplay g caller prim p s) (i : Nat) :
    ∃ f arg next value, g.head caller (run.point i).1 = .request f arg next ∧
      prim f arg (run.point i).2 = .ret value (run.point (i + 1)).2 ∧
      replyDestination f next value = (run.point (i + 1)).1 := by
  have step := run.step i
  cases head : g.head caller (run.point i).1 with
  | exit =>
    rw [head, Head.execute] at step
    cases step
  | request f arg next =>
    rw [head, Head.execute] at step
    cases answer : prim f arg (run.point i).2 with
    | ret value t =>
      rw [answer] at step
      obtain ⟨dest, final⟩ := StateTransition.repeat.inj step
      exact ⟨f, arg, next, value, rfl, answer.trans (congrArg (Syntax.StateReply.ret value) final), dest⟩
    | fault | diverge =>
      rw [answer] at step
      cases step

def mapped (run : GuardedReplay g caller prim p s) (code : σ → τ) (other : StatePrimitives Φ τ)
    (steps : ∀ i, run.mappedStep code other i) :
    GuardedReplay g caller other p (code s) where
  point i := ((run.point i).1, code (run.point i).2)
  start := congrArg (fun point : Packet R × σ => (point.1, code point.2)) run.start
  step := steps

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite
