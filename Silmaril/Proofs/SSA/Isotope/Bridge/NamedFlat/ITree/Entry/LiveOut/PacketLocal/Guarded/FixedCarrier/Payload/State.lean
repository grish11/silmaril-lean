module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.State.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Transport.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.State

open Silmaril.Isotope
open Silmaril.Elgot.ITree (out_ret out_vis diverge)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Feedback (Graph)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (withExitUB denote_exitContinuation)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits)

attribute [local instance] Recognize.requestTypes

universe v

variable {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} {σ : Type v}

private def liftOut : Outcome (Exits A).length Unit σ → Outcome 2 (RunTree Φ) σ
  | .ret i a s => .ret i (Recognize.encodeValue (fun _ => diverge) a) s
  | .fault s => .fault s
  | .diverge => .diverge

theorem observe_roots_on (g : Endpoint (Recognize.signature Φ) R A)
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (tree : Packet R → RunTree Φ) (roots : RootAgrees g caller tree) (decode : ExitDecoder)
    (decodes : ∀ p : Packet (Exits A), decode (packedReturn p) = some (p.1, p.2.val))
    (p : Packet R) (s : σ) :
    decorateOn prim g.control.selected (observeOn prim (tree p) s decode) A =
      g.observeAt caller prim p s := by
  let run := g.transition caller prim
  let start := (p, s)
  let native (x : Packet R × σ) : Fin R.length × Value Unit × σ := (x.1.1, x.1.2.val, x.2)
  let named (x : Packet R × σ) : Fin Loop.length × Value (RunTree Φ) × σ := (0, .atom (tree x.1), x.2)
  have nativeRows (x : Packet R × σ) :
      g.feedback caller prim (.block (native x).1 (native x).2.1 (native x).2.2) =
        match run x with
        | .inl y => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) (native y).1) (native y).2.1 (native y).2.2}
        | .inr o => WithTop.some {Feedback.external R (Exits A) o} := by
    change g.feedback caller prim (blockPoint x.1 x.2) = _
    rw [g.feedback_step]
    unfold run Endpoint.transition
    cases (g.control.head caller x.1).execute prim x.2 <;> rfl
  have namedRows (x : Packet R × σ) :
      feedbackOn prim decode (.block (named x).1 (named x).2.1 (named x).2.2) =
        match run x with
        | .inl y => WithTop.some {Outcome.ret (Feedback.internal Loop LambdaSSA.UB.Overlay.Shape.TwoRequest.Exits (named y).1) (named y).2.1 (named y).2.2}
        | .inr o => WithTop.some {Feedback.external Loop LambdaSSA.UB.Overlay.Shape.TwoRequest.Exits (liftOut (A := A) o)} := by
    change treeStepOn prim (tree x.1) x.2 decode = _
    rw [roots x.1]
    unfold run Endpoint.transition
    cases g.control.head caller x.1 with
    | exit i selected =>
      simp only [Head.execute, treeStepOn, out_ret, Part.some_dom, ↓reduceDIte, Part.get_some,
        decodes, terminalOn, liftOut]
      rfl
    | diverge => simp [Head.execute, treeStepOn, terminalOn, liftOut]
    | request f arg next =>
      simp only [Head.execute, treeStepOn, out_vis, Part.some_dom, ↓reduceDIte, Part.get_some]
      cases prim f arg x.2 <;> rfl
  have nativeClose := (Graph.transitions_run (R := R) (L := Exits A) run Outcome.diverge native id (g.feedback caller prim) rfl (by intro x; cases h : run x <;>
      simpa only [h] using! (nativeRows x))).close_eq start
  have namedClose := (Graph.transitions_run (R := Loop) (L := LambdaSSA.UB.Overlay.Shape.TwoRequest.Exits)
    run Outcome.diverge named (liftOut (A := A) (Φ := Φ))
    (feedbackOn prim decode) rfl (by intro x; cases h : run x <;>
      simpa only [h] using! (namedRows x))).close_eq start
  change Feedback.close (g.feedback caller prim) (blockPoint p s) =
    ((Graph.transitions run Outcome.diverge).close start).map (Set.image id) at nativeClose
  change Feedback.close (feedbackOn prim decode) (.block 0 (.atom (tree p)) s) =
    ((Graph.transitions run Outcome.diverge).close start).map (Set.image (liftOut (A := A))) at namedClose
  have roundtrip (o : Outcome (Exits A).length Unit σ) :
      projectOn (liftOut (A := A) (Φ := Φ) o) = o := by
    cases o with
    | ret i a s => exact congrArg (fun value => Outcome.ret i value s) (lower_lift (Φ := Φ) a)
    | fault | diverge => rfl
  have same : observeOn prim (tree p) s decode = Feedback.close (g.feedback caller prim) (blockPoint p s) := by
    rw [observeOn, namedClose, nativeClose, WithTop.map_map]
    congr 1
    funext set
    rw [Function.comp_apply, Set.image_image]
    exact congrArg (fun f => f '' set) (funext roundtrip)
  rw [same]
  simp only [decorateOn, Endpoint.observeAt, denote_exitContinuation]
  rfl

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.State
