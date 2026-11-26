module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Correspondence

/-! # Correspondence of one guarded step with the native feedback evaluator -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits resultBehaviour)

universe u x

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {states : Nat} {σ : Type x}

theorem Head.mem_request_successors (replies : ReplyEnumeration S) (f : Φ)
    (arg : Syntax.Payload (instrSrc f))
    (next : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Packet R)
    (config : Packet R) :
    config ∈ (Head.request f arg next).successors replies ↔ ∃ i a, next i a = config := by
  simp only [Head.successors, List.mem_map, replies.complete, true_and, Sigma.exists]

theorem Table.head_checked [DecidableEq Φ] {g : Table S R}
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
    {caller : Syntax.Payload (R.get g.entry)} {config : Packet R} {h : Head S R}
    (found : g.head? raw caller config = some h) : raw = g.native ∧ h = g.head caller config := by
  unfold Table.head? at found
  split at found
  · exact ⟨g.checked_reemission ‹g.checkNative raw = true›, (Option.some.inj found).symm⟩
  · cases found

/-- The computed row is the complete local native observation, before
following an internal edge or applying a selected exit continuation. -/
theorem Table.feedback_step (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (config : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint config s) = ((g.head caller config).execute prim s).routed :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.raw_step
    g caller prim config s

/-- The only internal feedback edge is the computed successful reply, with
the routed typed payload and the primitive's final machine state. -/
theorem Table.feedback_step_iff (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (config : Packet R) (s : σ)
    (q : Feedback.Point R.length Unit (σ)) :
    Feedback.Step (g.feedback caller prim) (blockPoint config s) q ↔
      ∃ (next : Packet R) (t : σ),
        (g.head caller config).execute prim s = .repeat next t ∧ q = blockPoint next t :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.step_iff
    g caller prim config s q

/-- The one-step observation equation is independent of the state carrier.
A terminal primitive divergence is already an ordinary singleton. -/
theorem Table.observe_state_step (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (config : Packet R) (s : σ) :
    g.observeAt caller prim config s =
      match (g.head caller config).execute prim s with
      | .exit i selected t => if selected then ⊤ else WithTop.some {Outcome.ret i .unit t}
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observe_state_step
    g caller prim config s

/-- The installed closure follows the one computed edge. At an outward
exit it applies literal UB exactly when that position is selected. -/
theorem Table.observe_step (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.Primitives Φ states) (config : Packet R) (s : Fin states) :
    g.observeAt caller prim config s =
      match (g.head caller config).execute prim s with
      | .exit i selected t => resultBehaviour (if selected then .ub else .ret i t)
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => resultBehaviour (.fault t)
      | .diverge => resultBehaviour .diverge :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observe_step
    g caller prim config s

/-- A complete classification of native closure determines the decorated
observation by applying the selected exit at the terminal store. -/
theorem Table.observe_of_closed (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.Primitives Φ states) (config : Packet R) (s : Fin states) (outcome : Result 2 states)
    (closed : Feedback.close (g.feedback caller prim) (blockPoint config s) = resultBehaviour outcome) :
    g.observeAt caller prim config s = resultBehaviour (g.markExit outcome) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observe_of_closed
    g caller prim config s outcome closed

/-- Exact re-emission connects the typed starting configuration to the
original decorated native CFG. The entry is the typed caller-forwarding jump. -/
theorem Table.observe_entry [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (checked : g.checkNative raw = true) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s =
      g.observeAt caller prim ⟨g.entry, caller⟩ s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observe_entry
    g raw checked caller prim s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
