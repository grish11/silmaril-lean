module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Restrictions

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier (encode rows)
open CFG.Dependent (Packet)
open ScheduleSearch (StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {states : Nat}

private theorem get_encode (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) : (configs.invocations stores).get (encode configs stores p) = p :=
  List.getElem_idxOf _

private def carrier (configs : ConfigurationEnumeration R) (stores : StateInventory states) :
    PositionalCarrier R Shape.TwoRequest.Exits Unit (Fin states) (configs.invocations stores).length 2 states where
  invocation code :=
    let input := (configs.invocations stores).get code
    (input.1.1, input.1.2.val, input.2)
  result := ⟨fun i => (i, .unit), fun _ _ eq => congrArg Prod.fst eq⟩
  final := ⟨id, fun _ _ eq => eq⟩

theorem classify (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    g.observeAt caller prim p s = Shape.TwoRequest.resultBehaviour (g.runFinite caller prim configs stores p s) := by
  let D := carrier configs stores
  let output := execute (rows g caller prim configs stores) (encode configs stores (p, s))
  apply g.observe_of_closed caller prim p s output
  have agrees (code : Fin (configs.invocations stores).length) :
      g.feedback caller prim (invocationPoint D.invocation code) =
        (rows g caller prim configs stores code).routed D := by
    change g.feedback caller prim
      (blockPoint ((configs.invocations stores).get code).1 ((configs.invocations stores).get code).2) = _
    rw [g.feedback_step, rows]
    dsimp only
    cases (g.head caller ((configs.invocations stores).get code).1).execute prim
      ((configs.invocations stores).get code).2 with
    | «repeat» next t =>
      change (Transition.repeat next t).routed =
        (Transition.repeat ((configs.invocations stores).get (encode configs stores (next, t))).1
          ((configs.invocations stores).get (encode configs stores (next, t))).2).routed
      rw [get_encode]
    | exit | fault | diverge => rfl
  have closed := classify_routed D (rows g caller prim configs stores) (encode configs stores (p, s)) agrees
  have atStart : invocationPoint D.invocation (encode configs stores (p, s)) = blockPoint p s := by
    change blockPoint ((configs.invocations stores).get (encode configs stores (p, s))).1
      ((configs.invocations stores).get (encode configs stores (p, s))).2 = blockPoint p s
    rw [get_encode]
  rw [atStart] at closed
  refine closed.trans ?_
  change output.routed D = Shape.TwoRequest.resultBehaviour output
  cases output <;> rfl

theorem runFinite_congr (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) {prim other : Syntax.Primitives Φ states}
    (agree : ∀ q ∈ g.queries caller configs stores, q.read prim = q.read other)
    (p : Packet R) (s : Fin states) :
    g.runFinite caller prim configs stores p s = g.runFinite caller other configs stores p s := by
  have sameRows : rows g caller prim configs stores = rows g caller other configs stores := by
    funext code
    unfold rows
    dsimp only
    let cfg := (configs.invocations stores).get code
    have step : (g.head caller cfg.1).execute prim cfg.2 = (g.head caller cfg.1).execute other cfg.2 := by
      cases head : g.head caller cfg.1 with
      | exit => rfl
      | request f arg next =>
        let q : InterpreterScript.Query Φ states := ⟨f, arg, cfg.2⟩
        have listed := query_mem g caller configs stores cfg.1 cfg.2 (q := q) (by rw [head]; rfl)
        have reply : prim f arg cfg.2 = other f arg cfg.2 := agree q listed
        simp only [Head.execute, reply]
    rw [step]
  simp only [Table.runFinite, sameRows]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier
