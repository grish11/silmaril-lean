module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs
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

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {states larger : Nat}

private theorem get_encode (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) : (configs.invocations stores).get (encode configs stores p) = p :=
  List.getElem_idxOf _

private def carrier (e : Fin states ↪ Fin larger) (configs : ConfigurationEnumeration R)
    (stores : StateInventory states) :
    PositionalCarrier R Shape.TwoRequest.Exits Unit (Fin larger) (configs.invocations stores).length 2 states where
  invocation code :=
    let input := (configs.invocations stores).get code
    (input.1.1, input.1.2.val, e input.2)
  result := ⟨fun i => (i, .unit), fun _ _ eq => congrArg Prod.fst eq⟩
  final := e

private theorem execute_mapState (e : Fin states → Fin larger)
    (prim : Syntax.Primitives Φ states) (other : Syntax.Primitives Φ larger)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e)
    (head : Head S R) (s : Fin states) :
    head.execute other (e s) = (head.execute prim s).mapState e := by
  cases head with
  | exit | diverge => rfl
  | request f a next =>
    simp only [Head.execute, agree]
    cases prim f a s <;> rfl

theorem classify_mapState (e : Fin states ↪ Fin larger)
    (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (prim : Syntax.Primitives Φ states) (other : Syntax.Primitives Φ larger)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    g.observeAt caller other p (e s) =
      Shape.TwoRequest.resultBehaviour ((g.runFinite caller prim configs stores p s).mapState e) := by
  let D := carrier e configs stores
  let output := execute (rows g caller prim configs stores) (encode configs stores (p, s))
  have agrees (code : Fin (configs.invocations stores).length) :
      g.feedback caller other (invocationPoint D.invocation code) =
        (rows g caller prim configs stores code).routed D := by
    change g.feedback caller other
      (blockPoint ((configs.invocations stores).get code).1 (e ((configs.invocations stores).get code).2)) = _
    rw [g.feedback_step, execute_mapState _ prim other agree, rows]
    dsimp only
    cases (g.head caller ((configs.invocations stores).get code).1).execute prim
      ((configs.invocations stores).get code).2 with
    | «repeat» next t =>
      change (Transition.repeat next (e t)).routed =
        (Transition.repeat ((configs.invocations stores).get (encode configs stores (next, t))).1
          (e ((configs.invocations stores).get (encode configs stores (next, t))).2)).routed
      rw [get_encode]
    | exit | fault | diverge => rfl
  have closed := classify_routed D (rows g caller prim configs stores) (encode configs stores (p, s)) agrees
  have atStart : invocationPoint D.invocation (encode configs stores (p, s)) = blockPoint p (e s) := by
    change blockPoint ((configs.invocations stores).get (encode configs stores (p, s))).1
      (e ((configs.invocations stores).get (encode configs stores (p, s))).2) = blockPoint p (e s)
    rw [get_encode]
  rw [atStart] at closed
  have decoded : output.routed D = Shape.TwoRequest.resultBehaviour (output.mapState e) := by
    cases output <;> rfl
  refine (g.observe_of_closed caller other p (e s) (output.mapState e) (closed.trans decoded)).trans ?_
  change Shape.TwoRequest.resultBehaviour (g.markExit (output.mapState e)) =
    Shape.TwoRequest.resultBehaviour ((g.markExit output).mapState e)
  congr 1
  cases output with
  | ret i t => cases sel : g.selected i <;> simp [Table.markExit, Result.mapState, sel]
  | fault | diverge | ub => rfl

theorem classify (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    g.observeAt caller prim p s = Shape.TwoRequest.resultBehaviour (g.runFinite caller prim configs stores p s) := by
  have agrees (f : Φ) (a : Syntax.Payload (instrSrc f)) (s : Fin states) :
      prim f a s = (prim f a s).mapState id := by cases prim f a s <;> rfl
  have observed := classify_mapState (Function.Embedding.refl (Fin states)) g caller prim prim agrees configs stores p s
  have same : (g.runFinite caller prim configs stores p s).mapState id = g.runFinite caller prim configs stores p s := by
    cases g.runFinite caller prim configs stores p s <;> rfl
  exact observed.trans (congrArg Shape.TwoRequest.resultBehaviour same)

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
    rw [head_execute_congr g caller configs stores agree cfg.1 cfg.2]
  simp only [Table.runFinite, sameRows]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier
