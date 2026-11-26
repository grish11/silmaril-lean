module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Paths
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Script

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag resultBehaviour result_order)
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives model)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {states : Nat} {g : Table S R} {h : Table S T}
  {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {initial final : Fin states} {point : ProductConfig R T}
  {path : List (ProductEdge S R T)} {stores : List (Fin states)} {rows : List (InterpreterScript.Row Φ states)}

private theorem refute_native (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (scheduled : ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows)
    {prim : Primitives Φ states} (run : InterpreterScript.Realizes prim rows)
    (wrong : ¬ g.observeAt caller prim point.1 final ≤ h.observeAt caller' prim point.2 final) :
    ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) initial ≤
      Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) initial := by
  obtain ⟨left, right⟩ := scheduled_observes scheduled run
  rwa [g.observe_entry raw readback, h.observe_entry raw' readback', left, right]

theorem refutes_exits (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (scheduled : ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows)
    (consistent : InterpreterScript.Consistent rows) {i j : Tag} {marked : Bool}
    (lower : g.head caller point.1 = .exit i marked) (upper : h.head caller' point.2 = .exit j false)
    (different : marked = true ∨ i ≠ j) :
    ∃ prim : Primitives Φ states,
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) initial ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) initial := by
  obtain ⟨prim, run⟩ := (InterpreterScript.feasible_iff rows).mpr consistent
  refine ⟨prim, refute_native readback readback' scheduled run ?_⟩
  rw [g.observe_step, h.observe_step, lower, upper, Head.execute, Head.execute]
  cases marked with
  | false => simpa [result_order, Result.refines] using different
  | true => simp [result_order, Result.refines]

theorem refutes_queries (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (scheduled : ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows)
    {f k : Φ} {arg : Payload (instrSrc f)} {arg' : Payload (instrSrc k)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {next' : (i : Fin (S.replies k).length) → Payload ((S.replies k).get i) → Packet T}
    (lower : g.head caller point.1 = .request f arg next)
    (upper : h.head caller' point.2 = .request k arg' next') (faultState : Fin states)
    (consistent : InterpreterScript.Consistent
      (rows ++ [⟨⟨f, arg, final⟩, .fault faultState⟩, ⟨⟨k, arg', final⟩, .diverge⟩])) :
    ∃ prim : Primitives Φ states,
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) initial ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) initial := by
  obtain ⟨prim, run⟩ := (InterpreterScript.feasible_iff _).mpr consistent
  have fault : prim f arg final = .fault faultState := run ⟨⟨f, arg, final⟩, .fault faultState⟩ (by simp)
  have diverges : prim k arg' final = .diverge := run ⟨⟨k, arg', final⟩, .diverge⟩ (by simp)
  refine ⟨prim, refute_native readback readback' scheduled (fun row mem => run row (List.mem_append_left _ mem)) ?_⟩
  rw [g.observe_step, h.observe_step, lower, upper, Head.execute, Head.execute, fault, diverges]
  change ¬ resultBehaviour (.fault faultState) ≤ resultBehaviour .diverge
  rw [result_order]
  simp [Result.refines]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
